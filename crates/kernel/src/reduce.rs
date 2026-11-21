//! Fast spine-based WHNF reducer and definitional equality engine.
//! Supports beta, zeta, iota, K-like, structure projections, height-ordered delta,
//! proof irrelevance in `Prop`, and function + structure eta-conversion.

use crate::arena::{BinderInfo, ExprData, ExprId, FVarId, LevelId, Literal, NameId};
use crate::check::TypeChecker;
use crate::env::{Declaration, QuotKind};
use crate::error::KernelError;
use crate::expr::{instantiate1, instantiate_level_params, instantiate_rev};
use crate::level::{level_eq, level_is_zero};

impl<'a> TypeChecker<'a> {
    /// Reduce `e` to weak head normal form (beta + zeta + iota + projection + delta).
    pub fn whnf(&mut self, e: ExprId) -> ExprId {
        if let Some(&cached) = self.whnf_cache.get(&e) {
            return cached;
        }
        let mut cur = e;
        loop {
            cur = self.whnf_core(cur);
            if let Some(r) = self.reduce_iota_or_proj(cur).or_else(|| self.unfold_head_delta(cur)) {
                cur = r;
            } else {
                break;
            }
        }
        self.whnf_cache.insert(e, cur);
        cur
    }

    /// Spine-based WHNF without delta: beta, zeta, and local let-bound fvars.
    pub(crate) fn whnf_core(&mut self, mut e: ExprId) -> ExprId {
        let mut spine = Vec::new();
        loop {
            match self.arena.get_expr(e).clone() {
                ExprData::App(f, a) => {
                    spine.push(a);
                    e = f;
                }
                ExprData::Lam { mut body, .. } if !spine.is_empty() => {
                    let mut args = Vec::with_capacity(spine.len());
                    args.push(spine.pop().unwrap());
                    while !spine.is_empty() {
                        if let ExprData::Lam { body: next, .. } = self.arena.get_expr(body) {
                            body = *next;
                            args.push(spine.pop().unwrap());
                        } else {
                            break;
                        }
                    }
                    e = instantiate_rev(self.arena, body, &args);
                }
                ExprData::Let { val, body, .. } => e = instantiate1(self.arena, body, val),
                ExprData::FVar(fv) => match self.local_value(fv) {
                    Some(val) => e = val,
                    None => break,
                },
                _ => break,
            }
        }
        while let Some(arg) = spine.pop() {
            e = self.arena.app(e, arg);
        }
        e
    }

    pub(crate) fn app_spine(&self, mut e: ExprId) -> (ExprId, Vec<ExprId>) {
        let mut args = Vec::new();
        while let ExprData::App(f, a) = self.arena.get_expr(e) {
            args.push(*a);
            e = *f;
        }
        args.reverse();
        (e, args)
    }

    pub(crate) fn reduce_iota_or_proj(&mut self, e: ExprId) -> Option<ExprId> {
        let (head, args) = self.app_spine(e);
        match self.arena.get_expr(head).clone() {
            ExprData::Proj { struct_name, idx, expr } => {
                let ind = match self.decls.get(&struct_name)? {
                    Declaration::Inductive(i) if i.ctors.len() == 1 && i.num_indices == 0 => i,
                    _ => return None,
                };
                let val = self.whnf(expr);
                let (vhead, vargs) = self.app_spine(val);
                if let ExprData::Const(cname, _) = self.arena.get_expr(vhead) {
                    let pos = ind.num_params as usize + idx as usize;
                    if *cname == ind.ctors[0] && pos < vargs.len() {
                        return Some(self.arena.app_n(vargs[pos], &args));
                    }
                }
                None
            }
            ExprData::Const(name, lvls) => {
                // Quotient reduction: `Quot.lift α r β f h (Quot.mk α' r' a)` -> `f a`.
                if let Some(Declaration::Quot { kind: QuotKind::Lift, .. }) = self.decls.get(&name) {
                    if args.len() >= 6 {
                        let major = self.whnf(args[5]);
                        let (mhead, margs) = self.app_spine(major);
                        if let ExprData::Const(mn, _) = self.arena.get_expr(mhead) {
                            if matches!(self.decls.get(mn), Some(Declaration::Quot { kind: QuotKind::Ctor, .. }))
                                && margs.len() == 3
                            {
                                let fa = self.arena.app(args[3], margs[2]);
                                return Some(self.arena.app_n(fa, &args[6..]));
                            }
                        }
                    }
                    return None;
                }
                let rec = match self.decls.get(&name)? {
                    Declaration::Recursor(r) if lvls.len() == r.level_params.len() => r.clone(),
                    _ => return None,
                };
                let major_idx = (rec.num_params + rec.num_motives + rec.num_minors + rec.num_indices) as usize;
                if args.len() <= major_idx {
                    return None;
                }
                let mut major = self.whnf(args[major_idx]);
                // Expand Nat literals one step so `Nat.rec` computes on `#ELN` literals.
                if let ExprData::Lit(Literal::Nat(k)) = *self.arena.get_expr(major) {
                    major = self.expand_nat_lit(k);
                }
                let prefix_end = (rec.num_params + rec.num_motives + rec.num_minors) as usize;
                if rec.k && rec.rules.len() == 1 && rec.rules[0].num_fields == 0 {
                    let rule = &rec.rules[0];
                    if let Some(Declaration::Constructor(c)) = self.decls.get(&rule.ctor_name) {
                        let c = c.clone();
                        let major_ty = self.infer_type(major).ok()?;
                        let ind_lvls = &lvls[lvls.len() - c.level_params.len()..];
                        let mut ctor_ty = instantiate_level_params(self.arena, c.ty, &c.level_params, ind_lvls);
                        for &p in &args[..rec.num_params as usize] {
                            ctor_ty = self.whnf(ctor_ty);
                            let ExprData::Pi { body, .. } = self.arena.get_expr(ctor_ty) else { return None };
                            ctor_ty = instantiate1(self.arena, *body, p);
                        }
                        if self.is_def_eq(major_ty, ctor_ty).ok()? {
                            let rhs = instantiate_level_params(self.arena, rule.rhs, &rec.level_params, &lvls);
                            let out = self.arena.app_n(rhs, &args[..prefix_end]);
                            return Some(self.arena.app_n(out, &args[major_idx + 1..]));
                        }
                    }
                }
                let (mhead, margs) = self.app_spine(major);
                if let ExprData::Const(cname, _) = self.arena.get_expr(mhead) {
                    let rule = rec.rules.iter().find(|r| r.ctor_name == *cname)?;
                    if margs.len() == (rec.num_params + rule.num_fields) as usize {
                        let rhs = instantiate_level_params(self.arena, rule.rhs, &rec.level_params, &lvls);
                        let out = self.arena.app_n(rhs, &args[..prefix_end]);
                        let out = self.arena.app_n(out, &margs[rec.num_params as usize..]);
                        return Some(self.arena.app_n(out, &args[major_idx + 1..]));
                    }
                }
                None
            }
            _ => None,
        }
    }

    fn expand_nat_lit(&mut self, k: u64) -> ExprId {
        if k == 0 {
            self.arena.const_path("Nat.zero", [])
        } else {
            let succ = self.arena.const_path("Nat.succ", []);
            let pred = self.arena.lit_nat(k - 1);
            self.arena.app(succ, pred)
        }
    }

    fn delta_info(&self, head: ExprId) -> Option<(ExprId, u64, Box<[LevelId]>, Box<[NameId]>)> {
        let ExprData::Const(name, lvls) = self.arena.get_expr(head) else { return None };
        let decl = self.decls.get(name)?;
        let (val, prio) = decl.delta_value()?;
        (lvls.len() == decl.level_params().len()).then(|| (val, prio, lvls.clone(), decl.level_params().into()))
    }

    fn unfold_delta_app(&mut self, val: ExprId, params: &[NameId], lvls: &[LevelId], args: &[ExprId]) -> ExprId {
        let inst = instantiate_level_params(self.arena, val, params, lvls);
        let app = self.arena.app_n(inst, args);
        self.whnf_core(app)
    }

    fn unfold_head_delta(&mut self, e: ExprId) -> Option<ExprId> {
        let (head, args) = self.app_spine(e);
        let (val, _, lvls, params) = self.delta_info(head)?;
        let inst = instantiate_level_params(self.arena, val, &params, &lvls);
        Some(self.arena.app_n(inst, &args))
    }

    fn is_proof(&mut self, e: ExprId) -> Result<Option<ExprId>, KernelError> {
        if matches!(self.arena.get_expr(e), ExprData::Sort(_) | ExprData::Pi { .. } | ExprData::Lit(_)) {
            return Ok(None);
        }
        let ty = self.infer_type(e)?;
        let sort = self.infer_sort(ty)?;
        Ok(level_is_zero(self.arena, sort).then_some(ty))
    }

    /// Definitional equality `a ≡ b` with DAG memoization.
    pub fn is_def_eq(&mut self, a: ExprId, b: ExprId) -> Result<bool, KernelError> {
        if a == b {
            return Ok(true);
        }
        let key = if a.0 <= b.0 { (a, b) } else { (b, a) };
        if self.def_eq_cache.contains(&key) {
            return Ok(true);
        }
        let eq = self.is_def_eq_core(a, b)?;
        if eq {
            self.def_eq_cache.insert(key);
        }
        Ok(eq)
    }

    fn is_def_eq_core(&mut self, mut a: ExprId, mut b: ExprId) -> Result<bool, KernelError> {
        a = self.whnf_core(a);
        b = self.whnf_core(b);
        if a == b {
            return Ok(true);
        }
        if let (Some(ta), Some(tb)) = (self.is_proof(a)?, self.is_proof(b)?) {
            return self.is_def_eq(ta, tb);
        }

        loop {
            if a == b {
                return Ok(true);
            }
            if let Some(ra) = self.reduce_iota_or_proj(a) {
                a = self.whnf_core(ra);
                continue;
            }
            if let Some(rb) = self.reduce_iota_or_proj(b) {
                b = self.whnf_core(rb);
                continue;
            }

            match (self.arena.get_expr(a).clone(), self.arena.get_expr(b).clone()) {
                (ExprData::Sort(u), ExprData::Sort(v)) => return Ok(level_eq(self.arena, u, v)),
                (ExprData::Lit(x), ExprData::Lit(y)) => return Ok(x == y),
                (ExprData::Lit(Literal::Nat(k)), _) => {
                    a = self.expand_nat_lit(k);
                    continue;
                }
                (_, ExprData::Lit(Literal::Nat(k))) => {
                    b = self.expand_nat_lit(k);
                    continue;
                }
                (
                    ExprData::Pi { name, binder_info, ty: t1, body: b1 },
                    ExprData::Pi { ty: t2, body: b2, .. },
                )
                | (
                    ExprData::Lam { name, binder_info, ty: t1, body: b1 },
                    ExprData::Lam { ty: t2, body: b2, .. },
                ) => {
                    if !self.is_def_eq(t1, t2)? {
                        return Ok(false);
                    }
                    let fv = self.push_local(name, binder_info, t1, None);
                    let fve = self.arena.fvar(fv);
                    let (ib1, ib2) = (instantiate1(self.arena, b1, fve), instantiate1(self.arena, b2, fve));
                    let res = self.is_def_eq(ib1, ib2);
                    self.pop_local();
                    return res;
                }
                (ExprData::Lam { name, binder_info, ty, body }, _) => {
                    if self.try_fun_eta(name, binder_info, ty, body, b)? {
                        return Ok(true);
                    }
                }
                (_, ExprData::Lam { name, binder_info, ty, body }) => {
                    if self.try_fun_eta(name, binder_info, ty, body, a)? {
                        return Ok(true);
                    }
                }
                _ => {}
            }

            let (ha, args_a) = self.app_spine(a);
            let (hb, args_b) = self.app_spine(b);
            if args_a.len() == args_b.len() && self.heads_equal(ha, hb) {
                let mut all_eq = true;
                for (&xa, &xb) in args_a.iter().zip(&args_b) {
                    if !self.is_def_eq(xa, xb)? {
                        all_eq = false;
                        break;
                    }
                }
                if all_eq {
                    return Ok(true);
                }
            }

            match (self.delta_info(ha), self.delta_info(hb)) {
                (Some((va, pa, la, ppa)), Some((vb, pb, lb, ppb))) => {
                    if pa >= pb {
                        a = self.unfold_delta_app(va, &ppa, &la, &args_a);
                    }
                    if pb >= pa {
                        b = self.unfold_delta_app(vb, &ppb, &lb, &args_b);
                    }
                }
                (Some((va, _, la, ppa)), None) => a = self.unfold_delta_app(va, &ppa, &la, &args_a),
                (None, Some((vb, _, lb, ppb))) => b = self.unfold_delta_app(vb, &ppb, &lb, &args_b),
                (None, None) => {
                    return Ok(self.try_struct_eta(a, b)? || self.try_struct_eta(b, a)?);
                }
            }
        }
    }

    fn try_fun_eta(&mut self, name: NameId, bi: BinderInfo, ty: ExprId, body: ExprId, other: ExprId) -> Result<bool, KernelError> {
        if matches!(self.arena.get_expr(other), ExprData::Sort(_) | ExprData::Pi { .. } | ExprData::Lit(_) | ExprData::Lam { .. }) {
            return Ok(false);
        }
        let other_ty = self.infer_type(other)?;
        let other_ty_w = self.whnf(other_ty);
        let ExprData::Pi { ty: dom, .. } = *self.arena.get_expr(other_ty_w) else { return Ok(false) };
        if !self.is_def_eq(ty, dom)? {
            return Ok(false);
        }
        let fv: FVarId = self.push_local(name, bi, ty, None);
        let fve = self.arena.fvar(fv);
        let (lhs, rhs) = (instantiate1(self.arena, body, fve), self.arena.app(other, fve));
        let res = self.is_def_eq(lhs, rhs);
        self.pop_local();
        res
    }

    fn try_struct_eta(&mut self, ctor_side: ExprId, other: ExprId) -> Result<bool, KernelError> {
        let (head, args) = self.app_spine(ctor_side);
        let ExprData::Const(cname, _) = *self.arena.get_expr(head) else { return Ok(false) };
        let Some(Declaration::Constructor(c)) = self.decls.get(&cname).cloned() else { return Ok(false) };
        let Some(Declaration::Inductive(ind)) = self.decls.get(&c.ind_name).cloned() else { return Ok(false) };
        if ind.is_prop || ind.is_rec || ind.ctors.len() != 1 || ind.num_indices != 0 || ind.all.len() != 1
            || args.len() != (c.num_params + c.num_fields) as usize
        {
            return Ok(false);
        }
        let other_ty = self.infer_type(other)?;
        let other_ty_w = self.whnf(other_ty);
        let (ohead, oargs) = self.app_spine(other_ty_w);
        if !matches!(self.arena.get_expr(ohead), ExprData::Const(n, _) if *n == ind.name && oargs.len() == ind.num_params as usize) {
            return Ok(false);
        }
        for fi in 0..c.num_fields {
            let rhs = self.arena.proj(ind.name, fi, other);
            if !self.is_def_eq(args[c.num_params as usize + fi as usize], rhs)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn heads_equal(&mut self, ha: ExprId, hb: ExprId) -> bool {
        if ha == hb {
            return true;
        }
        match (self.arena.get_expr(ha).clone(), self.arena.get_expr(hb).clone()) {
            (ExprData::Const(na, la), ExprData::Const(nb, lb)) if na == nb && la.len() == lb.len() => {
                la.iter().zip(lb.iter()).all(|(&x, &y)| level_eq(self.arena, x, y))
            }
            (
                ExprData::Proj { struct_name: sa, idx: ia, expr: ea },
                ExprData::Proj { struct_name: sb, idx: ib, expr: eb },
            ) if sa == sb && ia == ib => self.is_def_eq(ea, eb).unwrap_or(false),
            _ => false,
        }
    }
}

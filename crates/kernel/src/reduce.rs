//! Unified spine-machine WHNF reducer and definitional equality engine.
//! Supports beta, zeta, iota, K-like, quotient, `Nat` literals, structure projections,
//! height-ordered delta, proof irrelevance in `Prop`, and function + structure eta-conversion.

use crate::arena::{BinderInfo, ExprData, ExprId, FVarId, LevelId, Literal, NameId};
use crate::check::TypeChecker;
use crate::env::{Declaration, QuotKind};
use crate::error::KernelError;
use crate::expr::{instantiate1, instantiate_level_params, instantiate_rev};
use crate::level::{level_eq, level_is_zero};

impl<'a> TypeChecker<'a> {
    /// Cached universe-parameter instantiation (O(1) hit for the common 1-param case).
    pub(crate) fn inst_levels_cached(&mut self, e: ExprId, params: &[NameId], lvls: &[LevelId]) -> ExprId {
        if params.is_empty() || !self.arena.get_expr_meta(e).has_level_param() {
            return e;
        }
        if lvls.len() == 1 {
            let key = (e, lvls[0]);
            if let Some(&res) = self.inst_lvl1_cache.get(&key) {
                return res;
            }
            let res = instantiate_level_params(self.arena, e, params, lvls);
            self.inst_lvl1_cache.insert(key, res);
            return res;
        }
        instantiate_level_params(self.arena, e, params, lvls)
    }

    #[inline]
    fn inst_levels_opt(&mut self, e: ExprId, params: &[NameId], l0: Option<LevelId>, lvls: Option<&[LevelId]>) -> ExprId {
        match (l0, lvls) {
            (Some(l), _) => self.inst_levels_cached(e, params, &[l]),
            (None, Some(ls)) => self.inst_levels_cached(e, params, ls),
            (None, None) => e,
        }
    }

    /// Reduce `e` to weak head normal form (beta + zeta + iota + proj + quot + delta).
    pub fn whnf(&mut self, e: ExprId) -> ExprId {
        if let Some(&cached) = self.whnf_cache.get(&e) {
            return cached;
        }
        let cur = self.whnf_spine(e, true);
        self.whnf_cache.insert(e, cur);
        cur
    }

    /// Reduce `e` to weak head normal form without delta unfolding.
    #[inline]
    pub(crate) fn whnf_no_delta(&mut self, e: ExprId) -> ExprId {
        self.whnf_spine(e, false)
    }

    fn whnf_spine(&mut self, e: ExprId, allow_delta: bool) -> ExprId {
        match self.arena.get_expr(e) {
            ExprData::Sort(_) | ExprData::Pi { .. } | ExprData::Lam { .. } | ExprData::Lit(_) | ExprData::BVar(_) => {
                return e;
            }
            ExprData::Const(_, _) if !allow_delta => return e,
            _ => {}
        }
        self.whnf_spine_with(e, Vec::new(), allow_delta)
    }

    /// Unified spine abstract machine: keeps arguments on `spine` across beta, zeta,
    /// local FVar, Proj, Quot.lift, Recursor iota/K, and delta steps without interning
    /// intermediate `App` nodes into the arena.
    fn whnf_spine_with(&mut self, mut cur: ExprId, mut spine: Vec<ExprId>, allow_delta: bool) -> ExprId {
        loop {
            match self.arena.get_expr(cur) {
                ExprData::App(f, a) => {
                    let (f, a) = (*f, *a);
                    spine.push(a);
                    cur = f;
                }
                ExprData::Lam { body, .. } if !spine.is_empty() => {
                    let mut body = *body;
                    let first = spine.pop().unwrap();
                    if spine.is_empty() {
                        cur = instantiate1(self.arena, body, first);
                    } else {
                        let mut args = Vec::with_capacity(spine.len() + 1);
                        args.push(first);
                        while !spine.is_empty() {
                            if let ExprData::Lam { body: next, .. } = self.arena.get_expr(body) {
                                body = *next;
                                args.push(spine.pop().unwrap());
                            } else {
                                break;
                            }
                        }
                        cur = instantiate_rev(self.arena, body, &args);
                    }
                }
                ExprData::Let { val, body, .. } => {
                    let (val, body) = (*val, *body);
                    cur = instantiate1(self.arena, body, val);
                }
                ExprData::FVar(fv) => match self.local_value(*fv) {
                    Some(val) => cur = val,
                    None => break,
                },
                ExprData::Proj { struct_name, idx, expr } => {
                    let (sn, idx, expr) = (*struct_name, *idx, *expr);
                    if let Some(v) = self.reduce_proj_head(sn, idx, expr) {
                        cur = v;
                    } else {
                        break;
                    }
                }
                ExprData::Const(name, lvls) => {
                    let name = *name;
                    let lvl_len = lvls.len();
                    let (l0, lvls_owned) = split_lvls(lvls);
                    if lvl_len == 0 {
                        if let Some((res, consumed)) = self.try_reduce_nat(name, &spine, allow_delta) {
                            let new_len = spine.len() - consumed;
                            spine.truncate(new_len);
                            cur = res;
                            continue;
                        }
                    }
                    let Some(decl) = self.decls.get(&name) else { break };
                    match decl {
                        Declaration::Quot { kind: QuotKind::Lift, .. } if spine.len() >= 6 => {
                            let len = spine.len();
                            let major = self.whnf(spine[len - 6]);
                            let (mhead, margs) = self.app_spine(major);
                            if let ExprData::Const(mn, _) = self.arena.get_expr(mhead) {
                                if matches!(self.decls.get(mn), Some(Declaration::Quot { kind: QuotKind::Ctor, .. }))
                                    && margs.len() == 3
                                {
                                    let f = spine[len - 4];
                                    spine.truncate(len - 6);
                                    spine.push(margs[2]);
                                    cur = f;
                                    continue;
                                }
                            }
                            break;
                        }
                        Declaration::Recursor(rec) if lvl_len == rec.level_params.len() => {
                            let prefix_end = (rec.num_params + rec.num_motives + rec.num_minors) as usize;
                            let major_idx = prefix_end + rec.num_indices as usize;
                            let len = spine.len();
                            if len <= major_idx {
                                break;
                            }
                            let mut major = self.whnf_lit_ctor(spine[len - 1 - major_idx]);
                            if let ExprData::Lit(Literal::Nat(k)) = self.arena.get_expr(major) {
                                let k = k.clone();
                                major = self.expand_nat_lit(&k);
                            }
                            if rec.k && rec.rules.len() == 1 && rec.rules[0].num_fields == 0 {
                                let rule = &rec.rules[0];
                                if let Some(Declaration::Constructor(c)) = self.decls.get(&rule.ctor_name) {
                                    if let Ok(major_ty) = self.infer_type_only(major) {
                                        let mut ctor_ty = if let Some(ref ls) = lvls_owned {
                                            let ind_lvls = &ls[ls.len() - c.level_params.len()..];
                                            self.inst_levels_cached(c.ty, &c.level_params, ind_lvls)
                                        } else if c.level_params.is_empty() {
                                            c.ty
                                        } else {
                                            self.inst_levels_cached(c.ty, &c.level_params, &[l0.unwrap()])
                                        };
                                        let mut ok = true;
                                        for i in 0..rec.num_params as usize {
                                            ctor_ty = self.whnf(ctor_ty);
                                            if let ExprData::Pi { body, .. } = self.arena.get_expr(ctor_ty) {
                                                ctor_ty = instantiate1(self.arena, *body, spine[len - 1 - i]);
                                            } else {
                                                ok = false;
                                                break;
                                            }
                                        }
                                        if ok && self.is_def_eq(major_ty, ctor_ty).unwrap_or(false) {
                                            cur = self.inst_levels_opt(rule.rhs, &rec.level_params, l0, lvls_owned.as_deref());
                                            spine.drain(len - 1 - major_idx..len - prefix_end);
                                            continue;
                                        }
                                    }
                                }
                            }
                            let (mut mhead, mut margs) = self.app_spine(major);
                            // Structure eta in WHNF (Lean 4 `to_ctor_when_structure`):
                            // expand opaque `x : S` to `S.mk p... (x.0) ...` for non-Prop structures.
                            if rec.rules.len() == 1 && rec.all.len() == 1 && rec.num_indices == 0
                                && !matches!(self.arena.get_expr(mhead), ExprData::Const(cn, _) if *cn == rec.rules[0].ctor_name || *cn == name)
                            {
                                if let Some(Declaration::Inductive(ind)) = self.decls.get(&rec.all[0]) {
                                    if !ind.is_prop && !ind.is_rec && ind.ctors.len() == 1 && ind.num_indices == 0 && ind.all.len() == 1 {
                                        if let Ok(mty) = self.infer_type_only(major) {
                                            let mty_w = self.whnf(mty);
                                            let (th, ta) = self.app_spine(mty_w);
                                            if let ExprData::Const(tn, tls) = self.arena.get_expr(th) {
                                                if *tn == ind.name && ta.len() == ind.num_params as usize {
                                                    let tls = tls.clone();
                                                    mhead = self.arena.const_(ind.ctors[0], tls);
                                                    margs = ta;
                                                    for fi in 0..rec.rules[0].num_fields {
                                                        margs.push(self.arena.proj(ind.name, fi, major));
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                            if let ExprData::Const(cname, _) = self.arena.get_expr(mhead) {
                                let cname = *cname;
                                if let Some(rule) = rec.rules.iter().find(|r| r.ctor_name == cname) {
                                    let ctor_np = match self.decls.get(&cname) {
                                        Some(Declaration::Constructor(c)) => c.num_params,
                                        _ => rec.num_params,
                                    };
                                    if margs.len() == (ctor_np + rule.num_fields) as usize {
                                        cur = self.inst_levels_opt(rule.rhs, &rec.level_params, l0, lvls_owned.as_deref());
                                        let keep_tail = len - 1 - major_idx;
                                        spine.splice(
                                            keep_tail..len - prefix_end,
                                            margs[ctor_np as usize..].iter().rev().copied(),
                                        );
                                        continue;
                                    }
                                }
                            }
                            break;
                        }
                        _ if allow_delta => {
                            if let Some((val, _)) = decl.delta_value() {
                                let params = decl.level_params();
                                if lvl_len == params.len() {
                                    cur = self.inst_levels_opt(val, params, l0, lvls_owned.as_deref());
                                    continue;
                                }
                            }
                            break;
                        }
                        _ => break,
                    }
                }
                _ => break,
            }
        }
        while let Some(arg) = spine.pop() {
            cur = self.arena.app(cur, arg);
        }
        cur
    }

    fn reduce_proj_head(&mut self, struct_name: NameId, idx: u32, expr: ExprId) -> Option<ExprId> {
        let ind = match self.decls.get(&struct_name)? {
            Declaration::Inductive(i) if i.ctors.len() == 1 && i.num_indices == 0 => i,
            _ => return None,
        };
        let val = self.whnf_lit_ctor(expr);
        let (vhead, vargs) = self.app_spine(val);
        if let ExprData::Const(cname, _) = self.arena.get_expr(vhead) {
            let pos = ind.num_params as usize + idx as usize;
            if *cname == ind.ctors[0] && pos < vargs.len() {
                return Some(vargs[pos]);
            }
        }
        None
    }

    pub(crate) fn app_spine(&self, mut e: ExprId) -> (ExprId, Vec<ExprId>) {
        if !matches!(self.arena.get_expr(e), ExprData::App(_, _)) {
            return (e, Vec::new());
        }
        let mut args = Vec::new();
        while let ExprData::App(f, a) = self.arena.get_expr(e) {
            args.push(*a);
            e = *f;
        }
        args.reverse();
        (e, args)
    }

    #[inline]
    fn expand_nat_lit(&mut self, k: &crate::nat::Nat) -> ExprId {
        if k.is_zero() {
            if let Some(z) = self.nat_zero { z } else {
                let z = self.arena.const_path("Nat.zero", []);
                self.nat_zero = Some(z);
                z
            }
        } else {
            let succ = if let Some(s) = self.nat_succ { s } else {
                let s = self.arena.const_path("Nat.succ", []);
                self.nat_succ = Some(s);
                s
            };
            let pred = self.arena.lit_nat_big(k.sub(&crate::nat::Nat::from_u128(1)));
            self.arena.app(succ, pred)
        }
    }

    /// Lean 4 kernel string literal expansion: `"ab"` is definitionally
    /// `String.ofList [Char.ofNat 97, Char.ofNat 98]`. Used only when a recursor, a projection or a
    /// definitional-equality check needs the structure of the literal.
    fn expand_str_lit(&mut self, s: &str) -> ExprId {
        let l0 = self.arena.lvl_nat(0);
        let char_t = self.arena.const_path("Char", []);
        let of_nat = self.arena.const_path("Char.ofNat", []);
        let nil = self.arena.const_path("List.nil", [l0]);
        let cons = self.arena.const_path("List.cons", [l0]);
        let mut list = self.arena.app(nil, char_t);
        for c in s.chars().rev() {
            let code = self.arena.lit_nat(c as u128);
            let ch = self.arena.app(of_nat, code);
            list = self.arena.app_n(cons, &[char_t, ch, list]);
        }
        let of_list = self.arena.const_path("String.ofList", []);
        self.arena.app(of_list, list)
    }

    /// WHNF that also opens a string literal into its constructor form.
    fn whnf_lit_ctor(&mut self, e: ExprId) -> ExprId {
        let w = self.whnf(e);
        if let ExprData::Lit(Literal::Str(s)) = self.arena.get_expr(w) {
            let s = s.clone();
            let ex = self.expand_str_lit(&s);
            return self.whnf(ex);
        }
        w
    }

    /// Lean 4 kernel `reduce_nat`: O(1) machine evaluation of closed `Nat` literal primitives.
    /// Does `e` mention a local without a `let` value?
    fn has_opaque_fvar(&self, e: ExprId) -> bool {
        if !self.arena.get_expr_meta(e).has_fvar() { return false; }
        let mut stack = vec![e];
        let mut seen = crate::hash::FxHashSet::default();
        while let Some(x) = stack.pop() {
            if !self.arena.get_expr_meta(x).has_fvar() || !seen.insert(x) { continue; }
            match self.arena.get_expr(x) {
                ExprData::FVar(fv) => match self.local_value(*fv) {
                    None => return true,
                    Some(v) => stack.push(v),
                },
                ExprData::App(f, a) => { stack.push(*f); stack.push(*a); }
                ExprData::Lam { ty, body, .. } | ExprData::Pi { ty, body, .. } => { stack.push(*ty); stack.push(*body); }
                ExprData::Let { ty, val, body, .. } => { stack.push(*ty); stack.push(*val); stack.push(*body); }
                ExprData::Proj { expr, .. } => stack.push(*expr),
                _ => {}
            }
        }
        false
    }

    fn try_reduce_nat(&mut self, name: NameId, spine: &[ExprId], allow_succ: bool) -> Option<(ExprId, usize)> {
        use crate::nat::{Nat, MAX_BITS};
        let len = spine.len();
        if len == 0 { return None; }
        let crate::arena::NameData::Str(parent, seg) = self.arena.get_name(name) else { return None };
        let crate::arena::NameData::Str(gp, pseg) = self.arena.get_name(*parent) else { return None };
        if *gp != crate::arena::Arena::ANONYMOUS || pseg.as_ref() != "Nat" { return None; }
        // The binary operations Lean's kernel evaluates on literals (GMP there, `Nat` here).
        let op: &'static str = match seg.as_ref() {
            "succ" if allow_succ => "succ", "log2" => "log2",
            "add" => "add", "sub" => "sub", "mul" => "mul", "pow" => "pow", "div" => "div", "mod" => "mod",
            "gcd" => "gcd", "beq" => "beq", "ble" => "ble", "land" => "land", "lor" => "lor", "xor" => "xor",
            "shiftLeft" => "shiftLeft", "shiftRight" => "shiftRight",
            _ => return None,
        };
        let as_nat = |tc: &mut Self, e: ExprId| -> Option<Nat> {
            let w = tc.whnf(e);
            match tc.arena.get_expr(w) {
                ExprData::Lit(Literal::Nat(n)) => Some(n.clone()),
                ExprData::Const(cn, _) => match tc.arena.get_name(*cn) {
                    crate::arena::NameData::Str(p, s) if s.as_ref() == "zero" => match tc.arena.get_name(*p) {
                        crate::arena::NameData::Str(g, ps) if *g == crate::arena::Arena::ANONYMOUS && ps.as_ref() == "Nat" => Some(Nat::zero()),
                        _ => None,
                    },
                    _ => None,
                },
                _ => None,
            }
        };
        // As in Lean's `reduce_nat`: only closed terms can evaluate to literals, so never whnf an
        // argument that mentions a free variable without a value (that would unfold open
        // arithmetic for nothing). `let`-bound variables count as closed: Lean substitutes them.
        let arity = if op == "succ" || op == "log2" { 1 } else { 2 };
        if len < arity || spine[len - arity..].iter().any(|&x| self.has_opaque_fvar(x)) {
            return None;
        }
        if op == "succ" || op == "log2" {
            let a = as_nat(self, spine[len - 1])?;
            let r = if op == "succ" { a.add(&Nat::from_u128(1)) } else { a.log2() };
            return Some((self.arena.lit_nat_big(r), 1));
        }
        if len < 2 { return None; }
        let a = as_nat(self, spine[len - 1])?;
        let b = as_nat(self, spine[len - 2])?;
        let r = match op {
            "add" => a.add(&b),
            "sub" => a.sub(&b),
            "mul" => a.mul(&b),
            "pow" => a.pow(&b)?,
            "div" => a.div(&b),
            "mod" => a.rem(&b),
            "gcd" => a.gcd(&b),
            "land" => a.land(&b),
            "lor" => a.lor(&b),
            "xor" => a.xor(&b),
            "shiftLeft" => {
                let k = b.to_u64().filter(|k| a.bits().saturating_add(*k) <= MAX_BITS)?;
                a.shl(k)
            }
            "shiftRight" => a.shr(b.to_u64().unwrap_or(u64::MAX)),
            "beq" | "ble" => {
                let res = if op == "beq" { a == b } else { a <= b };
                let p = if res { "Bool.true" } else { "Bool.false" };
                return Some((self.arena.const_path(p, []), 2));
            }
            _ => return None,
        };
        Some((self.arena.lit_nat_big(r), 2))
    }

    fn delta_info(&self, head: ExprId) -> Option<(ExprId, u64, &'a [NameId], Option<LevelId>, Option<Box<[LevelId]>>)> {
        let ExprData::Const(name, lvls) = self.arena.get_expr(head) else { return None };
        let decl = self.decls.get(name)?;
        let (val, prio) = decl.delta_value()?;
        let params = decl.level_params();
        if lvls.len() != params.len() { return None; }
        let (l0, lvls_owned) = split_lvls(lvls);
        Some((val, prio, params, l0, lvls_owned))
    }

    fn unfold_delta_app(&mut self, val: ExprId, params: &[NameId], l0: Option<LevelId>, lvls: Option<&[LevelId]>, args: &[ExprId]) -> ExprId {
        let inst = self.inst_levels_opt(val, params, l0, lvls);
        let spine: Vec<ExprId> = args.iter().rev().copied().collect();
        self.whnf_spine_with(inst, spine, false)
    }

    fn is_proof(&mut self, e: ExprId) -> Result<Option<ExprId>, KernelError> {
        if matches!(self.arena.get_expr(e), ExprData::Sort(_) | ExprData::Pi { .. } | ExprData::Lit(_)) {
            return Ok(None);
        }
        let prev = self.infer_only;
        self.infer_only = true;
        let r = self.infer_type(e).and_then(|ty| self.infer_sort(ty).map(|s| (ty, s)));
        self.infer_only = prev;
        let (ty, sort) = r?;
        Ok(level_is_zero(self.arena, sort).then_some(ty))
    }

    /// Definitional equality `a ≡ b` with DAG memoization.
    pub fn is_def_eq(&mut self, a: ExprId, b: ExprId) -> Result<bool, KernelError> {
        if a == b { return Ok(true); }
        let key = if a.0 <= b.0 { (a, b) } else { (b, a) };
        if self.def_eq_cache.contains(&key) { return Ok(true); }
        if self.def_neq_cache.contains(&key) { return Ok(false); }
        let eq = self.is_def_eq_core(a, b)?;
        if eq { self.def_eq_cache.insert(key); } else { self.def_neq_cache.insert(key); }
        Ok(eq)
    }

    fn is_def_eq_core(&mut self, mut a: ExprId, mut b: ExprId) -> Result<bool, KernelError> {
        a = self.whnf_no_delta(a);
        b = self.whnf_no_delta(b);
        let mut checked_proof = false;

        loop {
            if a == b { return Ok(true); }
            match (self.arena.get_expr(a), self.arena.get_expr(b)) {
                (ExprData::Sort(u), ExprData::Sort(v)) => {
                    let (u, v) = (*u, *v);
                    return Ok(level_eq(self.arena, u, v));
                }
                (ExprData::Lit(x), ExprData::Lit(y)) => return Ok(x == y),
                (ExprData::Lit(Literal::Nat(k)), _) => { let k = k.clone(); a = self.expand_nat_lit(&k); continue; }
                (_, ExprData::Lit(Literal::Nat(k))) => { let k = k.clone(); b = self.expand_nat_lit(&k); continue; }
                (ExprData::Lit(Literal::Str(sv)), _) => { let sv = sv.clone(); let ex = self.expand_str_lit(&sv); a = self.whnf_no_delta(ex); continue; }
                (_, ExprData::Lit(Literal::Str(sv))) => { let sv = sv.clone(); let ex = self.expand_str_lit(&sv); b = self.whnf_no_delta(ex); continue; }
                (ExprData::Pi { name, binder_info, ty: t1, body: b1 }, ExprData::Pi { ty: t2, body: b2, .. }) => {
                    let (name, bi, t1, b1, t2, b2) = (*name, *binder_info, *t1, *b1, *t2, *b2);
                    if !self.is_def_eq(t1, t2)? { return Ok(false); }
                    let fv = self.push_local(name, bi, t1, None);
                    let fve = self.arena.fvar(fv);
                    let (ib1, ib2) = (instantiate1(self.arena, b1, fve), instantiate1(self.arena, b2, fve));
                    let res = self.is_def_eq(ib1, ib2);
                    self.pop_local();
                    return res;
                }
                (ExprData::Lam { name, binder_info, ty: t1, body: b1 }, ExprData::Lam { ty: t2, body: b2, .. }) => {
                    let (name, bi, t1, b1, t2, b2) = (*name, *binder_info, *t1, *b1, *t2, *b2);
                    if self.is_def_eq(t1, t2)? {
                        let fv = self.push_local(name, bi, t1, None);
                        let fve = self.arena.fvar(fv);
                        let (ib1, ib2) = (instantiate1(self.arena, b1, fve), instantiate1(self.arena, b2, fve));
                        let res = self.is_def_eq(ib1, ib2)?;
                        self.pop_local();
                        if res { return Ok(true); }
                    }
                    if !checked_proof {
                        if let (Some(ta), Some(tb)) = (self.is_proof(a)?, self.is_proof(b)?) {
                            return self.is_def_eq(ta, tb);
                        }
                    }
                    return Ok(false);
                }
                (ExprData::Lam { name, binder_info, ty, body }, _) => {
                    let (name, bi, ty, body) = (*name, *binder_info, *ty, *body);
                    if self.try_fun_eta(name, bi, ty, body, b)? { return Ok(true); }
                }
                (_, ExprData::Lam { name, binder_info, ty, body }) => {
                    let (name, bi, ty, body) = (*name, *binder_info, *ty, *body);
                    if self.try_fun_eta(name, bi, ty, body, a)? { return Ok(true); }
                }
                _ => {}
            }

            // Proof irrelevance before any structural comparison or unfolding, as in Lean's
            // `is_def_eq_core`: comparing two proofs' internals can force huge computations.
            if !checked_proof {
                checked_proof = true;
                if let (Some(ta), Some(tb)) = (self.is_proof(a)?, self.is_proof(b)?) {
                    return self.is_def_eq(ta, tb);
                }
            }

            let (ha, args_a) = self.app_spine(a);
            let (hb, args_b) = self.app_spine(b);
            if args_a.len() == args_b.len() && self.heads_equal(ha, hb) {
                let mut all_eq = true;
                for (&xa, &xb) in args_a.iter().zip(&args_b) {
                    if !self.is_def_eq(xa, xb)? { all_eq = false; break; }
                }
                if all_eq { return Ok(true); }
            }

            match (self.delta_info(ha), self.delta_info(hb)) {
                (Some((va, pa, ppa, l0a, la)), Some((vb, pb, ppb, l0b, lb))) => {
                    if pa >= pb { a = self.unfold_delta_app(va, ppa, l0a, la.as_deref(), &args_a); }
                    if pb >= pa { b = self.unfold_delta_app(vb, ppb, l0b, lb.as_deref(), &args_b); }
                }
                (Some((va, _, ppa, l0a, la)), None) => a = self.unfold_delta_app(va, ppa, l0a, la.as_deref(), &args_a),
                (None, Some((vb, _, ppb, l0b, lb))) => b = self.unfold_delta_app(vb, ppb, l0b, lb.as_deref(), &args_b),
                (None, None) => return Ok(self.try_struct_eta(a, b)? || self.try_struct_eta(b, a)? || self.try_unit_like(a, b)?),
            }
        }
    }

    fn try_fun_eta(&mut self, name: NameId, bi: BinderInfo, ty: ExprId, body: ExprId, other: ExprId) -> Result<bool, KernelError> {
        if matches!(self.arena.get_expr(other), ExprData::Sort(_) | ExprData::Pi { .. } | ExprData::Lit(_) | ExprData::Lam { .. }) {
            return Ok(false);
        }
        let other_ty = self.infer_type_only(other)?;
        let other_ty_w = self.whnf(other_ty);
        let ExprData::Pi { ty: dom, .. } = *self.arena.get_expr(other_ty_w) else { return Ok(false) };
        if !self.is_def_eq(ty, dom)? { return Ok(false); }
        let fv: FVarId = self.push_local(name, bi, ty, None);
        let fve = self.arena.fvar(fv);
        let (lhs, rhs) = (instantiate1(self.arena, body, fve), self.arena.app(other, fve));
        let res = self.is_def_eq(lhs, rhs);
        self.pop_local();
        res
    }

    /// Lean's `is_def_eq_unit_like`: any two terms of a non-recursive structure whose single
    /// constructor has no fields are equal (for example `Std.Rii α`), provided their types are.
    fn try_unit_like(&mut self, a: ExprId, b: ExprId) -> Result<bool, KernelError> {
        let a_ty = self.infer_type_only(a)?;
        let a_ty_w = self.whnf(a_ty);
        let (head, _) = self.app_spine(a_ty_w);
        let ExprData::Const(iname, _) = *self.arena.get_expr(head) else { return Ok(false) };
        let Some(Declaration::Inductive(ind)) = self.decls.get(&iname) else { return Ok(false) };
        if ind.is_rec || ind.ctors.len() != 1 || ind.num_indices != 0 || ind.all.len() != 1 {
            return Ok(false);
        }
        let Some(Declaration::Constructor(c)) = self.decls.get(&ind.ctors[0]) else { return Ok(false) };
        if c.num_fields != 0 {
            return Ok(false);
        }
        let b_ty = self.infer_type_only(b)?;
        self.is_def_eq(a_ty_w, b_ty)
    }

    fn try_struct_eta(&mut self, ctor_side: ExprId, other: ExprId) -> Result<bool, KernelError> {
        let (head, args) = self.app_spine(ctor_side);
        let ExprData::Const(cname, _) = *self.arena.get_expr(head) else { return Ok(false) };
        let Some(Declaration::Constructor(c)) = self.decls.get(&cname) else { return Ok(false) };
        let Some(Declaration::Inductive(ind)) = self.decls.get(&c.ind_name) else { return Ok(false) };
        if ind.is_prop || ind.is_rec || ind.ctors.len() != 1 || ind.num_indices != 0 || ind.all.len() != 1
            || args.len() != (c.num_params + c.num_fields) as usize
        {
            return Ok(false);
        }
        let other_ty = self.infer_type_only(other)?;
        let other_ty_w = self.whnf(other_ty);
        let (ohead, oargs) = self.app_spine(other_ty_w);
        if !matches!(self.arena.get_expr(ohead), ExprData::Const(n, _) if *n == ind.name && oargs.len() == ind.num_params as usize) {
            return Ok(false);
        }
        for fi in 0..c.num_fields {
            let rhs = self.arena.proj(ind.name, fi, other);
            if !self.is_def_eq(args[c.num_params as usize + fi as usize], rhs)? { return Ok(false); }
        }
        Ok(true)
    }

    fn heads_equal(&mut self, ha: ExprId, hb: ExprId) -> bool {
        if ha == hb { return true; }
        match (self.arena.get_expr(ha), self.arena.get_expr(hb)) {
            (ExprData::Const(na, la), ExprData::Const(nb, lb)) if na == nb && la.len() == lb.len() => {
                let (la, lb) = (la.clone(), lb.clone());
                la.iter().zip(lb.iter()).all(|(&x, &y)| level_eq(self.arena, x, y))
            }
            (ExprData::Proj { struct_name: sa, idx: ia, expr: ea }, ExprData::Proj { struct_name: sb, idx: ib, expr: eb })
                if sa == sb && ia == ib =>
            {
                let (ea, eb) = (*ea, *eb);
                self.is_def_eq(ea, eb).unwrap_or(false)
            }
            _ => false,
        }
    }
}

#[inline]
fn split_lvls(lvls: &[LevelId]) -> (Option<LevelId>, Option<Box<[LevelId]>>) {
    match lvls.len() {
        0 => (None, None),
        1 => (Some(lvls[0]), None),
        _ => (None, Some(lvls.into())),
    }
}


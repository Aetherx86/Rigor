//! Fast spine-based WHNF reducer and definitional equality engine.
//!
//! Supports beta, zeta (let + local let-bound fvars), delta (height-ordered unfolding),
//! proof irrelevance in `Prop`, and function eta-conversion, accelerated by DAG caches.

use crate::arena::{ExprData, ExprId, FVarId, LevelId};
use crate::check::TypeChecker;
use crate::error::KernelError;
use crate::expr::{instantiate1, instantiate_level_params, instantiate_rev};
use crate::level::{level_eq, level_is_zero};

impl<'a> TypeChecker<'a> {
    /// Reduce `e` to weak head normal form (beta + zeta + delta).
    pub fn whnf(&mut self, e: ExprId) -> ExprId {
        if let Some(&cached) = self.whnf_cache.get(&e) {
            return cached;
        }
        let mut cur = e;
        loop {
            cur = self.whnf_core(cur);
            if let Some(unfolded) = self.unfold_head_delta(cur) {
                cur = unfolded;
            } else {
                break;
            }
        }
        self.whnf_cache.insert(e, cur);
        cur
    }

    /// Spine-based WHNF without delta unfolding: reduces beta, zeta, and local let-bound fvars.
    /// Peels consecutive applications onto an explicit spine so `((λ x1..xn. body) a1..an)`
    /// performs a single simultaneous multi-substitution instead of `n` traversals.
    pub(crate) fn whnf_core(&mut self, mut e: ExprId) -> ExprId {
        let mut spine: Vec<ExprId> = Vec::new();
        loop {
            match self.arena.get_expr(e).clone() {
                ExprData::App(f, a) => {
                    spine.push(a);
                    e = f;
                }
                ExprData::Lam { body, .. } if !spine.is_empty() => {
                    // Peel as many consecutive lambdas as we have arguments on the spine.
                    let mut cur_body = body;
                    let mut args = Vec::with_capacity(spine.len());
                    args.push(spine.pop().unwrap());
                    while !spine.is_empty() {
                        if let ExprData::Lam { body: next, .. } = self.arena.get_expr(cur_body) {
                            cur_body = *next;
                            args.push(spine.pop().unwrap());
                        } else {
                            break;
                        }
                    }
                    e = instantiate_rev(self.arena, cur_body, &args);
                }
                ExprData::Let { val, body, .. } => {
                    e = instantiate1(self.arena, body, val);
                }
                ExprData::FVar(fv) => {
                    if let Some(val) = self.local_value(fv) {
                        e = val;
                    } else {
                        break;
                    }
                }
                _ => break,
            }
        }
        while let Some(arg) = spine.pop() {
            e = self.arena.app(e, arg);
        }
        e
    }

    /// Split `e` into `(head, args)` where `args` are in application order `[a_0, ..., a_{n-1}]`.
    pub(crate) fn app_spine(&self, mut e: ExprId) -> (ExprId, Vec<ExprId>) {
        let mut args = Vec::new();
        while let ExprData::App(f, a) = self.arena.get_expr(e) {
            args.push(*a);
            e = *f;
        }
        args.reverse();
        (e, args)
    }

    /// Look up delta-reduction priority and unfolded head value if `head` is a reducible `Const`.
    fn delta_info(&self, head: ExprId) -> Option<(ExprId, u64, Box<[LevelId]>, Box<[crate::arena::NameId]>)> {
        if let ExprData::Const(name, lvls) = self.arena.get_expr(head) {
            let decl = self.decls.get(name)?;
            let (val, prio) = decl.delta_value()?;
            if lvls.len() == decl.level_params().len() {
                return Some((val, prio, lvls.clone(), decl.level_params().into()));
            }
        }
        None
    }

    /// Unfold the delta-reducible head constant of `e` (preserving any spine arguments).
    fn unfold_head_delta(&mut self, e: ExprId) -> Option<ExprId> {
        let (head, args) = self.app_spine(e);
        let (val, _prio, lvls, params) = self.delta_info(head)?;
        let inst = instantiate_level_params(self.arena, val, &params, &lvls);
        Some(self.arena.app_n(inst, &args))
    }

    /// Check whether `e` is a proof (i.e. `infer_type(e) : Sort 0`).
    fn is_proof(&mut self, e: ExprId) -> Result<Option<ExprId>, KernelError> {
        match self.arena.get_expr(e) {
            ExprData::Sort(_) | ExprData::Pi { .. } | ExprData::Lit(_) => return Ok(None),
            _ => {}
        }
        let ty = self.infer_type(e)?;
        let sort = self.infer_sort(ty)?;
        if level_is_zero(self.arena, sort) {
            Ok(Some(ty))
        } else {
            Ok(None)
        }
    }

    /// Definitional equality `a ≡ b` under beta, delta, zeta, proof irrelevance in `Prop`, and eta.
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
        // 1. Cheap syntactic reduction (beta + zeta + local let).
        a = self.whnf_core(a);
        b = self.whnf_core(b);
        if a == b {
            return Ok(true);
        }

        // 2. Proof irrelevance: any two proofs of definitionally equal propositions are equal.
        if let Some(ty_a) = self.is_proof(a)? {
            if let Some(ty_b) = self.is_proof(b)? {
                return self.is_def_eq(ty_a, ty_b);
            }
        }

        // 3. Structural & height-guided delta unfolding loop.
        loop {
            if a == b {
                return Ok(true);
            }

            match (self.arena.get_expr(a).clone(), self.arena.get_expr(b).clone()) {
                (ExprData::Sort(u), ExprData::Sort(v)) => {
                    return Ok(level_eq(self.arena, u, v));
                }
                (ExprData::Lit(x), ExprData::Lit(y)) => {
                    return Ok(x == y);
                }
                (
                    ExprData::Pi {
                        name,
                        binder_info,
                        ty: t1,
                        body: b1,
                    },
                    ExprData::Pi {
                        ty: t2, body: b2, ..
                    },
                ) => {
                    if !self.is_def_eq(t1, t2)? {
                        return Ok(false);
                    }
                    let fv = self.push_local(name, binder_info, t1, None);
                    let fv_expr = self.arena.fvar(fv);
                    let ib1 = instantiate1(self.arena, b1, fv_expr);
                    let ib2 = instantiate1(self.arena, b2, fv_expr);
                    let res = self.is_def_eq(ib1, ib2);
                    self.pop_local();
                    return res;
                }
                (
                    ExprData::Lam {
                        name,
                        binder_info,
                        ty: t1,
                        body: b1,
                    },
                    ExprData::Lam {
                        ty: t2, body: b2, ..
                    },
                ) => {
                    if !self.is_def_eq(t1, t2)? {
                        return Ok(false);
                    }
                    let fv = self.push_local(name, binder_info, t1, None);
                    let fv_expr = self.arena.fvar(fv);
                    let ib1 = instantiate1(self.arena, b1, fv_expr);
                    let ib2 = instantiate1(self.arena, b2, fv_expr);
                    let res = self.is_def_eq(ib1, ib2);
                    self.pop_local();
                    return res;
                }
                // Function eta: `(fun x : T => body) ≡ f` when `f` has Pi type.
                (
                    ExprData::Lam {
                        name,
                        binder_info,
                        ty,
                        body,
                    },
                    _,
                ) => {
                    if self.try_eta(name, binder_info, ty, body, b)? {
                        return Ok(true);
                    }
                }
                (
                    _,
                    ExprData::Lam {
                        name,
                        binder_info,
                        ty,
                        body,
                    },
                ) => {
                    if self.try_eta(name, binder_info, ty, body, a)? {
                        return Ok(true);
                    }
                }
                _ => {}
            }

            // 4. Head-spine comparison + height-ordered delta unfolding.
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

            // Delta step: unfold the side with greater priority (height), or both if tied.
            let da = self.delta_info(ha);
            let db = self.delta_info(hb);
            match (da, db) {
                (Some((va, pa, la, ppa)), Some((vb, pb, lb, ppb))) => {
                    if pa > pb {
                        let inst = instantiate_level_params(self.arena, va, &ppa, &la);
                        let app_a = self.arena.app_n(inst, &args_a);
                        a = self.whnf_core(app_a);
                    } else if pb > pa {
                        let inst = instantiate_level_params(self.arena, vb, &ppb, &lb);
                        let app_b = self.arena.app_n(inst, &args_b);
                        b = self.whnf_core(app_b);
                    } else {
                        let ia = instantiate_level_params(self.arena, va, &ppa, &la);
                        let ib = instantiate_level_params(self.arena, vb, &ppb, &lb);
                        let app_a = self.arena.app_n(ia, &args_a);
                        let app_b = self.arena.app_n(ib, &args_b);
                        a = self.whnf_core(app_a);
                        b = self.whnf_core(app_b);
                    }
                }
                (Some((va, _, la, ppa)), None) => {
                    let inst = instantiate_level_params(self.arena, va, &ppa, &la);
                    let app_a = self.arena.app_n(inst, &args_a);
                    a = self.whnf_core(app_a);
                }
                (None, Some((vb, _, lb, ppb))) => {
                    let inst = instantiate_level_params(self.arena, vb, &ppb, &lb);
                    let app_b = self.arena.app_n(inst, &args_b);
                    b = self.whnf_core(app_b);
                }
                (None, None) => return Ok(false),
            }
        }
    }

    fn try_eta(
        &mut self,
        name: crate::arena::NameId,
        binder_info: crate::arena::BinderInfo,
        ty: ExprId,
        body: ExprId,
        other: ExprId,
    ) -> Result<bool, KernelError> {
        match self.arena.get_expr(other) {
            ExprData::Sort(_) | ExprData::Pi { .. } | ExprData::Lit(_) | ExprData::Lam { .. } => {
                return Ok(false);
            }
            _ => {}
        }
        let other_ty = self.infer_type(other)?;
        let other_ty_whnf = self.whnf(other_ty);
        let dom = match self.arena.get_expr(other_ty_whnf) {
            ExprData::Pi { ty: dom, .. } => *dom,
            _ => return Ok(false),
        };
        if !self.is_def_eq(ty, dom)? {
            return Ok(false);
        }
        let fv: FVarId = self.push_local(name, binder_info, ty, None);
        let fv_expr = self.arena.fvar(fv);
        let lhs = instantiate1(self.arena, body, fv_expr);
        let rhs = self.arena.app(other, fv_expr);
        let res = self.is_def_eq(lhs, rhs);
        self.pop_local();
        res
    }

    fn heads_equal(&mut self, ha: ExprId, hb: ExprId) -> bool {
        if ha == hb {
            return true;
        }
        match (self.arena.get_expr(ha).clone(), self.arena.get_expr(hb).clone()) {
            (ExprData::Const(na, la), ExprData::Const(nb, lb)) if na == nb && la.len() == lb.len() => {
                la.iter()
                    .zip(lb.iter())
                    .all(|(&x, &y)| level_eq(self.arena, x, y))
            }
            _ => false,
        }
    }
}

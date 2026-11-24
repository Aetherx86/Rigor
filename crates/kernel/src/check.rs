//! Bidirectional CIC type inference and declaration verification.

use crate::arena::{Arena, BinderInfo, ExprData, ExprId, FVarId, LevelId, NameId};
use crate::env::Declaration;
use crate::error::KernelError;
use crate::expr::{abstract_fvars, expr_check_level_params, instantiate1, instantiate_level_params, instantiate_rev};
use crate::hash::{FxHashMap, FxHashSet};
use crate::level::level_is_zero;

#[derive(Debug, Clone)]
pub(crate) struct LocalDecl {
    pub id: FVarId,
    pub ty: ExprId,
    pub val: Option<ExprId>,
}

/// Stateful per-declaration type checker holding thread-local caches and a local context.
pub struct TypeChecker<'a> {
    pub(crate) decls: &'a FxHashMap<NameId, Declaration>,
    pub(crate) arena: &'a mut Arena,
    pub(crate) locals: Vec<LocalDecl>,
    next_fvar: u32,
    pub(crate) whnf_cache: FxHashMap<ExprId, ExprId>,
    pub(crate) infer_cache: FxHashMap<ExprId, ExprId>,
    /// Lean's `infer_only` mode: types of terms built during reduction and definitional-equality
    /// checking are inferred without re-checking application arguments (such intermediate terms
    /// need not be well-typed on their own). Results live in a separate cache so that a term is
    /// never treated as checked because it was only inferred.
    pub(crate) infer_only: bool,
    pub(crate) infer_only_cache: FxHashMap<ExprId, ExprId>,
    /// Lean's `m_eager_reduce` mode: activated while checking the argument type of an
    /// `eagerReduce _ _` application, enabling `reduce_nat` and the `Bool.true` reflection fast
    /// path even on terms containing free variables.
    pub(crate) eager_reduce: bool,
    pub(crate) def_eq_cache: FxHashSet<(ExprId, ExprId)>,
    /// Pairs already shown not definitionally equal (Lean's failure cache); without it, nested
    /// structure eta and delta unfolding re-explore the same failing comparisons exponentially.
    pub(crate) def_neq_cache: FxHashSet<(ExprId, ExprId)>,
    pub(crate) inst_lvl1_cache: FxHashMap<(ExprId, LevelId), ExprId>,
    pub(crate) nat_zero: Option<ExprId>,
    pub(crate) nat_succ: Option<ExprId>,
}

impl<'a> TypeChecker<'a> {
    pub fn new(decls: &'a FxHashMap<NameId, Declaration>, arena: &'a mut Arena) -> Self {
        Self {
            decls,
            arena,
            locals: Vec::with_capacity(32),
            next_fvar: 0,
            whnf_cache: FxHashMap::default(),
            infer_cache: FxHashMap::default(),
            infer_only: false,
            infer_only_cache: FxHashMap::default(),
            eager_reduce: false,
            def_eq_cache: FxHashSet::default(),
            def_neq_cache: FxHashSet::default(),
            inst_lvl1_cache: FxHashMap::default(),
            nat_zero: None,
            nat_succ: None,
        }
    }

    pub(crate) fn fresh_fvar(&mut self) -> FVarId {
        let id = FVarId(self.next_fvar);
        self.next_fvar = self.next_fvar.checked_add(1).expect("FVarId overflow");
        id
    }

    pub(crate) fn push_local(&mut self, ty: ExprId, val: Option<ExprId>) -> FVarId {
        let id = self.fresh_fvar();
        self.locals.push(LocalDecl { id, ty, val });
        id
    }

    pub(crate) fn push_existing_local(&mut self, id: FVarId, ty: ExprId) {
        self.locals.push(LocalDecl { id, ty, val: None });
    }

    pub(crate) fn pop_local(&mut self) { self.locals.pop(); }

    pub(crate) fn local_type(&self, id: FVarId) -> Option<ExprId> {
        self.locals.iter().rev().find(|l| l.id == id).map(|l| l.ty)
    }

    pub(crate) fn local_value(&self, id: FVarId) -> Option<ExprId> {
        self.locals.iter().rev().find(|l| l.id == id).and_then(|l| l.val)
    }

    /// Infer the type of `e` in the current local context (DAG-memoized).
    pub fn infer_type(&mut self, e: ExprId) -> Result<ExprId, KernelError> {
        // Fast path for O(1) leaves: skip cache probe/insert.
        match *self.arena.get_expr(e) {
            ExprData::BVar(idx) => return Err(KernelError::UnboundBVar(idx)),
            ExprData::FVar(fv) => return self.local_type(fv).ok_or(KernelError::UnknownFVar(fv)),
            ExprData::Sort(u) => {
                let next = self.arena.lvl_succ(u);
                return Ok(self.arena.sort(next));
            }
            ExprData::Lit(lid) => {
                let is_nat = matches!(self.arena.get_lit(lid), crate::arena::Literal::Nat(_));
                let n = self.arena.name_from_path(if is_nat { "Nat" } else { "String" });
                if !self.decls.contains_key(&n) { return Err(KernelError::UnknownConstant(n)); }
                return Ok(self.arena.const_(n, []));
            }
            _ => {}
        }
        if let Some(&ty) = self.infer_cache.get(&e) {
            return Ok(ty);
        }
        if self.infer_only {
            if let Some(&ty) = self.infer_only_cache.get(&e) {
                return Ok(ty);
            }
        }
        let ty = self.infer_type_core(e)?;
        if self.infer_only { self.infer_only_cache.insert(e, ty); } else { self.infer_cache.insert(e, ty); }
        Ok(ty)
    }

    /// Infer a type without re-checking arguments (Lean's `infer_type(e, infer_only = true)`).
    pub(crate) fn infer_type_only(&mut self, e: ExprId) -> Result<ExprId, KernelError> {
        let prev = self.infer_only;
        self.infer_only = true;
        let r = self.infer_type(e);
        self.infer_only = prev;
        r
    }

    /// Infer the type of `ty`, reduce it to WHNF, and assert it is `Sort u`, returning `u`.
    pub fn infer_sort(&mut self, ty: ExprId) -> Result<LevelId, KernelError> {
        let ty_ty = self.infer_type(ty)?;
        let whnf = self.whnf(ty_ty);
        match self.arena.get_expr(whnf) {
            ExprData::Sort(u) => Ok(*u),
            _ => Err(KernelError::ExpectedSort(whnf)),
        }
    }

    fn infer_type_core(&mut self, e: ExprId) -> Result<ExprId, KernelError> {
        match self.arena.get_expr(e) {
            ExprData::BVar(idx) => Err(KernelError::UnboundBVar(*idx)),
            ExprData::FVar(fv) => self.local_type(*fv).ok_or(KernelError::UnknownFVar(*fv)),
            ExprData::Sort(u) => {
                let u = *u;
                let next = self.arena.lvl_succ(u);
                Ok(self.arena.sort(next))
            }
            ExprData::Const(name, lvls_id) => {
                let (name, lvls_id) = (*name, *lvls_id);
                let decl = self.decls.get(&name).ok_or(KernelError::UnknownConstant(name))?;
                let params = decl.level_params();
                let lvls: Box<[LevelId]> = self.arena.get_level_list(lvls_id).into();
                if lvls.len() != params.len() {
                    return Err(KernelError::LevelParamCountMismatch { constant: name, expected: params.len(), got: lvls.len() });
                }
                Ok(self.inst_levels_cached(decl.ty(), params, &lvls))
            }
            ExprData::App(f, a) => {
                let (f, a) = (*f, *a);
                if self.infer_only {
                    return self.infer_app_only(e);
                }
                let f_ty = self.infer_type(f)?;
                let f_ty_whnf = self.whnf(f_ty);
                let (dom, body) = match self.arena.get_expr(f_ty_whnf) {
                    ExprData::Pi { ty, body, .. } => (*ty, *body),
                    _ => return Err(KernelError::ExpectedPi(f_ty_whnf)),
                };
                let a_ty = self.infer_type(a)?;
                let prev = self.eager_reduce;
                self.eager_reduce |= self.is_eager_reduce(a);
                let eq = self.is_def_eq(a_ty, dom);
                self.eager_reduce = prev;
                if !eq? { return Err(KernelError::TypeMismatch { expected: dom, got: a_ty }); }
                Ok(instantiate1(self.arena, body, a))
            }
            ExprData::Pi { .. } => self.infer_pi_telescope(e),
            ExprData::Lam { .. } => self.infer_lam_telescope(e),
            ExprData::Let { .. } => self.infer_let_telescope(e),
            ExprData::Lit(lid) => {
                let is_nat = matches!(self.arena.get_lit(*lid), crate::arena::Literal::Nat(_));
                let n = self.arena.name_from_path(if is_nat { "Nat" } else { "String" });
                if !self.decls.contains_key(&n) { return Err(KernelError::UnknownConstant(n)); }
                Ok(self.arena.const_(n, []))
            }
            ExprData::Proj { struct_name, idx, expr } => {
                let (s, i, x) = (*struct_name, *idx, *expr);
                self.infer_proj(s, i, x)
            }
        }
    }

    /// Infer the type of a structure projection `Proj(S, idx, e)` while enforcing the
    /// Prop-elimination / Subsingleton soundness guard (never smuggle Type witnesses out of Prop).
    fn infer_proj(&mut self, struct_name: NameId, idx: u32, expr: ExprId) -> Result<ExprId, KernelError> {
        let err = |reason| KernelError::InvalidProjection { struct_name, idx, reason };
        let ind = match self.decls.get(&struct_name) {
            Some(Declaration::Inductive(i)) => i,
            _ => return Err(err("not an inductive type")),
        };
        if ind.ctors.len() != 1 || ind.num_indices != 0 || ind.all.len() != 1 {
            return Err(err("projection requires a non-mutual, 0-index, 1-constructor structure"));
        }
        let Some(Declaration::Constructor(ctor)) = self.decls.get(&ind.ctors[0]) else {
            unreachable!("structure constructor missing");
        };
        if idx >= ctor.num_fields {
            return Err(err("field index out of bounds"));
        }
        let expr_ty = self.infer_type(expr)?;
        let expr_ty_whnf = self.whnf(expr_ty);
        let (head, args) = self.app_spine(expr_ty_whnf);
        let lvls: Box<[LevelId]> = match *self.arena.get_expr(head) {
            ExprData::Const(n, ls) if n == struct_name && args.len() == ind.num_params as usize => {
                self.arena.get_level_list(ls).into()
            }
            _ => return Err(err("expression type does not match structure")),
        };

        let ctor_ty = instantiate_level_params(self.arena, ctor.ty, &ctor.level_params, &lvls);
        // parameters, then the earlier fields as projections of `expr`, then field `idx`'s type
        let earlier: Vec<ExprId> = (0..idx).map(|i| self.arena.proj(struct_name, i, expr)).collect();
        let args: Vec<ExprId> = args.into_iter().chain(earlier).collect();
        let (cur, complete) = self.inst_pis(ctor_ty, &args);
        let cur = self.whnf(cur);
        let ExprData::Pi { ty, .. } = *self.arena.get_expr(cur) else { unreachable!("constructor field telescope mismatch") };
        assert!(complete, "constructor telescope mismatch");
        if ind.is_prop && !ind.can_elim_large {
            let field_sort = self.infer_sort(ty)?;
            if !level_is_zero(self.arena, field_sort) {
                return Err(err("cannot project non-Prop field out of a non-Subsingleton Prop inductive"));
            }
        }
        Ok(ty)
    }

    /// Check that `decl` is completely well-formed and well-typed in the current environment.
    pub fn check_decl(&mut self, decl: &Declaration) -> Result<(), KernelError> {
        let params = decl.level_params();
        check_unique_params(params)?;
        let ty = decl.ty();
        expr_check_level_params(self.arena, ty, params)?;
        let ty_sort = self.infer_sort(ty)?;

        if let Declaration::Theorem { name, .. } = decl {
            if !level_is_zero(self.arena, ty_sort) {
                let sort = self.arena.sort(ty_sort);
                return Err(KernelError::TheoremNotInProp { name: *name, sort });
            }
        }
        let (Declaration::Definition { val, .. } | Declaration::Opaque { val, .. } | Declaration::Theorem { val, .. }) = decl else {
            return Ok(()); // axioms, quotients, and inductive types (checked when they were built)
        };
        expr_check_level_params(self.arena, *val, params)?;
        let val_ty = self.infer_type(*val)?;
        if !self.is_def_eq(val_ty, ty)? {
            return Err(KernelError::TypeMismatch { expected: ty, got: val_ty });
        }
        Ok(())
    }

    /// Instantiate the leading Pi binders of `e` (after whnf) with `args`; the flag is false if
    /// `e` had fewer binders than arguments (the missing ones are skipped).
    pub(crate) fn inst_pis(&mut self, mut e: ExprId, args: &[ExprId]) -> (ExprId, bool) {
        let mut complete = true;
        for &a in args {
            e = self.whnf(e);
            match *self.arena.get_expr(e) {
                ExprData::Pi { body, .. } => e = instantiate1(self.arena, body, a),
                _ => complete = false,
            }
        }
        (e, complete)
    }

    /// Batch `App` spine type inference in `infer_only` mode (matches Lean's `infer_app`).
    fn infer_app_only(&mut self, e: ExprId) -> Result<ExprId, KernelError> {
        let (head, args) = self.app_spine(e);
        let mut f_ty = self.infer_type(head)?;
        let mut i = 0;
        while i < args.len() {
            if !matches!(self.arena.get_expr(f_ty), ExprData::Pi { .. }) {
                f_ty = self.whnf(f_ty);
                if !matches!(self.arena.get_expr(f_ty), ExprData::Pi { .. }) {
                    return Err(KernelError::ExpectedPi(f_ty));
                }
            }
            let start = i;
            let mut body = f_ty;
            while i < args.len() {
                if let ExprData::Pi { body: next, .. } = *self.arena.get_expr(body) {
                    body = next;
                    i += 1;
                } else {
                    break;
                }
            }
            f_ty = instantiate_rev(self.arena, body, &args[start..i]);
        }
        Ok(f_ty)
    }

    /// Batched `Pi` telescope inference: peels all consecutive `Pi` binders and instantiates once.
    fn infer_pi_telescope(&mut self, mut cur: ExprId) -> Result<ExprId, KernelError> {
        let saved = self.locals.len();
        let (mut fvars, mut us) = (Vec::new(), Vec::new());
        let res = (|| -> Result<ExprId, KernelError> {
            while let ExprData::Pi { ty, body, .. } = *self.arena.get_expr(cur) {
                let dom = instantiate_rev(self.arena, ty, &fvars);
                us.push(self.infer_sort(dom)?);
                let fv = self.push_local(dom, None);
                fvars.push(self.arena.fvar(fv));
                cur = body;
            }
            let body_inst = instantiate_rev(self.arena, cur, &fvars);
            let mut v = self.infer_sort(body_inst)?;
            for u in us.into_iter().rev() {
                v = self.arena.lvl_imax(u, v);
            }
            Ok(self.arena.sort(v))
        })();
        self.locals.truncate(saved);
        res
    }

    /// Batched `Lam` telescope inference: peels consecutive `Lam` binders, instantiates and abstracts once.
    fn infer_lam_telescope(&mut self, mut cur: ExprId) -> Result<ExprId, KernelError> {
        let saved = self.locals.len();
        let (mut fvars, mut fvar_exprs): (Vec<FVarId>, Vec<ExprId>) = (Vec::new(), Vec::new());
        let mut binders: Vec<(NameId, BinderInfo, ExprId)> = Vec::new();
        let body_ty = (|| -> Result<ExprId, KernelError> {
            while let ExprData::Lam { name, binder_info, ty, body } = *self.arena.get_expr(cur) {
                let dom = instantiate_rev(self.arena, ty, &fvar_exprs);
                let _u = self.infer_sort(dom)?;
                let fv = self.push_local(dom, None);
                fvars.push(fv);
                fvar_exprs.push(self.arena.fvar(fv));
                binders.push((name, binder_info, ty));
                cur = body;
            }
            let body_inst = instantiate_rev(self.arena, cur, &fvar_exprs);
            self.infer_type(body_inst)
        })();
        self.locals.truncate(saved);
        let mut res = abstract_fvars(self.arena, body_ty?, &fvars);
        for (name, bi, orig_ty) in binders.into_iter().rev() {
            res = self.arena.pi(name, bi, orig_ty, res);
        }
        Ok(res)
    }

    /// Batched `Let` telescope inference: peels consecutive `Let` binders and instantiates body once.
    fn infer_let_telescope(&mut self, mut cur: ExprId) -> Result<ExprId, KernelError> {
        let saved = self.locals.len();
        let (mut fvars, mut fvar_exprs, mut vals): (Vec<FVarId>, Vec<ExprId>, Vec<ExprId>) =
            (Vec::new(), Vec::new(), Vec::new());
        let body_ty = (|| -> Result<ExprId, KernelError> {
            while let ExprData::Let { ty, val, body } = *self.arena.get_expr(cur) {
                let dom = instantiate_rev(self.arena, ty, &fvar_exprs);
                let _u = self.infer_sort(dom)?;
                let val_inst = instantiate_rev(self.arena, val, &fvar_exprs);
                if !self.infer_only {
                    let val_ty = self.infer_type(val_inst)?;
                    if !self.is_def_eq(val_ty, dom)? {
                        return Err(KernelError::TypeMismatch { expected: dom, got: val_ty });
                    }
                }
                let fv = self.push_local(dom, Some(val_inst));
                fvars.push(fv);
                fvar_exprs.push(self.arena.fvar(fv));
                vals.push(val_inst);
                cur = body;
            }
            let body_inst = instantiate_rev(self.arena, cur, &fvar_exprs);
            self.infer_type(body_inst)
        })();
        self.locals.truncate(saved);
        let mut res = body_ty?;
        for (&fv, &val) in fvars.iter().zip(&vals).rev() {
            if !self.arena.get_expr_meta(res).has_fvar() {
                break;
            }
            let abs = abstract_fvars(self.arena, res, &[fv]);
            if abs != res {
                res = instantiate1(self.arena, abs, val);
            }
        }
        Ok(res)
    }
}

pub(crate) fn check_unique_params(params: &[NameId]) -> Result<(), KernelError> {
    for (i, &p) in params.iter().enumerate() {
        if params[..i].contains(&p) {
            return Err(KernelError::DuplicateLevelParam(p));
        }
    }
    Ok(())
}


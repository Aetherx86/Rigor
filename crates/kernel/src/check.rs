//! Bidirectional CIC type inference and declaration verification.

use crate::arena::{Arena, BinderInfo, ExprData, ExprId, FVarId, LevelId, NameId};
use crate::env::Declaration;
use crate::error::KernelError;
use crate::expr::{abstract_fvars, expr_check_level_params, instantiate1, instantiate_level_params};
use crate::hash::{FxHashMap, FxHashSet};
use crate::level::level_is_zero;

#[derive(Debug, Clone)]
pub(crate) struct LocalDecl {
    pub id: FVarId,
    #[allow(dead_code)]
    pub name: NameId,
    #[allow(dead_code)]
    pub binder_info: BinderInfo,
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

    pub(crate) fn push_local(&mut self, name: NameId, binder_info: BinderInfo, ty: ExprId, val: Option<ExprId>) -> FVarId {
        let id = self.fresh_fvar();
        self.locals.push(LocalDecl { id, name, binder_info, ty, val });
        id
    }

    pub(crate) fn push_existing_local(&mut self, id: FVarId, name: NameId, binder_info: BinderInfo, ty: ExprId) {
        self.locals.push(LocalDecl { id, name, binder_info, ty, val: None });
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
                let decl = self
                    .decls
                    .get(&name)
                    .ok_or(KernelError::UnknownConstant(name))?;
                let params = decl.level_params();
                let lvls = self.arena.get_level_list(lvls_id);
                if lvls.len() != params.len() {
                    return Err(KernelError::LevelParamCountMismatch {
                        constant: name,
                        expected: params.len(),
                        got: lvls.len(),
                    });
                }
                let ty = decl.ty();
                if params.is_empty() || !self.arena.get_expr_meta(ty).has_level_param() {
                    return Ok(ty);
                }
                if lvls.len() == 1 {
                    let l0 = lvls[0];
                    return Ok(self.inst_levels_cached(ty, params, &[l0]));
                }
                let lvls: Box<[LevelId]> = lvls.into();
                Ok(instantiate_level_params(self.arena, ty, params, &lvls))
            }
            ExprData::App(f, a) => {
                let (f, a) = (*f, *a);
                let f_ty = self.infer_type(f)?;
                let f_ty_whnf = self.whnf(f_ty);
                let (dom, body) = match self.arena.get_expr(f_ty_whnf) {
                    ExprData::Pi { ty, body, .. } => (*ty, *body),
                    _ => return Err(KernelError::ExpectedPi(f_ty_whnf)),
                };
                if self.infer_only {
                    return Ok(instantiate1(self.arena, body, a));
                }
                let a_ty = self.infer_type(a)?;
                let eq = if self.is_eager_reduce(a) {
                    let prev = self.eager_reduce;
                    self.eager_reduce = true;
                    let r = self.is_def_eq(a_ty, dom);
                    self.eager_reduce = prev;
                    r?
                } else {
                    self.is_def_eq(a_ty, dom)?
                };
                if !eq {
                    return Err(KernelError::TypeMismatch {
                        expected: dom,
                        got: a_ty,
                    });
                }
                Ok(instantiate1(self.arena, body, a))
            }
            ExprData::Pi { name, binder_info, ty, body } => {
                let (name, binder_info, ty, body) = (*name, *binder_info, *ty, *body);
                let u = self.infer_sort(ty)?;
                let fv = self.push_local(name, binder_info, ty, None);
                let fv_expr = self.arena.fvar(fv);
                let body_inst = instantiate1(self.arena, body, fv_expr);
                let v = self.infer_sort(body_inst);
                self.pop_local();
                let v = v?;
                let res_lvl = self.arena.lvl_imax(u, v);
                Ok(self.arena.sort(res_lvl))
            }
            ExprData::Lam { name, binder_info, ty, body } => {
                let (name, binder_info, ty, body) = (*name, *binder_info, *ty, *body);
                let _u = self.infer_sort(ty)?;
                let fv = self.push_local(name, binder_info, ty, None);
                let fv_expr = self.arena.fvar(fv);
                let body_inst = instantiate1(self.arena, body, fv_expr);
                let body_ty = self.infer_type(body_inst);
                self.pop_local();
                let body_ty = body_ty?;
                let abs_body_ty = abstract_fvars(self.arena, body_ty, &[fv]);
                Ok(self.arena.pi(name, binder_info, ty, abs_body_ty))
            }
            ExprData::Let { ty, val, body } => {
                let (ty, val, body) = (*ty, *val, *body);
                let _u = self.infer_sort(ty)?;
                let val_ty = if self.infer_only { ty } else { self.infer_type(val)? };
                if !self.infer_only && !self.is_def_eq(val_ty, ty)? {
                    return Err(KernelError::TypeMismatch {
                        expected: ty,
                        got: val_ty,
                    });
                }
                let fv = self.push_local(Arena::ANONYMOUS, BinderInfo::Default, ty, Some(val));
                let fv_expr = self.arena.fvar(fv);
                let body_inst = instantiate1(self.arena, body, fv_expr);
                let body_ty = self.infer_type(body_inst);
                self.pop_local();
                let body_ty = body_ty?;
                let abs = abstract_fvars(self.arena, body_ty, &[fv]);
                Ok(instantiate1(self.arena, abs, val))
            }
            ExprData::Lit(lid) => match self.arena.get_lit(*lid) {
                crate::arena::Literal::Nat(_) => {
                    let nat_name = self.arena.name_from_path("Nat");
                    if self.decls.contains_key(&nat_name) {
                        Ok(self.arena.const_(nat_name, []))
                    } else {
                        Err(KernelError::UnknownConstant(nat_name))
                    }
                }
                crate::arena::Literal::Str(_) => {
                    let str_name = self.arena.name_from_path("String");
                    if self.decls.contains_key(&str_name) {
                        Ok(self.arena.const_(str_name, []))
                    } else {
                        Err(KernelError::UnknownConstant(str_name))
                    }
                }
            },
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

        let mut cur = instantiate_level_params(self.arena, ctor.ty, &ctor.level_params, &lvls);
        for &p_arg in &args {
            cur = self.whnf(cur);
            match self.arena.get_expr(cur) {
                ExprData::Pi { body, .. } => cur = instantiate1(self.arena, *body, p_arg),
                _ => unreachable!("constructor parameter telescope mismatch"),
            }
        }
        for field_i in 0..=idx {
            cur = self.whnf(cur);
            match self.arena.get_expr(cur) {
                ExprData::Pi { ty, body, .. } => {
                    let (ty, body) = (*ty, *body);
                    if field_i == idx {
                        if ind.is_prop && !ind.can_elim_large {
                            let field_sort = self.infer_sort(ty)?;
                            if !level_is_zero(self.arena, field_sort) {
                                return Err(err("cannot project non-Prop field out of a non-Subsingleton Prop inductive"));
                            }
                        }
                        return Ok(ty);
                    }
                    let prev_proj = self.arena.proj(struct_name, field_i, expr);
                    cur = instantiate1(self.arena, body, prev_proj);
                }
                _ => unreachable!("constructor field telescope mismatch"),
            }
        }
        unreachable!()
    }

    /// Check that `decl` is completely well-formed and well-typed in the current environment.
    pub fn check_decl(&mut self, decl: &Declaration) -> Result<(), KernelError> {
        let params = decl.level_params();
        check_unique_params(params)?;
        let ty = decl.ty();
        expr_check_level_params(self.arena, ty, params)?;
        let ty_sort = self.infer_sort(ty)?;

        match decl {
            Declaration::Axiom { .. }
            | Declaration::Inductive(_)
            | Declaration::Constructor(_)
            | Declaration::Recursor(_)
            | Declaration::Quot { .. } => Ok(()),
            Declaration::Definition { val, .. } | Declaration::Opaque { val, .. } => {
                expr_check_level_params(self.arena, *val, params)?;
                let val_ty = self.infer_type(*val)?;
                if !self.is_def_eq(val_ty, ty)? {
                    return Err(KernelError::TypeMismatch { expected: ty, got: val_ty });
                }
                Ok(())
            }
            Declaration::Theorem { name, val, .. } => {
                if !level_is_zero(self.arena, ty_sort) {
                    let sort = self.arena.sort(ty_sort);
                    return Err(KernelError::TheoremNotInProp { name: *name, sort });
                }
                expr_check_level_params(self.arena, *val, params)?;
                let val_ty = self.infer_type(*val)?;
                if !self.is_def_eq(val_ty, ty)? {
                    return Err(KernelError::TypeMismatch { expected: ty, got: val_ty });
                }
                Ok(())
            }
        }
    }
}

fn check_unique_params(params: &[NameId]) -> Result<(), KernelError> {
    for (i, &p) in params.iter().enumerate() {
        if params[..i].contains(&p) {
            return Err(KernelError::DuplicateLevelParam(p));
        }
    }
    Ok(())
}


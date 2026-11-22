//! Global environment storing verified declarations and supporting lock-free parallel checking.

use std::sync::Arc;

use crate::arena::{Arena, ExprData, ExprId, NameId};
use crate::check::TypeChecker;
use crate::error::KernelError;
use crate::expr::any_subexpr;
use crate::hash::FxHashMap;
use crate::inductive::{check_inductive_block, InductiveSpec};

/// Delta-reduction hint, matching Lean 4's `ReducibilityHints`.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ReducibilityHint {
    Opaque,
    Abbrev,
    Regular(u32),
}

#[derive(Debug, Clone)]
pub struct InductiveInfo {
    pub name: NameId, pub level_params: Box<[NameId]>, pub ty: ExprId,
    pub num_params: u32, pub num_indices: u32, pub all: Box<[NameId]>, pub ctors: Box<[NameId]>,
    pub is_rec: bool, pub is_prop: bool, pub can_elim_large: bool,
}

#[derive(Debug, Clone)]
pub struct ConstructorInfo {
    pub name: NameId, pub ind_name: NameId, pub level_params: Box<[NameId]>,
    pub ty: ExprId, pub num_params: u32, pub num_fields: u32,
}

#[derive(Debug, Clone)]
pub struct RecursorRule { pub ctor_name: NameId, pub num_fields: u32, pub rhs: ExprId }

#[derive(Debug, Clone)]
pub struct RecursorInfo {
    pub name: NameId, pub level_params: Box<[NameId]>, pub ty: ExprId, pub all: Box<[NameId]>,
    pub num_params: u32, pub num_indices: u32, pub num_motives: u32, pub num_minors: u32,
    pub rules: Box<[RecursorRule]>, pub k: bool,
}

#[derive(Debug, Clone)]
pub enum Declaration {
    Axiom { name: NameId, level_params: Box<[NameId]>, ty: ExprId },
    Definition { name: NameId, level_params: Box<[NameId]>, ty: ExprId, val: ExprId, hint: ReducibilityHint },
    Theorem { name: NameId, level_params: Box<[NameId]>, ty: ExprId, val: ExprId },
    Opaque { name: NameId, level_params: Box<[NameId]>, ty: ExprId, val: ExprId },
    Inductive(InductiveInfo),
    Constructor(ConstructorInfo),
    Recursor(RecursorInfo),
    Quot { name: NameId, level_params: Box<[NameId]>, ty: ExprId, kind: QuotKind },
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum QuotKind { Type, Ctor, Lift, Ind }

/// The same field of whichever declaration kind `$d` is.
macro_rules! decl_field {
    ($d:expr, $f:ident) => {
        match $d {
            Declaration::Axiom { $f, .. } | Declaration::Definition { $f, .. } | Declaration::Theorem { $f, .. }
            | Declaration::Opaque { $f, .. } | Declaration::Quot { $f, .. } => $f,
            Declaration::Inductive(i) => &i.$f,
            Declaration::Constructor(c) => &c.$f,
            Declaration::Recursor(r) => &r.$f,
        }
    };
}

impl Declaration {
    #[inline]
    pub fn name(&self) -> NameId { *decl_field!(self, name) }
    #[inline]
    pub fn level_params(&self) -> &[NameId] { decl_field!(self, level_params) }
    #[inline]
    pub fn ty(&self) -> ExprId { *decl_field!(self, ty) }

    #[inline]
    pub fn delta_value(&self) -> Option<(ExprId, u64)> {
        match self {
            Declaration::Definition { val, hint, .. } => match hint {
                ReducibilityHint::Opaque => None,
                ReducibilityHint::Abbrev => Some((*val, u64::MAX)),
                ReducibilityHint::Regular(h) => Some((*val, (*h as u64) + 1)),
            },
            Declaration::Theorem { val, .. } => Some((*val, 0)),
            _ => None,
        }
    }
}

/// Mutable environment used while sequentially building and verifying declarations.
#[derive(Debug, Default)]
pub struct Environment {
    pub arena: Arena,
    decls: FxHashMap<NameId, Declaration>,
    /// Deferred checking (see [`Environment::set_deferred_checking`]): admitted but not yet
    /// type-checked axioms, definitions, theorems and opaques, in admission order.
    defer: bool,
    deferred: Vec<NameId>,
}

impl Environment {
    pub fn new() -> Self { Self { arena: Arena::new(), decls: FxHashMap::default(), defer: false, deferred: Vec::new() } }
    #[inline]
    pub fn get(&self, name: NameId) -> Option<&Declaration> { self.decls.get(&name) }
    #[inline]
    pub fn len(&self) -> usize { self.decls.len() }

    /// Compute Lean 4-style definition height: `1 + max(height of referenced definitions)`.
    pub fn compute_height(&self, expr: ExprId) -> u32 {
        let mut h = 0;
        any_subexpr(&self.arena, expr, |_, _| false, |d| {
            if let ExprData::Const(n, _) = d {
                if let Some(Declaration::Definition { hint: ReducibilityHint::Regular(x), .. }) = self.decls.get(n) { h = h.max(*x); }
            }
            false
        });
        h.saturating_add(1)
    }

    /// Type-check and insert a declaration into the global environment.
    pub fn add_decl(&mut self, mut decl: Declaration) -> Result<(), KernelError> {
        let name = decl.name();
        if self.decls.contains_key(&name) { return Err(KernelError::DuplicateDeclaration(name)); }
        if let Declaration::Definition { val, hint: hint @ ReducibilityHint::Regular(0), .. } = &mut decl {
            *hint = ReducibilityHint::Regular(self.compute_height(*val));
        }
        if self.defer && matches!(decl, Declaration::Axiom { .. } | Declaration::Definition { .. } | Declaration::Theorem { .. } | Declaration::Opaque { .. }) {
            // Admit now, type-check later in `check_deferred`. Requiring every referenced constant
            // to exist already rules out self-reference and forward references, so the later
            // check sees exactly the environment a sequential check would have seen.
            let (ty, val) = match &decl {
                Declaration::Axiom { ty, .. } => (*ty, None),
                Declaration::Definition { ty, val, .. } | Declaration::Theorem { ty, val, .. } | Declaration::Opaque { ty, val, .. } => (*ty, Some(*val)),
                _ => unreachable!(),
            };
            self.require_known_consts(ty)?;
            if let Some(v) = val { self.require_known_consts(v)?; }
            self.decls.insert(name, decl);
            self.deferred.push(name);
            return Ok(());
        }
        let (nl, ll, lll, litl, el) = (
            self.arena.name_len(),
            self.arena.level_len(),
            self.arena.level_list_len(),
            self.arena.lit_len(),
            self.arena.expr_len(),
        );
        let res = {
            let mut tc = TypeChecker::new(&self.decls, &mut self.arena);
            tc.check_decl(&decl)
        };
        self.arena.truncate_to(nl, ll, lll, litl, el);
        res?;
        self.decls.insert(name, decl);
        Ok(())
    }

    /// Validate an inductive (or mutual inductive) block, enforce strict positivity and
    /// predicativity, generate constructors and recursors, and insert them atomically.
    pub fn add_inductive(&mut self, spec: InductiveSpec) -> Result<(), KernelError> {
        let generated = check_inductive_block(&self.decls, &mut self.arena, &spec)?;
        for d in generated {
            self.decls.insert(d.name(), d);
        }
        Ok(())
    }

    /// Register Lean 4's four quotient primitives (`Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind`).
    /// Requires `Eq` to already be declared in the environment.
    pub fn add_quot(&mut self) -> Result<(), KernelError> {
        use crate::arena::BinderInfo::{Default as BD, Implicit as BI};
        let eq_n = self.arena.name_from_path("Eq");
        if !self.decls.contains_key(&eq_n) {
            return Err(KernelError::UnknownConstant(eq_n));
        }
        let q_n = self.arena.name_from_path("Quot");
        let qmk_n = self.arena.name_from_path("Quot.mk");
        let qlift_n = self.arena.name_from_path("Quot.lift");
        let qind_n = self.arena.name_from_path("Quot.ind");
        if self.decls.contains_key(&q_n) {
            return Ok(());
        }
        let u = self.arena.name_from_path("u");
        let v = self.arena.name_from_path("v");
        let (lu, lv) = (self.arena.lvl_param(u), self.arena.lvl_param(v));
        let (su, sv, prop) = (self.arena.sort(lu), self.arena.sort(lv), self.arena.prop());
        let (b0, b1, b2, b3, b4) = (
            self.arena.bvar(0), self.arena.bvar(1), self.arena.bvar(2), self.arena.bvar(3), self.arena.bvar(4),
        );
        let q_u = self.arena.const_(q_n, [lu]);
        let qmk_u = self.arena.const_(qmk_n, [lu]);
        let eq_v = self.arena.const_(eq_n, [lv]);
        // Right-nested anonymous Pi types: pis([(bi, A), (bi', B)], C) = (A) -> (B) -> C.
        let pis = |a: &mut Arena, bs: &[(crate::arena::BinderInfo, ExprId)], body: ExprId| {
            bs.iter().rev().fold(body, |acc, &(bi, ty)| a.pi(Arena::ANONYMOUS, bi, ty, acc))
        };
        let r_ty = pis(&mut self.arena, &[(BD, b0), (BD, b1)], prop);
        // Quot.{u} : {α : Sort u} → (r : α → α → Prop) → Sort u
        let q_ty = pis(&mut self.arena, &[(BI, su), (BD, r_ty)], su);
        // Quot.mk.{u} : {α : Sort u} → (r : α → α → Prop) → α → Quot.{u} α r
        let ret = self.arena.app_n(q_u, &[b2, b1]);
        let qmk_ty = pis(&mut self.arena, &[(BI, su), (BD, r_ty), (BD, b1)], ret);
        // Quot.lift.{u,v} : {α : Sort u} → {r : α → α → Prop} → {β : Sort v} → (f : α → β)
        //   → (∀ a b, r a b → Eq.{v} β (f a) (f b)) → Quot.{u} α r → β
        // Under (α:#6, r:#5, β:#4, f:#3, a:#2, b:#1, _:#0): Eq.{v} β (f a) (f b)
        let (fa, fb) = (self.arena.app(b3, b2), self.arena.app(b3, b1));
        let eq_fafb = self.arena.app_n(eq_v, &[b4, fa, fb]);
        let rab = self.arena.app_n(b4, &[b1, b0]);
        let resp = pis(&mut self.arena, &[(BD, b3), (BD, b4), (BD, rab)], eq_fafb);
        let f_ty = pis(&mut self.arena, &[(BD, b2)], b1);
        let q_ar = self.arena.app_n(q_u, &[b4, b3]);
        let qlift_ty = pis(&mut self.arena, &[(BI, su), (BI, r_ty), (BI, sv), (BD, f_ty), (BD, resp), (BD, q_ar)], b3);
        // Quot.ind.{u} : {α : Sort u} → {r : α → α → Prop} → {β : Quot.{u} α r → Prop}
        //   → (∀ a, β (Quot.mk α r a)) → ∀ q, β q
        let q_ar_2 = self.arena.app_n(q_u, &[b1, b0]);
        let beta_ty = pis(&mut self.arena, &[(BD, q_ar_2)], prop);
        let mk_a = self.arena.app_n(qmk_u, &[b3, b2, b0]);
        let b_mka = self.arena.app(b1, mk_a);
        let all_a = pis(&mut self.arena, &[(BD, b2)], b_mka);
        let q_ar_4 = self.arena.app_n(q_u, &[b3, b2]);
        let bq = self.arena.app(b2, b0);
        let qind_ty = pis(&mut self.arena, &[(BI, su), (BI, r_ty), (BI, beta_ty), (BD, all_a), (BD, q_ar_4)], bq);

        let decls = [
            Declaration::Quot { name: q_n, level_params: Box::new([u]), ty: q_ty, kind: QuotKind::Type },
            Declaration::Quot { name: qmk_n, level_params: Box::new([u]), ty: qmk_ty, kind: QuotKind::Ctor },
            Declaration::Quot { name: qlift_n, level_params: Box::new([u, v]), ty: qlift_ty, kind: QuotKind::Lift },
            Declaration::Quot { name: qind_n, level_params: Box::new([u]), ty: qind_ty, kind: QuotKind::Ind },
        ];
        let mut inserted = Vec::with_capacity(4);
        for d in decls {
            let check = {
                let mut tc = TypeChecker::new(&self.decls, &mut self.arena);
                tc.check_decl(&d)
            };
            if let Err(e) = check {
                for n in inserted {
                    self.decls.remove(&n);
                }
                return Err(e);
            }
            let n = d.name();
            self.decls.insert(n, d);
            inserted.push(n);
        }
        Ok(())
    }

    /// Defer type-checking of axioms, definitions, theorems and opaques until
    /// [`Environment::check_deferred`], which checks them in parallel. Inductives and quotients
    /// are still checked immediately. The environment must not be trusted until
    /// `check_deferred` has returned `Ok`.
    pub fn set_deferred_checking(&mut self, on: bool) { self.defer = on; }

    fn require_known_consts(&self, e: ExprId) -> Result<(), KernelError> {
        let mut missing = None;
        any_subexpr(&self.arena, e, |_, _| false, |d| {
            let (ExprData::Const(n, _) | ExprData::Proj { struct_name: n, .. }) = d else { return false };
            if !self.decls.contains_key(n) { missing = Some(*n); }
            missing.is_some()
        });
        missing.map_or(Ok(()), |n| Err(KernelError::UnknownConstant(n)))
    }

    /// Type-check every deferred declaration on `threads` worker threads (each declaration in its
    /// own scratch arena over the shared, read-only environment). On failure returns the
    /// earliest failing declaration in admission order; the environment is then unusable.
    pub fn check_deferred(&mut self, threads: usize) -> Result<(), (NameId, KernelError)> {
        use std::sync::atomic::{AtomicUsize, Ordering};
        let pending = std::mem::take(&mut self.deferred);
        if pending.is_empty() { return Ok(()); }
        self.arena.shrink_for_sharing();
        let arena = Arc::new(std::mem::replace(&mut self.arena, Arena::new()));
        let decls = &self.decls;
        let next = AtomicUsize::new(0);
        let first_err: std::sync::Mutex<Option<(usize, NameId, KernelError)>> = std::sync::Mutex::new(None);
        let n_threads = threads.max(1).min(pending.len());
        std::thread::scope(|sc| {
            for _ in 0..n_threads {
                let (arena, pending, next, first_err) = (&arena, &pending, &next, &first_err);
                std::thread::Builder::new()
                    .stack_size(1 << 30)
                    .spawn_scoped(sc, move || loop {
                        let i = next.fetch_add(1, Ordering::Relaxed);
                        if i >= pending.len() { break; }
                        if let Some((j, _, _)) = *first_err.lock().unwrap() { if j < i { break; } }
                        let decl = &decls[&pending[i]];
                        let mut scratch = Arena::child(Arc::clone(arena));
                        let res = TypeChecker::new(decls, &mut scratch).check_decl(decl);
                        if let Err(e) = res {
                            let mut g = first_err.lock().unwrap();
                            if g.as_ref().is_none_or(|(j, _, _)| i < *j) { *g = Some((i, pending[i], e)); }
                        }
                    })
                    .expect("spawn checker thread");
            }
        });
        self.arena = Arc::try_unwrap(arena).unwrap_or_else(|_| unreachable!("worker arenas are dropped"));
        match first_err.into_inner().unwrap() {
            Some((_, name, e)) => Err((name, e)),
            None => Ok(()),
        }
    }

    /// Consume this environment and return its underlying arena and verified declarations.
    pub fn into_parts(self) -> (Arena, FxHashMap<NameId, Declaration>) {
        (self.arena, self.decls)
    }
}

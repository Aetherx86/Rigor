//! Global environment storing verified declarations and supporting lock-free parallel checking.

use std::sync::Arc;

use crate::arena::{Arena, ExprData, ExprId, NameId};
use crate::check::TypeChecker;
use crate::error::KernelError;
use crate::hash::{FxHashMap, FxHashSet};
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
    pub is_rec: bool, pub is_reflexive: bool, pub is_prop: bool, pub can_elim_large: bool,
}

#[derive(Debug, Clone)]
pub struct ConstructorInfo {
    pub name: NameId, pub ind_name: NameId, pub level_params: Box<[NameId]>,
    pub ty: ExprId, pub ctor_idx: u32, pub num_params: u32, pub num_fields: u32,
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

impl Declaration {
    #[inline]
    pub fn name(&self) -> NameId {
        match self {
            Declaration::Axiom { name, .. } | Declaration::Definition { name, .. }
            | Declaration::Theorem { name, .. } | Declaration::Opaque { name, .. }
            | Declaration::Quot { name, .. } => *name,
            Declaration::Inductive(i) => i.name,
            Declaration::Constructor(c) => c.name,
            Declaration::Recursor(r) => r.name,
        }
    }

    #[inline]
    pub fn level_params(&self) -> &[NameId] {
        match self {
            Declaration::Axiom { level_params, .. } | Declaration::Definition { level_params, .. }
            | Declaration::Theorem { level_params, .. } | Declaration::Opaque { level_params, .. }
            | Declaration::Quot { level_params, .. } => level_params,
            Declaration::Inductive(i) => &i.level_params,
            Declaration::Constructor(c) => &c.level_params,
            Declaration::Recursor(r) => &r.level_params,
        }
    }

    #[inline]
    pub fn ty(&self) -> ExprId {
        match self {
            Declaration::Axiom { ty, .. } | Declaration::Definition { ty, .. }
            | Declaration::Theorem { ty, .. } | Declaration::Opaque { ty, .. }
            | Declaration::Quot { ty, .. } => *ty,
            Declaration::Inductive(i) => i.ty,
            Declaration::Constructor(c) => c.ty,
            Declaration::Recursor(r) => r.ty,
        }
    }

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
    #[inline]
    pub fn is_empty(&self) -> bool { self.decls.is_empty() }

    /// Compute Lean 4-style definition height: `1 + max(height of referenced definitions)`.
    pub fn compute_height(&self, expr: ExprId) -> u32 {
        let mut visited = FxHashSet::default();
        self.max_height_rec(expr, &mut visited).saturating_add(1)
    }

    fn max_height_rec(&self, e: ExprId, visited: &mut FxHashSet<ExprId>) -> u32 {
        if !visited.insert(e) { return 0; }
        match self.arena.get_expr(e) {
            ExprData::Const(name, _) => match self.decls.get(name) {
                Some(Declaration::Definition { hint: ReducibilityHint::Regular(h), .. }) => *h,
                _ => 0,
            },
            ExprData::App(f, a) => self.max_height_rec(*f, visited).max(self.max_height_rec(*a, visited)),
            ExprData::Lam { ty, body, .. } | ExprData::Pi { ty, body, .. } => {
                self.max_height_rec(*ty, visited).max(self.max_height_rec(*body, visited))
            }
            ExprData::Let { ty, val, body, .. } => self
                .max_height_rec(*ty, visited)
                .max(self.max_height_rec(*val, visited))
                .max(self.max_height_rec(*body, visited)),
            ExprData::Proj { expr, .. } => self.max_height_rec(*expr, visited),
            ExprData::BVar(_) | ExprData::FVar(_) | ExprData::Sort(_) | ExprData::Lit(_) => 0,
        }
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
        let r_ty = {
            let inner = self.arena.pi(Arena::ANONYMOUS, BD, b1, prop);
            self.arena.pi(Arena::ANONYMOUS, BD, b0, inner)
        };

        // Quot.{u} : {α : Sort u} → (r : α → α → Prop) → Sort u
        let q_ty = {
            let p_r = self.arena.pi(Arena::ANONYMOUS, BD, r_ty, su);
            self.arena.pi(Arena::ANONYMOUS, BI, su, p_r)
        };
        // Quot.mk.{u} : {α : Sort u} → (r : α → α → Prop) → α → Quot.{u} α r
        let qmk_ty = {
            let ret = self.arena.app_n(q_u, &[b2, b1]);
            let p_a = self.arena.pi(Arena::ANONYMOUS, BD, b1, ret);
            let p_r = self.arena.pi(Arena::ANONYMOUS, BD, r_ty, p_a);
            self.arena.pi(Arena::ANONYMOUS, BI, su, p_r)
        };
        // Quot.lift.{u,v} : {α : Sort u} → {r : α → α → Prop} → {β : Sort v} → (f : α → β)
        //   → (∀ a b, r a b → Eq.{v} β (f a) (f b)) → Quot.{u} α r → β
        let qlift_ty = {
            let q_ar = self.arena.app_n(q_u, &[b4, b3]);
            let q_to_b = self.arena.pi(Arena::ANONYMOUS, BD, q_ar, b3);
            // Under (α:#6, r:#5, β:#4, f:#3, a:#2, b:#1, _:#0): Eq.{v} β (f a) (f b)
            let fa_s = self.arena.app(b3, b2);
            let fb_s = self.arena.app(b3, b1);
            let eq_fafb_s = self.arena.app_n(eq_v, &[b4, fa_s, fb_s]);
            let rab = self.arena.app_n(b4, &[b1, b0]);
            let h_pi = self.arena.pi(Arena::ANONYMOUS, BD, rab, eq_fafb_s);
            let b_pi = self.arena.pi(Arena::ANONYMOUS, BD, b4, h_pi);
            let a_pi = self.arena.pi(Arena::ANONYMOUS, BD, b3, b_pi);
            let f_ty = self.arena.pi(Arena::ANONYMOUS, BD, b2, b1);
            let p_h = self.arena.pi(Arena::ANONYMOUS, BD, a_pi, q_to_b);
            let p_f = self.arena.pi(Arena::ANONYMOUS, BD, f_ty, p_h);
            let p_b = self.arena.pi(Arena::ANONYMOUS, BI, sv, p_f);
            let p_r = self.arena.pi(Arena::ANONYMOUS, BI, r_ty, p_b);
            self.arena.pi(Arena::ANONYMOUS, BI, su, p_r)
        };
        // Quot.ind.{u} : {α : Sort u} → {r : α → α → Prop} → {β : Quot.{u} α r → Prop}
        //   → (∀ a, β (Quot.mk α r a)) → ∀ q, β q
        let qind_ty = {
            let q_ar_2 = self.arena.app_n(q_u, &[b1, b0]);
            let beta_ty = self.arena.pi(Arena::ANONYMOUS, BD, q_ar_2, prop);
            let q_ar_4 = self.arena.app_n(q_u, &[b3, b2]);
            let bq = self.arena.app(b2, b0);
            let all_q = self.arena.pi(Arena::ANONYMOUS, BD, q_ar_4, bq);
            let mk_a = self.arena.app_n(qmk_u, &[b3, b2, b0]);
            let b_mka = self.arena.app(b1, mk_a);
            let all_a = self.arena.pi(Arena::ANONYMOUS, BD, b2, b_mka);
            let p_h = self.arena.pi(Arena::ANONYMOUS, BD, all_a, all_q);
            let p_b = self.arena.pi(Arena::ANONYMOUS, BI, beta_ty, p_h);
            let p_r = self.arena.pi(Arena::ANONYMOUS, BI, r_ty, p_b);
            self.arena.pi(Arena::ANONYMOUS, BI, su, p_r)
        };

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

    /// Number of admitted declarations still waiting for `check_deferred`.
    pub fn deferred_len(&self) -> usize { self.deferred.len() }

    fn require_known_consts(&self, e: ExprId) -> Result<(), KernelError> {
        let mut stack = vec![e];
        let mut seen = FxHashSet::default();
        while let Some(x) = stack.pop() {
            if !seen.insert(x) { continue; }
            match self.arena.get_expr(x) {
                ExprData::Const(n, _) => if !self.decls.contains_key(n) { return Err(KernelError::UnknownConstant(*n)); },
                ExprData::App(f, a) => { stack.push(*f); stack.push(*a); }
                ExprData::Lam { ty, body, .. } | ExprData::Pi { ty, body, .. } => { stack.push(*ty); stack.push(*body); }
                ExprData::Let { ty, val, body, .. } => { stack.push(*ty); stack.push(*val); stack.push(*body); }
                ExprData::Proj { struct_name, expr, .. } => {
                    if !self.decls.contains_key(struct_name) { return Err(KernelError::UnknownConstant(*struct_name)); }
                    stack.push(*expr);
                }
                _ => {}
            }
        }
        Ok(())
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

    /// Freeze this environment into an immutable, lock-free shareable snapshot for parallel checking.
    pub fn freeze(self) -> FrozenEnv {
        FrozenEnv {
            arena: Arc::new(self.arena),
            decls: Arc::new(self.decls),
        }
    }
}

/// Immutable environment snapshot shareable across worker threads with zero locking.
#[derive(Debug, Clone)]
pub struct FrozenEnv {
    pub arena: Arc<Arena>,
    pub decls: Arc<FxHashMap<NameId, Declaration>>,
}

impl FrozenEnv {
    /// Verify a batch of independent declarations in parallel across `threads` OS threads,
    /// using an isolated thread-local scratch arena (`Arena::child`) per worker.
    pub fn check_batch_parallel(
        &self,
        decls: &[Declaration],
        threads: usize,
    ) -> Vec<Result<(), KernelError>> {
        if decls.is_empty() {
            return Vec::new();
        }
        let n_threads = threads.max(1).min(decls.len());
        if n_threads == 1 {
            let mut scratch = Arena::child(Arc::clone(&self.arena));
            return decls
                .iter()
                .map(|d| {
                    if self.decls.contains_key(&d.name()) {
                        return Err(KernelError::DuplicateDeclaration(d.name()));
                    }
                    let mut tc = TypeChecker::new(&self.decls, &mut scratch);
                    tc.check_decl(d)
                })
                .collect();
        }

        let chunk_size = decls.len().div_ceil(n_threads);
        let mut results: Vec<Result<(), KernelError>> = Vec::with_capacity(decls.len());
        std::thread::scope(|s| {
            let mut handles = Vec::with_capacity(n_threads);
            for chunk in decls.chunks(chunk_size) {
                let arena_ref = Arc::clone(&self.arena);
                let decls_ref = Arc::clone(&self.decls);
                handles.push(s.spawn(move || {
                    let mut scratch = Arena::child(arena_ref);
                    let mut out = Vec::with_capacity(chunk.len());
                    for d in chunk {
                        if decls_ref.contains_key(&d.name()) {
                            out.push(Err(KernelError::DuplicateDeclaration(d.name())));
                        } else {
                            let mut tc = TypeChecker::new(&decls_ref, &mut scratch);
                            out.push(tc.check_decl(d));
                        }
                    }
                    out
                }));
            }
            for h in handles {
                results.extend(h.join().expect("worker thread panicked"));
            }
        });
        results
    }
}

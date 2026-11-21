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
    pub name: NameId,
    pub level_params: Box<[NameId]>,
    pub ty: ExprId,
    pub num_params: u32,
    pub num_indices: u32,
    pub all: Box<[NameId]>,
    pub ctors: Box<[NameId]>,
    pub is_rec: bool,
    pub is_reflexive: bool,
    pub is_prop: bool,
    pub can_elim_large: bool,
}

#[derive(Debug, Clone)]
pub struct ConstructorInfo {
    pub name: NameId,
    pub ind_name: NameId,
    pub level_params: Box<[NameId]>,
    pub ty: ExprId,
    pub ctor_idx: u32,
    pub num_params: u32,
    pub num_fields: u32,
}

#[derive(Debug, Clone)]
pub struct RecursorRule {
    pub ctor_name: NameId,
    pub num_fields: u32,
    pub rhs: ExprId,
}

#[derive(Debug, Clone)]
pub struct RecursorInfo {
    pub name: NameId,
    pub level_params: Box<[NameId]>,
    pub ty: ExprId,
    pub all: Box<[NameId]>,
    pub num_params: u32,
    pub num_indices: u32,
    pub num_motives: u32,
    pub num_minors: u32,
    pub rules: Box<[RecursorRule]>,
    pub k: bool,
}

#[derive(Debug, Clone)]
pub enum Declaration {
    Axiom {
        name: NameId,
        level_params: Box<[NameId]>,
        ty: ExprId,
    },
    Definition {
        name: NameId,
        level_params: Box<[NameId]>,
        ty: ExprId,
        val: ExprId,
        hint: ReducibilityHint,
    },
    Theorem {
        name: NameId,
        level_params: Box<[NameId]>,
        ty: ExprId,
        val: ExprId,
    },
    Opaque {
        name: NameId,
        level_params: Box<[NameId]>,
        ty: ExprId,
        val: ExprId,
    },
    Inductive(InductiveInfo),
    Constructor(ConstructorInfo),
    Recursor(RecursorInfo),
}

impl Declaration {
    #[inline]
    pub fn name(&self) -> NameId {
        match self {
            Declaration::Axiom { name, .. }
            | Declaration::Definition { name, .. }
            | Declaration::Theorem { name, .. }
            | Declaration::Opaque { name, .. } => *name,
            Declaration::Inductive(i) => i.name,
            Declaration::Constructor(c) => c.name,
            Declaration::Recursor(r) => r.name,
        }
    }

    #[inline]
    pub fn level_params(&self) -> &[NameId] {
        match self {
            Declaration::Axiom { level_params, .. }
            | Declaration::Definition { level_params, .. }
            | Declaration::Theorem { level_params, .. }
            | Declaration::Opaque { level_params, .. } => level_params,
            Declaration::Inductive(i) => &i.level_params,
            Declaration::Constructor(c) => &c.level_params,
            Declaration::Recursor(r) => &r.level_params,
        }
    }

    #[inline]
    pub fn ty(&self) -> ExprId {
        match self {
            Declaration::Axiom { ty, .. }
            | Declaration::Definition { ty, .. }
            | Declaration::Theorem { ty, .. }
            | Declaration::Opaque { ty, .. } => *ty,
            Declaration::Inductive(i) => i.ty,
            Declaration::Constructor(c) => c.ty,
            Declaration::Recursor(r) => r.ty,
        }
    }

    /// Returns `(value, unfold_priority)` if this declaration is delta-reducible.
    #[inline]
    pub fn delta_value(&self) -> Option<(ExprId, u64)> {
        match self {
            Declaration::Definition { val, hint, .. } => match hint {
                ReducibilityHint::Opaque => None,
                ReducibilityHint::Abbrev => Some((*val, u64::MAX)),
                ReducibilityHint::Regular(h) => Some((*val, (*h as u64) + 1)),
            },
            Declaration::Theorem { val, .. } => Some((*val, 0)),
            Declaration::Axiom { .. }
            | Declaration::Opaque { .. }
            | Declaration::Inductive(_)
            | Declaration::Constructor(_)
            | Declaration::Recursor(_) => None,
        }
    }
}

/// Mutable environment used while sequentially building and verifying declarations.
#[derive(Debug, Default)]
pub struct Environment {
    pub arena: Arena,
    decls: FxHashMap<NameId, Declaration>,
}

impl Environment {
    pub fn new() -> Self {
        Self {
            arena: Arena::new(),
            decls: FxHashMap::default(),
        }
    }

    #[inline]
    pub fn get(&self, name: NameId) -> Option<&Declaration> {
        self.decls.get(&name)
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.decls.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.decls.is_empty()
    }

    /// Compute Lean 4-style definition height: `1 + max(height of referenced definitions)`.
    pub fn compute_height(&self, expr: ExprId) -> u32 {
        let mut visited = FxHashSet::default();
        let max_ref = self.max_height_rec(expr, &mut visited);
        max_ref.saturating_add(1)
    }

    fn max_height_rec(&self, e: ExprId, visited: &mut FxHashSet<ExprId>) -> u32 {
        if !visited.insert(e) {
            return 0;
        }
        match self.arena.get_expr(e) {
            ExprData::Const(name, _) => match self.decls.get(name) {
                Some(Declaration::Definition {
                    hint: ReducibilityHint::Regular(h),
                    ..
                }) => *h,
                _ => 0,
            },
            ExprData::App(f, a) => self
                .max_height_rec(*f, visited)
                .max(self.max_height_rec(*a, visited)),
            ExprData::Lam { ty, body, .. } | ExprData::Pi { ty, body, .. } => self
                .max_height_rec(*ty, visited)
                .max(self.max_height_rec(*body, visited)),
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
        if self.decls.contains_key(&name) {
            return Err(KernelError::DuplicateDeclaration(name));
        }
        // Auto-compute height for Regular(0) definitions.
        if let Declaration::Definition {
            val,
            hint: hint @ ReducibilityHint::Regular(0),
            ..
        } = &mut decl
        {
            *hint = ReducibilityHint::Regular(self.compute_height(*val));
        }
        {
            let mut tc = TypeChecker::new(&self.decls, &mut self.arena);
            tc.check_decl(&decl)?;
        }
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

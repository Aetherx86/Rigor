//! Post-verification axiom footprint auditing and declaration inspection.
//!
//! Computes exact transitive axiom dependencies across an already-verified [`Environment`]
//! (analogous to Lean 4's `#print axioms`), classifies standard vs non-standard/unsound axioms,
//! and enforces allowlist / `forbid_sorry` verification policies.

use std::collections::{HashMap, HashSet, VecDeque};

use rigor_kernel::{Arena, Declaration, Environment, ExprData, ExprId, NameId};

use crate::pretty::{format_expr, format_name};

/// Lean 4's three standard classical axioms.
pub const STANDARD_AXIOMS: &[&str] = &["propext", "Quot.sound", "Classical.choice"];

/// Well-known axiom names indicating incomplete proofs (`sorryAx`) or compiler trust extensions.
pub const TRUST_EXTENDING_AXIOMS: &[&str] = &["sorryAx", "Lean.ofReduceBool", "Lean.trustCompiler"];

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum DeclKind {
    Axiom,
    Definition,
    Theorem,
    Opaque,
    Inductive,
    Constructor,
    Recursor,
    Quot,
}

impl DeclKind {
    pub fn as_str(self) -> &'static str {
        match self {
            DeclKind::Axiom => "axiom",
            DeclKind::Definition => "def",
            DeclKind::Theorem => "theorem",
            DeclKind::Opaque => "opaque",
            DeclKind::Inductive => "inductive",
            DeclKind::Constructor => "constructor",
            DeclKind::Recursor => "recursor",
            DeclKind::Quot => "quot",
        }
    }
}

/// Detailed inspection of a single verified declaration and its transitive axiom footprint.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DeclInspection {
    pub name: String,
    pub kind: DeclKind,
    pub level_params: Vec<String>,
    pub ty: String,
    pub direct_deps: Vec<String>,
    pub axioms: Vec<String>,
    pub non_standard_axioms: Vec<String>,
    pub uses_sorry: bool,
    pub uses_quot: bool,
}

/// Usage summary for a single declared axiom across the entire environment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AxiomUsage {
    pub name: String,
    pub is_standard: bool,
    pub is_sorry: bool,
    pub is_trust_extending: bool,
    pub dependent_decls: usize,
    pub dependent_theorems: usize,
}

/// Whole-environment axiom audit summary.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AuditReport {
    pub total_env_decls: usize,
    pub theorems: usize,
    pub axioms: Vec<AxiomUsage>,
    pub non_standard_axioms: Vec<String>,
    pub sorry_theorems: Vec<String>,
    pub uses_quot: bool,
}

/// Policy enforced after kernel verification succeeds.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct AxiomPolicy {
    /// If `Some`, every axiom declared/used in scope must appear in this allowlist.
    pub allow_axioms: Option<Vec<String>>,
    /// If `true`, reject `sorryAx` (whether declared or depended upon).
    pub forbid_sorry: bool,
}

/// One violation reported by [`check_axiom_policy`] or [`check_decl_policy`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PolicyViolation {
    pub decl: Option<String>,
    pub axiom: String,
    pub reason: String,
}

/// Returns true if `name` is one of Lean 4's three standard classical axioms.
pub fn is_standard_axiom(name: &str) -> bool {
    STANDARD_AXIOMS.contains(&name)
}

/// Returns true if `name` is Lean's `sorryAx` (or a namespaced suffix `.sorryAx`).
pub fn is_sorry_axiom(name: &str) -> bool {
    name == "sorryAx" || name.ends_with(".sorryAx")
}

/// Returns true if `name` is a known incomplete-proof or compiler-trust axiom.
pub fn is_trust_extending_axiom(name: &str) -> bool {
    is_sorry_axiom(name) || TRUST_EXTENDING_AXIOMS.contains(&name)
}

/// Look up a declaration's [`NameId`] by its dotted Lean name (without mutating `env`).
pub fn lookup_name(env: &Environment, dotted: &str) -> Option<NameId> {
    env.decls()
        .keys()
        .copied()
        .find(|&id| format_name(&env.arena, id) == dotted)
}

fn decl_kind(decl: &Declaration) -> DeclKind {
    match decl {
        Declaration::Axiom { .. } => DeclKind::Axiom,
        Declaration::Definition { .. } => DeclKind::Definition,
        Declaration::Theorem { .. } => DeclKind::Theorem,
        Declaration::Opaque { .. } => DeclKind::Opaque,
        Declaration::Inductive(_) => DeclKind::Inductive,
        Declaration::Constructor(_) => DeclKind::Constructor,
        Declaration::Recursor(_) => DeclKind::Recursor,
        Declaration::Quot { .. } => DeclKind::Quot,
    }
}

/// Collect all constant names referenced directly by expression `e` (DAG-memoized via `seen_exprs`).
fn collect_expr_consts(
    arena: &Arena,
    root: ExprId,
    seen_exprs: &mut HashSet<ExprId>,
    out: &mut HashSet<NameId>,
) {
    let mut stack = vec![root];
    while let Some(e) = stack.pop() {
        if !seen_exprs.insert(e) {
            continue;
        }
        match *arena.get_expr(e) {
            ExprData::Const(n, _) => {
                out.insert(n);
            }
            ExprData::Proj {
                struct_name, expr, ..
            } => {
                out.insert(struct_name);
                stack.push(expr);
            }
            ExprData::App(f, a) => {
                stack.push(f);
                stack.push(a);
            }
            ExprData::Lam { ty, body, .. } | ExprData::Pi { ty, body, .. } => {
                stack.push(ty);
                stack.push(body);
            }
            ExprData::Let { ty, val, body } => {
                stack.push(ty);
                stack.push(val);
                stack.push(body);
            }
            ExprData::BVar(_) | ExprData::FVar(_) | ExprData::Sort(_) | ExprData::Lit(_) => {}
        }
    }
}

/// Collect direct constant dependencies of `decl` (both type and value/rules/ctors).
fn direct_decl_deps(
    arena: &Arena,
    decl: &Declaration,
    seen_exprs: &mut HashSet<ExprId>,
) -> HashSet<NameId> {
    let mut deps = HashSet::new();
    match decl {
        Declaration::Axiom { ty, .. } | Declaration::Quot { ty, .. } => {
            collect_expr_consts(arena, *ty, seen_exprs, &mut deps);
        }
        Declaration::Definition { ty, val, .. }
        | Declaration::Theorem { ty, val, .. }
        | Declaration::Opaque { ty, val, .. } => {
            collect_expr_consts(arena, *ty, seen_exprs, &mut deps);
            collect_expr_consts(arena, *val, seen_exprs, &mut deps);
        }
        Declaration::Inductive(info) => {
            collect_expr_consts(arena, info.ty, seen_exprs, &mut deps);
            for &c in info.ctors.iter() {
                deps.insert(c);
            }
            for &m in info.all.iter() {
                deps.insert(m);
            }
        }
        Declaration::Constructor(info) => {
            collect_expr_consts(arena, info.ty, seen_exprs, &mut deps);
            deps.insert(info.ind_name);
        }
        Declaration::Recursor(info) => {
            collect_expr_consts(arena, info.ty, seen_exprs, &mut deps);
            for &m in info.all.iter() {
                deps.insert(m);
            }
            for r in info.rules.iter() {
                deps.insert(r.ctor_name);
                collect_expr_consts(arena, r.rhs, seen_exprs, &mut deps);
            }
        }
    }
    deps.remove(&decl.name());
    deps
}

/// Inspect a single declaration and compute its exact transitive axiom footprint.
pub fn inspect_decl(env: &Environment, target: NameId) -> Option<DeclInspection> {
    let root_decl = env.get(target)?;
    let mut direct_seen_exprs = HashSet::new();
    let direct_ids = direct_decl_deps(&env.arena, root_decl, &mut direct_seen_exprs);
    let mut direct_deps: Vec<String> = direct_ids
        .iter()
        .map(|&id| format_name(&env.arena, id))
        .collect();
    direct_deps.sort();

    // Iterative DFS over the transitive declaration graph; `seen_exprs` is shared globally so
    // shared DAG subexpressions across declarations are walked at most once.
    let mut visited_decls = HashSet::new();
    let mut seen_exprs = HashSet::new();
    let mut worklist = vec![target];
    let mut axioms = Vec::new();
    let mut uses_quot = false;

    while let Some(cur) = worklist.pop() {
        if !visited_decls.insert(cur) {
            continue;
        }
        let Some(d) = env.get(cur) else {
            continue;
        };
        match d {
            Declaration::Axiom { .. } => {
                axioms.push(format_name(&env.arena, cur));
            }
            Declaration::Quot { .. } => {
                uses_quot = true;
            }
            _ => {}
        }
        let deps = direct_decl_deps(&env.arena, d, &mut seen_exprs);
        for dep in deps {
            if !visited_decls.contains(&dep) {
                worklist.push(dep);
            }
        }
    }

    axioms.sort();
    axioms.dedup();
    let non_standard_axioms: Vec<String> = axioms
        .iter()
        .filter(|a| !is_standard_axiom(a))
        .cloned()
        .collect();
    let uses_sorry = axioms.iter().any(|a| is_sorry_axiom(a));
    let level_params = root_decl
        .level_params()
        .iter()
        .map(|&p| format_name(&env.arena, p))
        .collect();

    Some(DeclInspection {
        name: format_name(&env.arena, target),
        kind: decl_kind(root_decl),
        level_params,
        ty: format_expr(&env.arena, root_decl.ty()),
        direct_deps,
        axioms,
        non_standard_axioms,
        uses_sorry,
        uses_quot,
    })
}

/// Audit the entire verified environment using reverse-BFS from each declared axiom.
/// Runs in `O(|axioms| * (|V| + |E|))` without recursion.
pub fn audit_environment(env: &Environment) -> AuditReport {
    let decls = env.decls();
    let mut rev_deps: HashMap<NameId, Vec<NameId>> = HashMap::with_capacity(decls.len());
    let mut axiom_ids: Vec<NameId> = Vec::new();
    let mut theorems = 0usize;
    let mut uses_quot = false;
    let mut seen_exprs = HashSet::new();

    for (&name, decl) in decls.iter() {
        match decl {
            Declaration::Axiom { .. } => axiom_ids.push(name),
            Declaration::Theorem { .. } => theorems += 1,
            Declaration::Quot { .. } => uses_quot = true,
            _ => {}
        }
        seen_exprs.clear();
        for dep in direct_decl_deps(&env.arena, decl, &mut seen_exprs) {
            rev_deps.entry(dep).or_default().push(name);
        }
    }

    let mut axioms = Vec::with_capacity(axiom_ids.len());
    let mut sorry_theorems = Vec::new();
    let mut sorry_thm_set = HashSet::new();

    for ax_id in axiom_ids {
        let ax_name = format_name(&env.arena, ax_id);
        let is_std = is_standard_axiom(&ax_name);
        let is_sorry = is_sorry_axiom(&ax_name);
        let is_trust = is_trust_extending_axiom(&ax_name);

        let mut visited: HashSet<NameId> = HashSet::new();
        let mut queue = VecDeque::new();
        visited.insert(ax_id);
        queue.push_back(ax_id);

        let mut dep_decls = 0usize;
        let mut dep_thms = 0usize;

        while let Some(cur) = queue.pop_front() {
            if cur != ax_id {
                dep_decls += 1;
                if matches!(decls.get(&cur), Some(Declaration::Theorem { .. })) {
                    dep_thms += 1;
                    if is_sorry && sorry_thm_set.insert(cur) {
                        sorry_theorems.push(format_name(&env.arena, cur));
                    }
                }
            }
            if let Some(parents) = rev_deps.get(&cur) {
                for &p in parents {
                    if visited.insert(p) {
                        queue.push_back(p);
                    }
                }
            }
        }

        axioms.push(AxiomUsage {
            name: ax_name,
            is_standard: is_std,
            is_sorry,
            is_trust_extending: is_trust,
            dependent_decls: dep_decls,
            dependent_theorems: dep_thms,
        });
    }

    axioms.sort_by(|a, b| a.name.cmp(&b.name));
    sorry_theorems.sort();
    let non_standard_axioms = axioms
        .iter()
        .filter(|a| !a.is_standard)
        .map(|a| a.name.clone())
        .collect();

    AuditReport {
        total_env_decls: decls.len(),
        theorems,
        axioms,
        non_standard_axioms,
        sorry_theorems,
        uses_quot,
    }
}

/// Evaluate an [`AxiomPolicy`] against a whole-environment [`AuditReport`].
///
/// Unused axiom declarations (such as `sorryAx` declared in Lean's `Init.Prelude` with zero
/// dependents) do not trigger violations; any axiom with `dependent_decls > 0` is enforced.
pub fn check_axiom_policy(report: &AuditReport, policy: &AxiomPolicy) -> Vec<PolicyViolation> {
    let mut violations = Vec::new();
    for ax in &report.axioms {
        if ax.dependent_decls == 0 {
            continue;
        }
        if policy.forbid_sorry && ax.is_sorry {
            violations.push(PolicyViolation {
                decl: None,
                axiom: ax.name.clone(),
                reason: format!(
                    "sorry axiom '{}' is forbidden (used by {} decl(s), {} theorem(s))",
                    ax.name, ax.dependent_decls, ax.dependent_theorems
                ),
            });
        }
        if let Some(allowed) = &policy.allow_axioms {
            if !allowed.iter().any(|a| a == &ax.name) {
                violations.push(PolicyViolation {
                    decl: None,
                    axiom: ax.name.clone(),
                    reason: format!(
                        "axiom '{}' is not in the allowed axiom list (used by {} decl(s))",
                        ax.name, ax.dependent_decls
                    ),
                });
            }
        }
    }
    violations
}

/// Evaluate an [`AxiomPolicy`] against a single declaration's [`DeclInspection`].
pub fn check_decl_policy(
    inspection: &DeclInspection,
    policy: &AxiomPolicy,
) -> Vec<PolicyViolation> {
    let mut violations = Vec::new();
    for ax in &inspection.axioms {
        if policy.forbid_sorry && is_sorry_axiom(ax) {
            violations.push(PolicyViolation {
                decl: Some(inspection.name.clone()),
                axiom: ax.clone(),
                reason: format!(
                    "declaration '{}' transitively depends on forbidden sorry axiom '{}'",
                    inspection.name, ax
                ),
            });
        }
        if let Some(allowed) = &policy.allow_axioms {
            if !allowed.iter().any(|a| a == ax) {
                violations.push(PolicyViolation {
                    decl: Some(inspection.name.clone()),
                    axiom: ax.clone(),
                    reason: format!(
                        "declaration '{}' depends on disallowed axiom '{}'",
                        inspection.name, ax
                    ),
                });
            }
        }
    }
    violations
}

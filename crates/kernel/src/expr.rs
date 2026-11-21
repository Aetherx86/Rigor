//! Compact DAG-preserving expression operations (substitution, abstraction, universe instantiation).

use crate::arena::{Arena, ExprData, ExprId, FVarId, LevelId, NameId};
use crate::error::KernelError;
use crate::hash::{FxHashMap, FxHashSet};
use crate::level::{level_check_params, level_instantiate};

#[inline]
pub fn instantiate1(arena: &mut Arena, e: ExprId, val: ExprId) -> ExprId {
    instantiate_rev(arena, e, &[val])
}

/// Simultaneous spine-order substitution: `args[0]` replaces `BVar(n-1)`, `args[n-1]` replaces `BVar(0)`.
pub fn instantiate_rev(arena: &mut Arena, e: ExprId, args: &[ExprId]) -> ExprId {
    if args.is_empty() || arena.get_expr_meta(e).is_closed() {
        return e;
    }
    let mut cache = FxHashMap::default();
    map_children(arena, e, 0, &mut cache, &mut |a, node, off| {
        if a.get_expr_meta(node).loose_bvar_range <= off {
            return Some(node);
        }
        if let ExprData::BVar(idx) = a.get_expr(node) {
            let idx = *idx;
            let n = args.len() as u32;
            return Some(if idx < off {
                node
            } else if idx < off + n {
                args[(n - 1 - (idx - off)) as usize]
            } else {
                a.bvar(idx - n)
            });
        }
        None
    })
}

/// Abstract free variables `fvars` (outermost to innermost) into `BVar(n-1 ..= 0)`.
pub fn abstract_fvars(arena: &mut Arena, e: ExprId, fvars: &[FVarId]) -> ExprId {
    if fvars.is_empty() || !arena.get_expr_meta(e).has_fvar() {
        return e;
    }
    let mut cache = FxHashMap::default();
    let n = fvars.len();
    map_children(arena, e, 0, &mut cache, &mut |a, node, off| {
        if !a.get_expr_meta(node).has_fvar() {
            return Some(node);
        }
        if let ExprData::FVar(fv) = a.get_expr(node) {
            return Some(if let Some(pos) = fvars.iter().rposition(|&x| x == *fv) {
                a.bvar(off + (n - 1 - pos) as u32)
            } else {
                node
            });
        }
        None
    })
}

/// Instantiate universe level parameters `params -> args` throughout an expression DAG.
pub fn instantiate_level_params(
    arena: &mut Arena,
    e: ExprId,
    params: &[NameId],
    args: &[LevelId],
) -> ExprId {
    if params.is_empty() || !arena.get_expr_meta(e).has_level_param() {
        return e;
    }
    let mut cache = FxHashMap::default();
    map_children(arena, e, 0, &mut cache, &mut |a, node, _off| {
        if !a.get_expr_meta(node).has_level_param() {
            return Some(node);
        }
        match a.get_expr(node).clone() {
            ExprData::Sort(l) => {
                let l2 = level_instantiate(a, l, params, args);
                Some(if l2 == l { node } else { a.sort(l2) })
            }
            ExprData::Const(name, lvls) => {
                let mut changed = false;
                let out: Vec<LevelId> = lvls
                    .iter()
                    .map(|&l| {
                        let l2 = level_instantiate(a, l, params, args);
                        if l2 != l {
                            changed = true;
                        }
                        l2
                    })
                    .collect();
                Some(if changed { a.const_(name, out) } else { node })
            }
            _ => None,
        }
    })
}

fn map_children<F>(
    arena: &mut Arena,
    e: ExprId,
    off: u32,
    cache: &mut FxHashMap<(ExprId, u32), ExprId>,
    leaf: &mut F,
) -> ExprId
where
    F: FnMut(&mut Arena, ExprId, u32) -> Option<ExprId>,
{
    if let Some(res) = leaf(arena, e, off) {
        return res;
    }
    if let Some(&res) = cache.get(&(e, off)) {
        return res;
    }
    let res = match arena.get_expr(e).clone() {
        ExprData::App(f, a) => {
            let f2 = map_children(arena, f, off, cache, leaf);
            let a2 = map_children(arena, a, off, cache, leaf);
            if f2 == f && a2 == a { e } else { arena.app(f2, a2) }
        }
        ExprData::Lam { name, binder_info, ty, body } => {
            let ty2 = map_children(arena, ty, off, cache, leaf);
            let b2 = map_children(arena, body, off + 1, cache, leaf);
            if ty2 == ty && b2 == body { e } else { arena.lam(name, binder_info, ty2, b2) }
        }
        ExprData::Pi { name, binder_info, ty, body } => {
            let ty2 = map_children(arena, ty, off, cache, leaf);
            let b2 = map_children(arena, body, off + 1, cache, leaf);
            if ty2 == ty && b2 == body { e } else { arena.pi(name, binder_info, ty2, b2) }
        }
        ExprData::Let { name, ty, val, body } => {
            let ty2 = map_children(arena, ty, off, cache, leaf);
            let v2 = map_children(arena, val, off, cache, leaf);
            let b2 = map_children(arena, body, off + 1, cache, leaf);
            if ty2 == ty && v2 == val && b2 == body { e } else { arena.let_(name, ty2, v2, b2) }
        }
        ExprData::Proj { struct_name, idx, expr } => {
            let x2 = map_children(arena, expr, off, cache, leaf);
            if x2 == expr { e } else { arena.proj(struct_name, idx, x2) }
        }
        ExprData::BVar(_) | ExprData::FVar(_) | ExprData::Sort(_) | ExprData::Const(_, _) | ExprData::Lit(_) => e,
    };
    cache.insert((e, off), res);
    res
}

/// True if `e` mentions any constant whose name is in `targets` (DAG-memoized).
pub fn expr_mentions_any_const(arena: &Arena, e: ExprId, targets: &[NameId]) -> bool {
    let mut visited = FxHashSet::default();
    mentions_rec(arena, e, targets, &mut visited)
}

fn mentions_rec(arena: &Arena, e: ExprId, targets: &[NameId], visited: &mut FxHashSet<ExprId>) -> bool {
    if !visited.insert(e) {
        return false;
    }
    match arena.get_expr(e) {
        ExprData::Const(name, _) => targets.contains(name),
        ExprData::App(f, a) => mentions_rec(arena, *f, targets, visited) || mentions_rec(arena, *a, targets, visited),
        ExprData::Lam { ty, body, .. } | ExprData::Pi { ty, body, .. } => {
            mentions_rec(arena, *ty, targets, visited) || mentions_rec(arena, *body, targets, visited)
        }
        ExprData::Let { ty, val, body, .. } => {
            mentions_rec(arena, *ty, targets, visited)
                || mentions_rec(arena, *val, targets, visited)
                || mentions_rec(arena, *body, targets, visited)
        }
        ExprData::Proj { struct_name, expr, .. } => {
            targets.contains(struct_name) || mentions_rec(arena, *expr, targets, visited)
        }
        ExprData::BVar(_) | ExprData::FVar(_) | ExprData::Sort(_) | ExprData::Lit(_) => false,
    }
}

/// True if `e` mentions `fvar` anywhere (O(1) skip when `!has_fvar`).
pub fn expr_mentions_fvar(arena: &Arena, e: ExprId, fvar: FVarId) -> bool {
    if !arena.get_expr_meta(e).has_fvar() {
        return false;
    }
    let mut visited = FxHashSet::default();
    mentions_fvar_rec(arena, e, fvar, &mut visited)
}

fn mentions_fvar_rec(arena: &Arena, e: ExprId, fvar: FVarId, visited: &mut FxHashSet<ExprId>) -> bool {
    if !arena.get_expr_meta(e).has_fvar() || !visited.insert(e) {
        return false;
    }
    match arena.get_expr(e) {
        ExprData::FVar(id) => *id == fvar,
        ExprData::App(f, a) => {
            mentions_fvar_rec(arena, *f, fvar, visited) || mentions_fvar_rec(arena, *a, fvar, visited)
        }
        ExprData::Lam { ty, body, .. } | ExprData::Pi { ty, body, .. } => {
            mentions_fvar_rec(arena, *ty, fvar, visited) || mentions_fvar_rec(arena, *body, fvar, visited)
        }
        ExprData::Let { ty, val, body, .. } => {
            mentions_fvar_rec(arena, *ty, fvar, visited)
                || mentions_fvar_rec(arena, *val, fvar, visited)
                || mentions_fvar_rec(arena, *body, fvar, visited)
        }
        ExprData::Proj { expr, .. } => mentions_fvar_rec(arena, *expr, fvar, visited),
        ExprData::BVar(_) | ExprData::Sort(_) | ExprData::Const(_, _) | ExprData::Lit(_) => false,
    }
}

/// Verify that every universe parameter in `e` is declared in `allowed` (DAG-memoized).
pub fn expr_check_level_params(arena: &Arena, e: ExprId, allowed: &[NameId]) -> Result<(), KernelError> {
    if !arena.get_expr_meta(e).has_level_param() {
        return Ok(());
    }
    let mut visited = FxHashSet::default();
    check_lvl_rec(arena, e, allowed, &mut visited)
}

fn check_lvl_rec(
    arena: &Arena,
    e: ExprId,
    allowed: &[NameId],
    visited: &mut FxHashSet<ExprId>,
) -> Result<(), KernelError> {
    if !arena.get_expr_meta(e).has_level_param() || !visited.insert(e) {
        return Ok(());
    }
    match arena.get_expr(e) {
        ExprData::Sort(l) => level_check_params(arena, *l, allowed),
        ExprData::Const(_, lvls) => {
            for &l in lvls.iter() {
                level_check_params(arena, l, allowed)?;
            }
            Ok(())
        }
        ExprData::App(f, a) => {
            check_lvl_rec(arena, *f, allowed, visited)?;
            check_lvl_rec(arena, *a, allowed, visited)
        }
        ExprData::Lam { ty, body, .. } | ExprData::Pi { ty, body, .. } => {
            check_lvl_rec(arena, *ty, allowed, visited)?;
            check_lvl_rec(arena, *body, allowed, visited)
        }
        ExprData::Let { ty, val, body, .. } => {
            check_lvl_rec(arena, *ty, allowed, visited)?;
            check_lvl_rec(arena, *val, allowed, visited)?;
            check_lvl_rec(arena, *body, allowed, visited)
        }
        ExprData::Proj { expr, .. } => check_lvl_rec(arena, *expr, allowed, visited),
        ExprData::BVar(_) | ExprData::FVar(_) | ExprData::Lit(_) => Ok(()),
    }
}

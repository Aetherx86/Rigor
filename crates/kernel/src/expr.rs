//! DAG-preserving expression operations: simultaneous multi-substitution (`instantiate_rev`),
//! fvar abstraction (`abstract_fvar`), universe parameter instantiation, and scope checks.
//!
//! All traversals skip closed/parameter-free sub-DAGs in O(1) using `ExprMeta` and memoize
//! visited nodes so diamond-shared DAGs stay linear in DAG size.

use crate::arena::{Arena, ExprData, ExprId, FVarId, LevelId, NameId};
use crate::error::KernelError;
use crate::hash::FxHashMap;
use crate::level::{level_check_params, level_instantiate};

/// Substitute a single closed term `val` for `BVar(0)` in `e`.
#[inline]
pub fn instantiate1(arena: &mut Arena, e: ExprId, val: ExprId) -> ExprId {
    instantiate_rev(arena, e, &[val])
}

/// Simultaneous multi-substitution matching spine order:
/// for `args = [a_0, a_1, ..., a_{n-1}]` (outermost to innermost), replaces
/// `BVar(n - 1)` with `a_0`, ..., `BVar(0)` with `a_{n-1}`, and shifts higher `BVar`s down by `n`.
///
/// Precondition: every `a_i` is closed (`loose_bvar_range == 0`), which holds for all kernel
/// values (local variables use `FVar`, never loose `BVar`).
pub fn instantiate_rev(arena: &mut Arena, e: ExprId, args: &[ExprId]) -> ExprId {
    let n = args.len() as u32;
    if n == 0 || arena.get_expr_meta(e).is_closed() {
        return e;
    }
    let mut cache: FxHashMap<(ExprId, u32), ExprId> = FxHashMap::default();
    inst_rec(arena, e, 0, args, &mut cache)
}

fn inst_rec(
    arena: &mut Arena,
    e: ExprId,
    offset: u32,
    args: &[ExprId],
    cache: &mut FxHashMap<(ExprId, u32), ExprId>,
) -> ExprId {
    let meta = arena.get_expr_meta(e);
    if meta.loose_bvar_range <= offset {
        return e;
    }
    if let Some(&res) = cache.get(&(e, offset)) {
        return res;
    }
    let n = args.len() as u32;
    let res = match arena.get_expr(e).clone() {
        ExprData::BVar(idx) => {
            if idx < offset {
                e
            } else if idx < offset + n {
                // Reverse mapping: idx == offset -> last arg; idx == offset + n - 1 -> first arg.
                args[(n - 1 - (idx - offset)) as usize]
            } else {
                arena.bvar(idx - n)
            }
        }
        ExprData::App(f, a) => {
            let f2 = inst_rec(arena, f, offset, args, cache);
            let a2 = inst_rec(arena, a, offset, args, cache);
            if f2 == f && a2 == a {
                e
            } else {
                arena.app(f2, a2)
            }
        }
        ExprData::Lam {
            name,
            binder_info,
            ty,
            body,
        } => {
            let ty2 = inst_rec(arena, ty, offset, args, cache);
            let body2 = inst_rec(arena, body, offset + 1, args, cache);
            if ty2 == ty && body2 == body {
                e
            } else {
                arena.lam(name, binder_info, ty2, body2)
            }
        }
        ExprData::Pi {
            name,
            binder_info,
            ty,
            body,
        } => {
            let ty2 = inst_rec(arena, ty, offset, args, cache);
            let body2 = inst_rec(arena, body, offset + 1, args, cache);
            if ty2 == ty && body2 == body {
                e
            } else {
                arena.pi(name, binder_info, ty2, body2)
            }
        }
        ExprData::Let {
            name,
            ty,
            val,
            body,
        } => {
            let ty2 = inst_rec(arena, ty, offset, args, cache);
            let val2 = inst_rec(arena, val, offset, args, cache);
            let body2 = inst_rec(arena, body, offset + 1, args, cache);
            if ty2 == ty && val2 == val && body2 == body {
                e
            } else {
                arena.let_(name, ty2, val2, body2)
            }
        }
        ExprData::Proj {
            struct_name,
            idx,
            expr,
        } => {
            let expr2 = inst_rec(arena, expr, offset, args, cache);
            if expr2 == expr {
                e
            } else {
                arena.intern_expr(ExprData::Proj {
                    struct_name,
                    idx,
                    expr: expr2,
                })
            }
        }
        ExprData::FVar(_) | ExprData::Sort(_) | ExprData::Const(_, _) | ExprData::Lit(_) => e,
    };
    cache.insert((e, offset), res);
    res
}

/// Abstract a list of free variables `fvars` (outermost to innermost) into de Bruijn indices
/// `BVar(fvars.len() - 1 ..= 0)` in `e`.
pub fn abstract_fvars(arena: &mut Arena, e: ExprId, fvars: &[FVarId]) -> ExprId {
    if fvars.is_empty() || !arena.get_expr_meta(e).has_fvar() {
        return e;
    }
    let mut cache: FxHashMap<(ExprId, u32), ExprId> = FxHashMap::default();
    abs_rec(arena, e, 0, fvars, &mut cache)
}

fn abs_rec(
    arena: &mut Arena,
    e: ExprId,
    offset: u32,
    fvars: &[FVarId],
    cache: &mut FxHashMap<(ExprId, u32), ExprId>,
) -> ExprId {
    if !arena.get_expr_meta(e).has_fvar() {
        return e;
    }
    if let Some(&res) = cache.get(&(e, offset)) {
        return res;
    }
    let n = fvars.len();
    let res = match arena.get_expr(e).clone() {
        ExprData::FVar(fv) => {
            if let Some(pos) = fvars.iter().rposition(|&x| x == fv) {
                arena.bvar(offset + (n - 1 - pos) as u32)
            } else {
                e
            }
        }
        ExprData::App(f, a) => {
            let f2 = abs_rec(arena, f, offset, fvars, cache);
            let a2 = abs_rec(arena, a, offset, fvars, cache);
            if f2 == f && a2 == a {
                e
            } else {
                arena.app(f2, a2)
            }
        }
        ExprData::Lam {
            name,
            binder_info,
            ty,
            body,
        } => {
            let ty2 = abs_rec(arena, ty, offset, fvars, cache);
            let body2 = abs_rec(arena, body, offset + 1, fvars, cache);
            if ty2 == ty && body2 == body {
                e
            } else {
                arena.lam(name, binder_info, ty2, body2)
            }
        }
        ExprData::Pi {
            name,
            binder_info,
            ty,
            body,
        } => {
            let ty2 = abs_rec(arena, ty, offset, fvars, cache);
            let body2 = abs_rec(arena, body, offset + 1, fvars, cache);
            if ty2 == ty && body2 == body {
                e
            } else {
                arena.pi(name, binder_info, ty2, body2)
            }
        }
        ExprData::Let {
            name,
            ty,
            val,
            body,
        } => {
            let ty2 = abs_rec(arena, ty, offset, fvars, cache);
            let val2 = abs_rec(arena, val, offset, fvars, cache);
            let body2 = abs_rec(arena, body, offset + 1, fvars, cache);
            if ty2 == ty && val2 == val && body2 == body {
                e
            } else {
                arena.let_(name, ty2, val2, body2)
            }
        }
        ExprData::Proj {
            struct_name,
            idx,
            expr,
        } => {
            let expr2 = abs_rec(arena, expr, offset, fvars, cache);
            if expr2 == expr {
                e
            } else {
                arena.intern_expr(ExprData::Proj {
                    struct_name,
                    idx,
                    expr: expr2,
                })
            }
        }
        ExprData::BVar(_) | ExprData::Sort(_) | ExprData::Const(_, _) | ExprData::Lit(_) => e,
    };
    cache.insert((e, offset), res);
    res
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
    let mut cache: FxHashMap<ExprId, ExprId> = FxHashMap::default();
    inst_lvl_rec(arena, e, params, args, &mut cache)
}

fn inst_lvl_rec(
    arena: &mut Arena,
    e: ExprId,
    params: &[NameId],
    args: &[LevelId],
    cache: &mut FxHashMap<ExprId, ExprId>,
) -> ExprId {
    if !arena.get_expr_meta(e).has_level_param() {
        return e;
    }
    if let Some(&res) = cache.get(&e) {
        return res;
    }
    let res = match arena.get_expr(e).clone() {
        ExprData::Sort(l) => {
            let l2 = level_instantiate(arena, l, params, args);
            if l2 == l {
                e
            } else {
                arena.sort(l2)
            }
        }
        ExprData::Const(name, lvls) => {
            let mut changed = false;
            let mut out = Vec::with_capacity(lvls.len());
            for &l in lvls.iter() {
                let l2 = level_instantiate(arena, l, params, args);
                if l2 != l {
                    changed = true;
                }
                out.push(l2);
            }
            if !changed {
                e
            } else {
                arena.const_(name, out)
            }
        }
        ExprData::App(f, a) => {
            let f2 = inst_lvl_rec(arena, f, params, args, cache);
            let a2 = inst_lvl_rec(arena, a, params, args, cache);
            if f2 == f && a2 == a {
                e
            } else {
                arena.app(f2, a2)
            }
        }
        ExprData::Lam {
            name,
            binder_info,
            ty,
            body,
        } => {
            let ty2 = inst_lvl_rec(arena, ty, params, args, cache);
            let body2 = inst_lvl_rec(arena, body, params, args, cache);
            if ty2 == ty && body2 == body {
                e
            } else {
                arena.lam(name, binder_info, ty2, body2)
            }
        }
        ExprData::Pi {
            name,
            binder_info,
            ty,
            body,
        } => {
            let ty2 = inst_lvl_rec(arena, ty, params, args, cache);
            let body2 = inst_lvl_rec(arena, body, params, args, cache);
            if ty2 == ty && body2 == body {
                e
            } else {
                arena.pi(name, binder_info, ty2, body2)
            }
        }
        ExprData::Let {
            name,
            ty,
            val,
            body,
        } => {
            let ty2 = inst_lvl_rec(arena, ty, params, args, cache);
            let val2 = inst_lvl_rec(arena, val, params, args, cache);
            let body2 = inst_lvl_rec(arena, body, params, args, cache);
            if ty2 == ty && val2 == val && body2 == body {
                e
            } else {
                arena.let_(name, ty2, val2, body2)
            }
        }
        ExprData::Proj {
            struct_name,
            idx,
            expr,
        } => {
            let expr2 = inst_lvl_rec(arena, expr, params, args, cache);
            if expr2 == expr {
                e
            } else {
                arena.intern_expr(ExprData::Proj {
                    struct_name,
                    idx,
                    expr: expr2,
                })
            }
        }
        ExprData::BVar(_) | ExprData::FVar(_) | ExprData::Lit(_) => e,
    };
    cache.insert(e, res);
    res
}

/// Verify that every universe parameter in `e` is declared in `allowed` (DAG-memoized).
pub fn expr_check_level_params(
    arena: &Arena,
    e: ExprId,
    allowed: &[NameId],
) -> Result<(), KernelError> {
    if !arena.get_expr_meta(e).has_level_param() {
        return Ok(());
    }
    let mut visited = crate::hash::FxHashSet::default();
    check_lvl_rec(arena, e, allowed, &mut visited)
}

fn check_lvl_rec(
    arena: &Arena,
    e: ExprId,
    allowed: &[NameId],
    visited: &mut crate::hash::FxHashSet<ExprId>,
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

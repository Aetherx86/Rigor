//! Predicative universe level algebra (`Zero`, `Succ`, `Max`, `IMax`, `Param`).
//! Smart constructors canonicalize on interning; `level_leq` / `level_eq` handle `IMax`
//! via complete case-splitting on blocking universe parameters (`p = 0` and `p = succ p`).

use crate::arena::{Arena, LevelData, LevelId, NameId};
use crate::error::KernelError;

impl Arena {
    pub fn lvl_nat(&mut self, n: u32) -> LevelId {
        let mut l = Self::LEVEL_ZERO;
        for _ in 0..n { l = self.lvl_succ(l); }
        l
    }

    pub fn lvl_param(&mut self, name: NameId) -> LevelId { self.intern_level_raw(LevelData::Param(name)) }
    pub fn lvl_succ(&mut self, l: LevelId) -> LevelId { self.intern_level_raw(LevelData::Succ(l)) }

    pub fn lvl_max(&mut self, a: LevelId, b: LevelId) -> LevelId {
        if a == b || b == Self::LEVEL_ZERO { return a; }
        if a == Self::LEVEL_ZERO { return b; }
        match (self.get_level(a).clone(), self.get_level(b).clone()) {
            (LevelData::Succ(a1), LevelData::Succ(b1)) => { let m = self.lvl_max(a1, b1); return self.lvl_succ(m); }
            (LevelData::Max(a1, a2), _) if a1 == b || a2 == b => return a,
            (_, LevelData::Max(b1, b2)) if b1 == a || b2 == a => return b,
            _ => {}
        }
        let (x, y) = if a.0 <= b.0 { (a, b) } else { (b, a) };
        self.intern_level_raw(LevelData::Max(x, y))
    }

    pub fn lvl_imax(&mut self, a: LevelId, b: LevelId) -> LevelId {
        if level_is_zero(self, b) { return Self::LEVEL_ZERO; }
        if level_is_nonzero(self, b) { return self.lvl_max(a, b); }
        if a == Self::LEVEL_ZERO || a == b { return b; }
        self.intern_level_raw(LevelData::IMax(a, b))
    }
}

pub fn level_is_zero(arena: &Arena, l: LevelId) -> bool {
    match arena.get_level(l) {
        LevelData::Zero => true,
        LevelData::Succ(_) | LevelData::Param(_) => false,
        LevelData::Max(a, b) => level_is_zero(arena, *a) && level_is_zero(arena, *b),
        LevelData::IMax(_, b) => level_is_zero(arena, *b),
    }
}

pub fn level_is_nonzero(arena: &Arena, l: LevelId) -> bool {
    match arena.get_level(l) {
        LevelData::Zero | LevelData::Param(_) => false,
        LevelData::Succ(_) => true,
        LevelData::Max(a, b) => level_is_nonzero(arena, *a) || level_is_nonzero(arena, *b),
        LevelData::IMax(_, b) => level_is_nonzero(arena, *b),
    }
}

pub fn level_instantiate(arena: &mut Arena, l: LevelId, params: &[NameId], args: &[LevelId]) -> LevelId {
    debug_assert_eq!(params.len(), args.len());
    if params.is_empty() || !arena.get_level_meta(l).has_param { return l; }
    match arena.get_level(l).clone() {
        LevelData::Zero => Arena::LEVEL_ZERO,
        LevelData::Param(p) => params.iter().zip(args).find(|(q, _)| **q == p).map(|(_, &a)| a).unwrap_or(l),
        LevelData::Succ(x) => {
            let x2 = level_instantiate(arena, x, params, args);
            if x2 == x { l } else { arena.lvl_succ(x2) }
        }
        LevelData::Max(a, b) => {
            let (a2, b2) = (level_instantiate(arena, a, params, args), level_instantiate(arena, b, params, args));
            if a2 == a && b2 == b { l } else { arena.lvl_max(a2, b2) }
        }
        LevelData::IMax(a, b) => {
            let (a2, b2) = (level_instantiate(arena, a, params, args), level_instantiate(arena, b, params, args));
            if a2 == a && b2 == b { l } else { arena.lvl_imax(a2, b2) }
        }
    }
}

pub fn level_check_params(arena: &Arena, l: LevelId, allowed: &[NameId]) -> Result<(), KernelError> {
    if !arena.get_level_meta(l).has_param { return Ok(()); }
    match arena.get_level(l) {
        LevelData::Zero => Ok(()),
        LevelData::Param(p) => if allowed.contains(p) { Ok(()) } else { Err(KernelError::UnboundLevelParam(*p)) },
        LevelData::Succ(x) => level_check_params(arena, *x, allowed),
        LevelData::Max(a, b) | LevelData::IMax(a, b) => {
            level_check_params(arena, *a, allowed)?;
            level_check_params(arena, *b, allowed)
        }
    }
}

fn find_imax_split_param(arena: &Arena, l: LevelId) -> Option<NameId> {
    match arena.get_level(l) {
        LevelData::Zero | LevelData::Param(_) => None,
        LevelData::Succ(x) => find_imax_split_param(arena, *x),
        LevelData::Max(a, b) => find_imax_split_param(arena, *a).or_else(|| find_imax_split_param(arena, *b)),
        LevelData::IMax(a, b) => find_rightmost_param(arena, *b)
            .or_else(|| find_imax_split_param(arena, *a))
            .or_else(|| find_imax_split_param(arena, *b)),
    }
}

fn find_rightmost_param(arena: &Arena, l: LevelId) -> Option<NameId> {
    match arena.get_level(l) {
        LevelData::Param(p) => Some(*p),
        LevelData::Max(a, b) => find_rightmost_param(arena, *a).or_else(|| find_rightmost_param(arena, *b)),
        LevelData::IMax(_, b) => find_rightmost_param(arena, *b),
        LevelData::Zero | LevelData::Succ(_) => None,
    }
}

fn collect_atoms(arena: &Arena, l: LevelId, add: u32, out: &mut Vec<(Option<NameId>, u32)>) {
    match arena.get_level(l) {
        LevelData::Zero => push_atom(out, None, add),
        LevelData::Param(p) => push_atom(out, Some(*p), add),
        LevelData::Succ(x) => collect_atoms(arena, *x, add.saturating_add(1), out),
        LevelData::Max(a, b) => { collect_atoms(arena, *a, add, out); collect_atoms(arena, *b, add, out); }
        LevelData::IMax(_, _) => unreachable!("all IMax nodes eliminated before atom collection"),
    }
}

fn push_atom(out: &mut Vec<(Option<NameId>, u32)>, base: Option<NameId>, off: u32) {
    for (b, k) in out.iter_mut() {
        if *b == base { if off > *k { *k = off; } return; }
    }
    out.push((base, off));
}

/// Semantic universe inequality `a <= b` under all assignments of universe parameters to naturals.
pub fn level_leq(arena: &mut Arena, a: LevelId, b: LevelId) -> bool {
    if a == b || level_is_zero(arena, a) { return true; }
    if level_is_zero(arena, b) { return false; }
    if let Some(p) = find_imax_split_param(arena, a).or_else(|| find_imax_split_param(arena, b)) {
        let z = Arena::LEVEL_ZERO;
        let (a0, b0) = (level_instantiate(arena, a, &[p], &[z]), level_instantiate(arena, b, &[p], &[z]));
        if !level_leq(arena, a0, b0) { return false; }
        let p_id = arena.lvl_param(p);
        let p_s = arena.lvl_succ(p_id);
        let (a1, b1) = (level_instantiate(arena, a, &[p], &[p_s]), level_instantiate(arena, b, &[p], &[p_s]));
        return level_leq(arena, a1, b1);
    }
    let (mut atoms_a, mut atoms_b) = (Vec::with_capacity(4), Vec::with_capacity(4));
    collect_atoms(arena, a, 0, &mut atoms_a);
    collect_atoms(arena, b, 0, &mut atoms_b);
    let max_const_b = atoms_b.iter().map(|&(_, k)| k).max().unwrap_or(0);
    for (base_a, off_a) in atoms_a {
        match base_a {
            None => if off_a > max_const_b { return false; },
            Some(p) => if !atoms_b.iter().any(|&(bb, ob)| bb == Some(p) && off_a <= ob) { return false; },
        }
    }
    true
}

/// Semantic universe equality `a == b` under all parameter assignments.
pub fn level_eq(arena: &mut Arena, a: LevelId, b: LevelId) -> bool {
    a == b || (level_leq(arena, a, b) && level_leq(arena, b, a))
}

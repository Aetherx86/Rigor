//! Two-tier flat hash-consed DAG arenas for `Name`, `Level`, and `Expr`.

use std::sync::Arc;

use crate::hash::FxHashMap;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct NameId(pub u32);
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct LevelId(pub u32);
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct LevelListId(pub u32);
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct LitId(pub u32);
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ExprId(pub u32);
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FVarId(pub u32);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum NameData {
    Anonymous,
    Str(NameId, Box<str>),
    Num(NameId, u64),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum LevelData {
    Zero,
    Succ(LevelId),
    Max(LevelId, LevelId),
    IMax(LevelId, LevelId),
    Param(NameId),
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct LevelMeta {
    pub has_param: bool,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum BinderInfo {
    Default,
    Implicit,
    StrictImplicit,
    InstImplicit,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Literal {
    Nat(crate::nat::Nat),
    Str(Box<str>),
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum ExprData {
    BVar(u32),
    FVar(FVarId),
    Sort(LevelId),
    Const(NameId, LevelListId),
    App(ExprId, ExprId),
    Lam { name: NameId, binder_info: BinderInfo, ty: ExprId, body: ExprId },
    Pi { name: NameId, binder_info: BinderInfo, ty: ExprId, body: ExprId },
    Let { ty: ExprId, val: ExprId, body: ExprId },
    Lit(LitId),
    Proj { struct_name: NameId, idx: u32, expr: ExprId },
}

pub const FLAG_HAS_FVAR: u8 = 1 << 0;
pub const FLAG_HAS_LEVEL_PARAM: u8 = 1 << 1;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct ExprMeta {
    pub loose_bvar_range: u32,
    pub flags: u8,
}

impl ExprMeta {
    #[inline]
    pub fn has_fvar(self) -> bool { (self.flags & FLAG_HAS_FVAR) != 0 }
    #[inline]
    pub fn has_level_param(self) -> bool { (self.flags & FLAG_HAS_LEVEL_PARAM) != 0 }
    #[inline]
    pub fn is_closed(self) -> bool { self.loose_bvar_range == 0 }
}

/// One hash-consed table (names, levels, level lists or literals) of one arena tier: ids below
/// `base` belong to the parent arena.
#[derive(Debug)]
struct Table<T> {
    base: u32,
    items: Vec<T>,
    map: FxHashMap<T, u32>,
}

impl<T: core::hash::Hash + Eq + Clone> Table<T> {
    fn new(base: u32) -> Self { Table { base, items: Vec::new(), map: FxHashMap::default() } }
    fn len(&self) -> u32 { self.base + self.items.len() as u32 }
    fn push(&mut self, d: T) -> u32 {
        let id = self.len();
        self.items.push(d.clone());
        self.map.insert(d, id);
        id
    }
    fn truncate(&mut self, n: u32) {
        for d in self.items.drain((n - self.base) as usize..) { self.map.remove(&d); }
    }
}

/// Hash-consed flat DAG store supporting an optional immutable shared parent arena.
#[derive(Debug)]
pub struct Arena {
    parent: Option<Arc<Arena>>,
    names: Table<NameData>,
    levels: Table<LevelData>,
    level_meta: Vec<LevelMeta>,
    level_lists: Table<Box<[LevelId]>>,
    lits: Table<Literal>,
    expr_base: u32,
    exprs: Vec<ExprData>,
    expr_meta: Vec<ExprMeta>,
    /// Hash-consing index over this arena's own expressions: open addressing with linear probing,
    /// storing only `u32` ids (equality is checked against `exprs`), so each expression is
    /// stored once rather than again as a hash-map key.
    expr_table: Vec<u32>,
    expr_table_len: usize,
    bvar_cache: [u32; 32],
}

impl Default for Arena {
    fn default() -> Self { Self::new() }
}

macro_rules! tier_lookup {
    ($self:ident, $field:ident, $key:expr) => {{
        let mut a: &Arena = &*$self;
        loop {
            if let Some(&id) = a.$field.map.get($key) { break Some(id); }
            match a.parent.as_deref() { Some(p) => a = p, None => break None }
        }
    }};
}
macro_rules! tier_get {
    ($self:ident, $field:ident, $id:expr) => {{
        let mut a: &Arena = $self;
        while $id < a.$field.base { a = a.parent.as_deref().unwrap(); }
        &a.$field.items[($id - a.$field.base) as usize]
    }};
}

impl Arena {
    pub const ANONYMOUS: NameId = NameId(0);
    pub const LEVEL_ZERO: LevelId = LevelId(0);
    pub const EMPTY_LEVELS: LevelListId = LevelListId(0);

    fn with_parent(parent: Option<Arc<Arena>>) -> Self {
        let p = parent.as_deref();
        let base = |f: fn(&Arena) -> u32| p.map_or(0, f);
        Self {
            names: Table::new(base(Arena::name_len)),
            levels: Table::new(base(Arena::level_len)),
            level_meta: Vec::new(),
            level_lists: Table::new(base(Arena::level_list_len)),
            lits: Table::new(base(Arena::lit_len)),
            expr_base: base(Arena::expr_len),
            exprs: Vec::new(),
            expr_meta: Vec::new(),
            expr_table: Vec::new(),
            expr_table_len: 0,
            bvar_cache: [u32::MAX; 32],
            parent,
        }
    }
    pub fn new() -> Self {
        let mut a = Self::with_parent(None);
        let n0 = a.intern_name_raw(NameData::Anonymous);
        let l0 = a.intern_level_raw(LevelData::Zero);
        let ll0 = a.intern_level_list(&[]);
        debug_assert_eq!((n0, l0, ll0), (Self::ANONYMOUS, Self::LEVEL_ZERO, Self::EMPTY_LEVELS));
        a
    }
    pub fn child(parent: Arc<Arena>) -> Self { Self::with_parent(Some(parent)) }

    #[inline]
    pub fn name_len(&self) -> u32 { self.names.len() }
    #[inline]
    pub fn level_len(&self) -> u32 { self.levels.len() }
    #[inline]
    pub fn level_list_len(&self) -> u32 { self.level_lists.len() }
    #[inline]
    pub fn lit_len(&self) -> u32 { self.lits.len() }
    #[inline]
    pub fn expr_len(&self) -> u32 { self.expr_base + self.exprs.len() as u32 }

    // ---------------------------------------------------------------- Names, levels, lists, literals
    fn intern_name_raw(&mut self, data: NameData) -> NameId {
        NameId(tier_lookup!(self, names, &data).unwrap_or_else(|| self.names.push(data)))
    }
    pub fn name_str(&mut self, parent: NameId, seg: &str) -> NameId { self.intern_name_raw(NameData::Str(parent, seg.into())) }
    pub fn name_num(&mut self, parent: NameId, num: u64) -> NameId { self.intern_name_raw(NameData::Num(parent, num)) }
    pub fn name_from_path(&mut self, path: &str) -> NameId {
        let mut cur = Self::ANONYMOUS;
        if !path.is_empty() {
            for seg in path.split('.') { cur = self.name_str(cur, seg); }
        }
        cur
    }
    #[inline]
    pub fn get_name(&self, id: NameId) -> &NameData { tier_get!(self, names, id.0) }

    pub(crate) fn intern_level_raw(&mut self, data: LevelData) -> LevelId {
        if let Some(id) = tier_lookup!(self, levels, &data) { return LevelId(id); }
        let has_param = match &data {
            LevelData::Zero => false,
            LevelData::Param(_) => true,
            LevelData::Succ(l) => self.get_level_meta(*l).has_param,
            LevelData::Max(a, b) | LevelData::IMax(a, b) => self.get_level_meta(*a).has_param || self.get_level_meta(*b).has_param,
        };
        self.level_meta.push(LevelMeta { has_param });
        LevelId(self.levels.push(data))
    }
    #[inline]
    pub fn get_level(&self, id: LevelId) -> &LevelData { tier_get!(self, levels, id.0) }
    #[inline]
    pub fn get_level_meta(&self, id: LevelId) -> LevelMeta {
        let mut a = self;
        while id.0 < a.levels.base { a = a.parent.as_deref().unwrap(); }
        a.level_meta[(id.0 - a.levels.base) as usize]
    }

    pub fn intern_level_list(&mut self, levels: &[LevelId]) -> LevelListId {
        if levels.is_empty() && self.level_list_len() > 0 { return Self::EMPTY_LEVELS; }
        LevelListId(tier_lookup!(self, level_lists, levels).unwrap_or_else(|| self.level_lists.push(levels.into())))
    }
    #[inline]
    pub fn get_level_list(&self, id: LevelListId) -> &[LevelId] { tier_get!(self, level_lists, id.0) }

    pub fn intern_lit(&mut self, data: Literal) -> LitId {
        LitId(tier_lookup!(self, lits, &data).unwrap_or_else(|| self.lits.push(data)))
    }
    #[inline]
    pub fn get_lit(&self, id: LitId) -> &Literal { tier_get!(self, lits, id.0) }

    // ---------------------------------------------------------------- Expressions
    #[inline]
    fn lookup_bvar(&self, idx: usize) -> Option<ExprId> {
        let v = self.bvar_cache[idx];
        if v != u32::MAX { Some(ExprId(v)) } else { self.parent.as_deref().and_then(|p| p.lookup_bvar(idx)) }
    }
    #[inline]
    fn expr_hash(data: &ExprData) -> u64 {
        use core::hash::{Hash, Hasher};
        let mut h = crate::hash::FxHasher::default();
        data.hash(&mut h);
        h.finish()
    }
    /// Data of an expression owned by this arena (not the parent).
    #[inline]
    fn own_expr(&self, id: u32) -> &ExprData { &self.exprs[(id - self.expr_base) as usize] }
    fn table_find(&self, data: &ExprData, h: u64) -> Option<ExprId> {
        if self.expr_table.is_empty() { return None; }
        let mask = self.expr_table.len() - 1;
        let mut i = h as usize & mask;
        loop {
            let s = self.expr_table[i];
            if s == u32::MAX { return None; }
            if self.own_expr(s) == data { return Some(ExprId(s)); }
            i = (i + 1) & mask;
        }
    }
    fn table_place(table: &mut [u32], id: u32, h: u64) {
        let mask = table.len() - 1;
        let mut i = h as usize & mask;
        while table[i] != u32::MAX { i = (i + 1) & mask; }
        table[i] = id;
    }
    fn table_insert(&mut self, id: u32, h: u64) {
        if (self.expr_table_len + 1) * 4 > self.expr_table.len() * 3 {
            let cap = (self.expr_table.len() * 2).max(1024);
            let mut grown = vec![u32::MAX; cap];
            for &s in self.expr_table.iter().filter(|&&s| s != u32::MAX) {
                Self::table_place(&mut grown, s, Self::expr_hash(self.own_expr(s)));
            }
            self.expr_table = grown;
        }
        Self::table_place(&mut self.expr_table, id, h);
        self.expr_table_len += 1;
    }
    /// Remove `id` with backward-shift deletion (keeps every probe chain intact).
    fn table_remove(&mut self, id: u32) {
        let mask = self.expr_table.len() - 1;
        let mut i = Self::expr_hash(self.own_expr(id)) as usize & mask;
        while self.expr_table[i] != id { i = (i + 1) & mask; }
        let mut j = i;
        loop {
            j = (j + 1) & mask;
            let s = self.expr_table[j];
            if s == u32::MAX { break; }
            let k = Self::expr_hash(self.own_expr(s)) as usize & mask;
            // move `s` back into the hole at `i` unless its home slot lies cyclically in (i, j]
            let in_range = if i <= j { i < k && k <= j } else { i < k || k <= j };
            if !in_range {
                self.expr_table[i] = s;
                i = j;
            }
        }
        self.expr_table[i] = u32::MAX;
        self.expr_table_len -= 1;
    }
    fn lookup_expr_h(&self, data: &ExprData, h: u64) -> Option<ExprId> {
        self.table_find(data, h).or_else(|| self.parent.as_deref().and_then(|p| p.lookup_expr_h(data, h)))
    }
    pub fn intern_expr(&mut self, data: ExprData) -> ExprId {
        if let ExprData::BVar(idx) = data { if (idx as usize) < 32 { return self.bvar(idx); } }
        let h = Self::expr_hash(&data);
        if let Some(id) = self.lookup_expr_h(&data, h) { return id; }
        let meta = self.compute_expr_meta(&data);
        let id = ExprId(self.expr_len());
        self.exprs.push(data);
        self.expr_meta.push(meta);
        self.table_insert(id.0, h);
        id
    }
    fn compute_expr_meta(&self, data: &ExprData) -> ExprMeta {
        match data {
            ExprData::BVar(idx) => ExprMeta { loose_bvar_range: idx.saturating_add(1), flags: 0 },
            ExprData::FVar(_) => ExprMeta { loose_bvar_range: 0, flags: FLAG_HAS_FVAR },
            ExprData::Sort(l) => ExprMeta {
                loose_bvar_range: 0,
                flags: if self.get_level_meta(*l).has_param { FLAG_HAS_LEVEL_PARAM } else { 0 },
            },
            ExprData::Const(_, lvls) => ExprMeta {
                loose_bvar_range: 0,
                flags: if self.get_level_list(*lvls).iter().any(|&l| self.get_level_meta(l).has_param) { FLAG_HAS_LEVEL_PARAM } else { 0 },
            },
            ExprData::App(f, a) => {
                let (mf, ma) = (self.get_expr_meta(*f), self.get_expr_meta(*a));
                ExprMeta { loose_bvar_range: mf.loose_bvar_range.max(ma.loose_bvar_range), flags: mf.flags | ma.flags }
            }
            ExprData::Lam { ty, body, .. } | ExprData::Pi { ty, body, .. } => {
                let (mt, mb) = (self.get_expr_meta(*ty), self.get_expr_meta(*body));
                ExprMeta {
                    loose_bvar_range: mt.loose_bvar_range.max(mb.loose_bvar_range.saturating_sub(1)),
                    flags: mt.flags | mb.flags,
                }
            }
            ExprData::Let { ty, val, body, .. } => {
                let (mt, mv, mb) = (self.get_expr_meta(*ty), self.get_expr_meta(*val), self.get_expr_meta(*body));
                ExprMeta {
                    loose_bvar_range: mt.loose_bvar_range.max(mv.loose_bvar_range).max(mb.loose_bvar_range.saturating_sub(1)),
                    flags: mt.flags | mv.flags | mb.flags,
                }
            }
            ExprData::Lit(_) => ExprMeta { loose_bvar_range: 0, flags: 0 },
            ExprData::Proj { expr, .. } => self.get_expr_meta(*expr),
        }
    }
    #[inline]
    pub fn get_expr(&self, id: ExprId) -> &ExprData {
        if id.0 < self.expr_base { self.parent.as_deref().unwrap().get_expr(id) }
        else { &self.exprs[(id.0 - self.expr_base) as usize] }
    }
    #[inline]
    pub fn get_expr_meta(&self, id: ExprId) -> ExprMeta {
        if id.0 < self.expr_base { self.parent.as_deref().unwrap().get_expr_meta(id) }
        else { self.expr_meta[(id.0 - self.expr_base) as usize] }
    }

    #[inline]
    pub fn bvar(&mut self, idx: u32) -> ExprId {
        if (idx as usize) < 32 {
            if let Some(id) = self.lookup_bvar(idx as usize) { return id; }
            let id = ExprId(self.expr_len());
            self.exprs.push(ExprData::BVar(idx));
            self.expr_meta.push(ExprMeta { loose_bvar_range: idx + 1, flags: 0 });
            self.bvar_cache[idx as usize] = id.0;
            id
        } else {
            self.intern_expr(ExprData::BVar(idx))
        }
    }
    #[inline]
    pub fn fvar(&mut self, id: FVarId) -> ExprId { self.intern_expr(ExprData::FVar(id)) }
    #[inline]
    pub fn sort(&mut self, level: LevelId) -> ExprId { self.intern_expr(ExprData::Sort(level)) }
    #[inline]
    pub fn prop(&mut self) -> ExprId { self.sort(Self::LEVEL_ZERO) }
    #[inline]
    pub fn const_(&mut self, name: NameId, levels: impl AsRef<[LevelId]>) -> ExprId {
        let lvls = self.intern_level_list(levels.as_ref());
        self.intern_expr(ExprData::Const(name, lvls))
    }
    pub fn const_path(&mut self, path: &str, levels: impl AsRef<[LevelId]>) -> ExprId {
        let n = self.name_from_path(path);
        self.const_(n, levels)
    }
    #[inline]
    pub fn app(&mut self, f: ExprId, a: ExprId) -> ExprId { self.intern_expr(ExprData::App(f, a)) }
    pub fn app_n(&mut self, mut f: ExprId, args: &[ExprId]) -> ExprId {
        for &a in args { f = self.app(f, a); }
        f
    }
    #[inline]
    pub fn lam(&mut self, name: NameId, binder_info: BinderInfo, ty: ExprId, body: ExprId) -> ExprId {
        self.intern_expr(ExprData::Lam { name, binder_info, ty, body })
    }
    #[inline]
    pub fn pi(&mut self, name: NameId, binder_info: BinderInfo, ty: ExprId, body: ExprId) -> ExprId {
        self.intern_expr(ExprData::Pi { name, binder_info, ty, body })
    }
    #[inline]
    pub fn let_(&mut self, _name: NameId, ty: ExprId, val: ExprId, body: ExprId) -> ExprId {
        self.intern_expr(ExprData::Let { ty, val, body })
    }
    #[inline]
    pub fn proj(&mut self, struct_name: NameId, idx: u32, expr: ExprId) -> ExprId {
        self.intern_expr(ExprData::Proj { struct_name, idx, expr })
    }
    #[inline]
    pub fn lit_nat(&mut self, n: u128) -> ExprId { self.lit_nat_big(crate::nat::Nat::from_u128(n)) }
    pub fn lit_nat_big(&mut self, n: crate::nat::Nat) -> ExprId {
        let lid = self.intern_lit(Literal::Nat(n));
        self.intern_expr(ExprData::Lit(lid))
    }
    #[inline]
    pub fn lit_str(&mut self, s: &str) -> ExprId {
        let lid = self.intern_lit(Literal::Str(s.into()));
        self.intern_expr(ExprData::Lit(lid))
    }

    /// Reclaim temporary expressions/levels/names interned during single-declaration type-checking.
    /// Release spare capacity and pack the hash-consing table (load up to 7/8) before the arena
    /// is frozen and shared read-only with checker threads.
    pub fn shrink_for_sharing(&mut self) {
        self.names.items.shrink_to_fit();
        self.levels.items.shrink_to_fit();
        self.level_meta.shrink_to_fit();
        self.level_lists.items.shrink_to_fit();
        self.lits.items.shrink_to_fit();
        self.exprs.shrink_to_fit();
        self.expr_meta.shrink_to_fit();
        let mut cap = 1024usize;
        while cap * 7 < self.expr_table_len * 8 + 8 { cap *= 2; }
        if cap < self.expr_table.len() {
            let mut packed = vec![u32::MAX; cap];
            for &s in self.expr_table.iter().filter(|&&s| s != u32::MAX) {
                Self::table_place(&mut packed, s, Self::expr_hash(self.own_expr(s)));
            }
            self.expr_table = packed;
        }
    }
    pub fn truncate_to(&mut self, n_len: u32, l_len: u32, ll_len: u32, lit_len: u32, e_len: u32) {
        debug_assert!(self.parent.is_none());
        for id in (e_len..self.expr_len()).rev() {
            match *self.own_expr(id) {
                // small bound variables live in `bvar_cache`, not in the table
                ExprData::BVar(i) if (i as usize) < 32 => {
                    if self.bvar_cache[i as usize] == id { self.bvar_cache[i as usize] = u32::MAX; }
                }
                _ => self.table_remove(id),
            }
        }
        self.exprs.truncate(e_len as usize);
        self.expr_meta.truncate(e_len as usize);
        self.names.truncate(n_len);
        self.levels.truncate(l_len);
        self.level_meta.truncate(l_len as usize);
        self.level_lists.truncate(ll_len);
        self.lits.truncate(lit_len);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn expr_data_size_at_most_16_bytes() {
        assert!(
            core::mem::size_of::<ExprData>() <= 16,
            "ExprData is {} bytes, expected <= 16",
            core::mem::size_of::<ExprData>()
        );
    }

    #[test]
    fn level_lists_and_lits_child_and_truncate() {
        let mut a = Arena::new();
        let l0 = Arena::LEVEL_ZERO;
        let l1 = a.lvl_nat(1);
        let l2 = a.lvl_nat(2);

        let ll_empty = a.intern_level_list(&[]);
        assert_eq!(ll_empty, Arena::EMPTY_LEVELS);
        assert_eq!(a.get_level_list(ll_empty), &[]);

        let ll1 = a.intern_level_list(&[l1, l2]);
        let ll1_dup = a.intern_level_list(&[l1, l2]);
        assert_eq!(ll1, ll1_dup);
        assert_eq!(a.get_level_list(ll1), &[l1, l2]);

        let lit_n = a.lit_nat(42);
        let lit_n_dup = a.lit_nat(42);
        let lit_s = a.lit_str("hello");
        assert_eq!(lit_n, lit_n_dup);
        assert_ne!(lit_n, lit_s);

        // Snapshot before temporary allocations
        let snap = (a.name_len(), a.level_len(), a.level_list_len(), a.lit_len(), a.expr_len());
        let tmp_name = a.name_from_path("Tmp.Const");
        let tmp_ll = a.intern_level_list(&[l0, l1, l2]);
        let tmp_const = a.const_(tmp_name, [l0, l1, l2]);
        let tmp_lit = a.lit_str("temporary");
        assert!(tmp_ll.0 >= snap.2);
        assert!(tmp_const.0 >= snap.4);
        assert!(tmp_lit.0 >= snap.4);

        a.truncate_to(snap.0, snap.1, snap.2, snap.3, snap.4);
        assert_eq!((a.name_len(), a.level_len(), a.level_list_len(), a.lit_len(), a.expr_len()), snap);

        // Re-interning after truncation must succeed cleanly
        let tmp_ll_again = a.intern_level_list(&[l0, l1, l2]);
        assert_eq!(tmp_ll_again, tmp_ll);
        assert_eq!(a.get_level_list(tmp_ll_again), &[l0, l1, l2]);
        let tmp_lit_again = a.lit_str("temporary");
        assert_eq!(a.get_lit(match *a.get_expr(tmp_lit_again) {
            ExprData::Lit(id) => id,
            _ => unreachable!(),
        }), &Literal::Str("temporary".into()));

        // Child arena shares parent level lists and literals without mutating parent
        let parent = Arc::new(a);
        let mut child = Arena::child(Arc::clone(&parent));
        assert_eq!(child.intern_level_list(&[l1, l2]), ll1);
        assert_eq!(child.lit_nat(42), lit_n);
        assert_eq!(child.lit_str("hello"), lit_s);

        let child_ll = child.intern_level_list(&[l2, l0]);
        assert!(child_ll.0 >= parent.level_list_len());
        assert_eq!(child.get_level_list(child_ll), &[l2, l0]);
        assert_eq!(child.get_level_list(ll1), &[l1, l2]);

        let child_lit = child.lit_nat(9999);
        assert!(child_lit.0 >= parent.expr_len());
        assert_eq!(child.lit_nat(9999), child_lit);
    }
}

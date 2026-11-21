//! Two-tier flat hash-consed DAG arenas for `Name`, `Level`, and `Expr`.

use std::sync::Arc;

use crate::hash::FxHashMap;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct NameId(pub u32);
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct LevelId(pub u32);
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
    Nat(u64),
    Str(Box<str>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ExprData {
    BVar(u32),
    FVar(FVarId),
    Sort(LevelId),
    Const(NameId, Box<[LevelId]>),
    App(ExprId, ExprId),
    Lam { name: NameId, binder_info: BinderInfo, ty: ExprId, body: ExprId },
    Pi { name: NameId, binder_info: BinderInfo, ty: ExprId, body: ExprId },
    Let { name: NameId, ty: ExprId, val: ExprId, body: ExprId },
    Lit(Literal),
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

/// Hash-consed flat DAG store supporting an optional immutable shared parent arena.
#[derive(Debug)]
pub struct Arena {
    parent: Option<Arc<Arena>>,
    name_base: u32,
    level_base: u32,
    expr_base: u32,
    names: Vec<NameData>,
    name_map: FxHashMap<NameData, NameId>,
    levels: Vec<LevelData>,
    level_meta: Vec<LevelMeta>,
    level_map: FxHashMap<LevelData, LevelId>,
    exprs: Vec<ExprData>,
    expr_meta: Vec<ExprMeta>,
    expr_map: FxHashMap<ExprData, ExprId>,
}

impl Default for Arena {
    fn default() -> Self { Self::new() }
}

impl Arena {
    pub const ANONYMOUS: NameId = NameId(0);
    pub const LEVEL_ZERO: LevelId = LevelId(0);

    pub fn new() -> Self {
        let mut a = Self {
            parent: None,
            name_base: 0,
            level_base: 0,
            expr_base: 0,
            names: Vec::with_capacity(256),
            name_map: FxHashMap::default(),
            levels: Vec::with_capacity(128),
            level_meta: Vec::with_capacity(128),
            level_map: FxHashMap::default(),
            exprs: Vec::with_capacity(1024),
            expr_meta: Vec::with_capacity(1024),
            expr_map: FxHashMap::default(),
        };
        let n0 = a.intern_name_raw(NameData::Anonymous);
        let l0 = a.intern_level_raw(LevelData::Zero);
        debug_assert_eq!((n0, l0), (Self::ANONYMOUS, Self::LEVEL_ZERO));
        a
    }

    pub fn child(parent: Arc<Arena>) -> Self {
        let (name_base, level_base, expr_base) = (parent.name_len(), parent.level_len(), parent.expr_len());
        Self {
            parent: Some(parent),
            name_base,
            level_base,
            expr_base,
            names: Vec::new(),
            name_map: FxHashMap::default(),
            levels: Vec::new(),
            level_meta: Vec::new(),
            level_map: FxHashMap::default(),
            exprs: Vec::new(),
            expr_meta: Vec::new(),
            expr_map: FxHashMap::default(),
        }
    }

    #[inline]
    pub fn name_len(&self) -> u32 { self.name_base + self.names.len() as u32 }
    #[inline]
    pub fn level_len(&self) -> u32 { self.level_base + self.levels.len() as u32 }
    #[inline]
    pub fn expr_len(&self) -> u32 { self.expr_base + self.exprs.len() as u32 }

    // ---------------------------------------------------------------- Names
    fn lookup_name(&self, data: &NameData) -> Option<NameId> {
        self.name_map.get(data).copied().or_else(|| self.parent.as_deref().and_then(|p| p.lookup_name(data)))
    }
    fn intern_name_raw(&mut self, data: NameData) -> NameId {
        if let Some(id) = self.lookup_name(&data) { return id; }
        let id = NameId(self.name_len());
        self.names.push(data.clone());
        self.name_map.insert(data, id);
        id
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
    pub fn get_name(&self, id: NameId) -> &NameData {
        if id.0 < self.name_base { self.parent.as_deref().unwrap().get_name(id) }
        else { &self.names[(id.0 - self.name_base) as usize] }
    }
    pub fn format_name(&self, id: NameId) -> String {
        match self.get_name(id) {
            NameData::Anonymous => "[anonymous]".into(),
            NameData::Str(p, s) if *p == Self::ANONYMOUS => s.to_string(),
            NameData::Str(p, s) => format!("{}.{s}", self.format_name(*p)),
            NameData::Num(p, n) if *p == Self::ANONYMOUS => n.to_string(),
            NameData::Num(p, n) => format!("{}.{n}", self.format_name(*p)),
        }
    }

    // ---------------------------------------------------------------- Levels
    fn lookup_level(&self, data: &LevelData) -> Option<LevelId> {
        self.level_map.get(data).copied().or_else(|| self.parent.as_deref().and_then(|p| p.lookup_level(data)))
    }
    pub(crate) fn intern_level_raw(&mut self, data: LevelData) -> LevelId {
        if let Some(id) = self.lookup_level(&data) { return id; }
        let has_param = match &data {
            LevelData::Zero => false,
            LevelData::Param(_) => true,
            LevelData::Succ(l) => self.get_level_meta(*l).has_param,
            LevelData::Max(a, b) | LevelData::IMax(a, b) => {
                self.get_level_meta(*a).has_param || self.get_level_meta(*b).has_param
            }
        };
        let id = LevelId(self.level_len());
        self.levels.push(data.clone());
        self.level_meta.push(LevelMeta { has_param });
        self.level_map.insert(data, id);
        id
    }
    #[inline]
    pub fn get_level(&self, id: LevelId) -> &LevelData {
        if id.0 < self.level_base { self.parent.as_deref().unwrap().get_level(id) }
        else { &self.levels[(id.0 - self.level_base) as usize] }
    }
    #[inline]
    pub fn get_level_meta(&self, id: LevelId) -> LevelMeta {
        if id.0 < self.level_base { self.parent.as_deref().unwrap().get_level_meta(id) }
        else { self.level_meta[(id.0 - self.level_base) as usize] }
    }

    // ---------------------------------------------------------------- Expressions
    fn lookup_expr(&self, data: &ExprData) -> Option<ExprId> {
        self.expr_map.get(data).copied().or_else(|| self.parent.as_deref().and_then(|p| p.lookup_expr(data)))
    }
    pub fn intern_expr(&mut self, data: ExprData) -> ExprId {
        if let Some(id) = self.lookup_expr(&data) { return id; }
        let meta = self.compute_expr_meta(&data);
        let id = ExprId(self.expr_len());
        self.exprs.push(data.clone());
        self.expr_meta.push(meta);
        self.expr_map.insert(data, id);
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
                flags: if lvls.iter().any(|&l| self.get_level_meta(l).has_param) { FLAG_HAS_LEVEL_PARAM } else { 0 },
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
    pub fn bvar(&mut self, idx: u32) -> ExprId { self.intern_expr(ExprData::BVar(idx)) }
    #[inline]
    pub fn fvar(&mut self, id: FVarId) -> ExprId { self.intern_expr(ExprData::FVar(id)) }
    #[inline]
    pub fn sort(&mut self, level: LevelId) -> ExprId { self.intern_expr(ExprData::Sort(level)) }
    #[inline]
    pub fn prop(&mut self) -> ExprId { self.sort(Self::LEVEL_ZERO) }
    #[inline]
    pub fn const_(&mut self, name: NameId, levels: impl Into<Box<[LevelId]>>) -> ExprId {
        self.intern_expr(ExprData::Const(name, levels.into()))
    }
    pub fn const_path(&mut self, path: &str, levels: impl Into<Box<[LevelId]>>) -> ExprId {
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
    pub fn let_(&mut self, name: NameId, ty: ExprId, val: ExprId, body: ExprId) -> ExprId {
        self.intern_expr(ExprData::Let { name, ty, val, body })
    }
    #[inline]
    pub fn proj(&mut self, struct_name: NameId, idx: u32, expr: ExprId) -> ExprId {
        self.intern_expr(ExprData::Proj { struct_name, idx, expr })
    }
    #[inline]
    pub fn lit_nat(&mut self, n: u64) -> ExprId { self.intern_expr(ExprData::Lit(Literal::Nat(n))) }
    #[inline]
    pub fn lit_str(&mut self, s: &str) -> ExprId { self.intern_expr(ExprData::Lit(Literal::Str(s.into()))) }
}

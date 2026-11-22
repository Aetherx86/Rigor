//! Unified spine-machine WHNF reducer and definitional equality engine.
//! Supports beta, zeta, iota, K-like, quotient, `Nat` literals, structure projections,
//! height-ordered delta, proof irrelevance in `Prop`, and function + structure eta-conversion.

use crate::arena::{Arena, BinderInfo, ExprData, ExprId, FVarId, LevelId, LevelListId, Literal, NameId};
use crate::check::TypeChecker;
use crate::env::{Declaration, QuotKind};
use crate::error::KernelError;
use crate::expr::{instantiate1, instantiate_level_params, instantiate_rev};
use crate::level::{level_eq, level_is_zero};

impl<'a> TypeChecker<'a> {
    /// Cached universe-parameter instantiation (O(1) hit for the common 1-param case).
    pub(crate) fn inst_levels_cached(&mut self, e: ExprId, params: &[NameId], lvls: &[LevelId]) -> ExprId {
        if params.is_empty() || !self.arena.get_expr_meta(e).has_level_param() {
            return e;
        }
        if lvls.len() == 1 {
            let key = (e, lvls[0]);
            if let Some(&res) = self.inst_lvl1_cache.get(&key) {
                return res;
            }
            let res = instantiate_level_params(self.arena, e, params, lvls);
            self.inst_lvl1_cache.insert(key, res);
            return res;
        }
        instantiate_level_params(self.arena, e, params, lvls)
    }

    #[inline]
    fn inst_levels_list(&mut self, e: ExprId, params: &[NameId], lvls_id: LevelListId) -> ExprId {
        if params.is_empty() || !self.arena.get_expr_meta(e).has_level_param() {
            return e;
        }
        let lvls = self.arena.get_level_list(lvls_id);
        if lvls.len() == 1 {
            let l0 = lvls[0];
            return self.inst_levels_cached(e, params, &[l0]);
        }
        let owned: Box<[LevelId]> = lvls.into();
        instantiate_level_params(self.arena, e, params, &owned)
    }

    /// Reduce `e` to weak head normal form (beta + zeta + iota + proj + quot + delta).
    pub fn whnf(&mut self, e: ExprId) -> ExprId {
        if let Some(&cached) = self.whnf_cache.get(&e) {
            return cached;
        }
        let cur = self.whnf_spine(e, true, false);
        self.whnf_cache.insert(e, cur);
        cur
    }

    /// Reduce `e` to weak head normal form without delta unfolding and without unfolding
    /// definitions inside projection targets (Lean's `whnf_core(e, false, true)`).
    #[inline]
    pub(crate) fn whnf_no_delta(&mut self, e: ExprId) -> ExprId {
        self.whnf_spine(e, false, true)
    }

    /// If `e` is a projection application `s.i a1 ... an`, try reducing the projection using full
    /// WHNF on `s` (Lean's `try_unfold_proj_app`).
    fn try_unfold_proj_app(&mut self, e: ExprId) -> Option<ExprId> {
        let mut h = e;
        while let ExprData::App(f, _) = *self.arena.get_expr(h) {
            h = f;
        }
        if !matches!(self.arena.get_expr(h), ExprData::Proj { .. }) {
            return None;
        }
        let res = self.whnf_spine(e, false, false);
        (res != e).then_some(res)
    }

    fn whnf_spine(&mut self, e: ExprId, allow_delta: bool, cheap_proj: bool) -> ExprId {
        match self.arena.get_expr(e) {
            ExprData::Sort(_) | ExprData::Pi { .. } | ExprData::Lam { .. } | ExprData::Lit(_) | ExprData::BVar(_) => {
                return e;
            }
            ExprData::Const(_, _) if !allow_delta => return e,
            _ => {}
        }
        self.whnf_spine_with(e, Vec::new(), allow_delta, cheap_proj)
    }

    /// Unified spine abstract machine: keeps arguments on `spine` across beta, zeta,
    /// local FVar, Proj, Quot.lift, Recursor iota/K, and delta steps without interning
    /// intermediate `App` nodes into the arena.
    fn whnf_spine_with(&mut self, mut cur: ExprId, mut spine: Vec<ExprId>, allow_delta: bool, cheap_proj: bool) -> ExprId {
        loop {
            match self.arena.get_expr(cur) {
                ExprData::App(f, a) => {
                    let (f, a) = (*f, *a);
                    spine.push(a);
                    cur = f;
                }
                ExprData::Lam { body, .. } if !spine.is_empty() => {
                    let mut body = *body;
                    let first = spine.pop().unwrap();
                    if spine.is_empty() {
                        cur = instantiate1(self.arena, body, first);
                    } else {
                        let mut args = Vec::with_capacity(spine.len() + 1);
                        args.push(first);
                        while !spine.is_empty() {
                            if let ExprData::Lam { body: next, .. } = self.arena.get_expr(body) {
                                body = *next;
                                args.push(spine.pop().unwrap());
                            } else {
                                break;
                            }
                        }
                        cur = instantiate_rev(self.arena, body, &args);
                    }
                }
                ExprData::Let { val, body, .. } => {
                    let (val, body) = (*val, *body);
                    cur = instantiate1(self.arena, body, val);
                }
                ExprData::FVar(fv) => match self.local_value(*fv) {
                    Some(val) => cur = val,
                    None => break,
                },
                ExprData::Proj { struct_name, idx, expr } => {
                    let (sn, idx, expr) = (*struct_name, *idx, *expr);
                    if let Some(v) = self.reduce_proj_head(sn, idx, expr, cheap_proj) {
                        cur = v;
                    } else {
                        break;
                    }
                }
                ExprData::Const(name, lvls_id) => {
                    let (name, lvls_id) = (*name, *lvls_id);
                    let lvl_len = self.arena.get_level_list(lvls_id).len();
                    if lvls_id == Arena::EMPTY_LEVELS {
                        if let Some((res, consumed)) = self.try_reduce_nat(name, &spine, allow_delta) {
                            let new_len = spine.len() - consumed;
                            spine.truncate(new_len);
                            cur = res;
                            continue;
                        }
                    }
                    let Some(decl) = self.decls.get(&name) else { break };
                    match decl {
                        Declaration::Quot { kind: QuotKind::Lift, .. } if spine.len() >= 6 => {
                            let len = spine.len();
                            let major = self.whnf(spine[len - 6]);
                            let (mhead, margs) = self.app_spine(major);
                            if let ExprData::Const(mn, _) = self.arena.get_expr(mhead) {
                                if matches!(self.decls.get(mn), Some(Declaration::Quot { kind: QuotKind::Ctor, .. }))
                                    && margs.len() == 3
                                {
                                    let f = spine[len - 4];
                                    spine.truncate(len - 6);
                                    spine.push(margs[2]);
                                    cur = f;
                                    continue;
                                }
                            }
                            break;
                        }
                        Declaration::Recursor(rec) if lvl_len == rec.level_params.len() => {
                            let prefix_end = (rec.num_params + rec.num_motives + rec.num_minors) as usize;
                            let major_idx = prefix_end + rec.num_indices as usize;
                            let len = spine.len();
                            if len <= major_idx {
                                break;
                            }
                            // As in Lean's `inductive_reduce_rec`: for K-like recursors (e.g. `Eq.rec`) first
                            // try to replace the major premise by the constructor using its type alone
                            // (`to_cnstr_when_K`), and only then reduce it. Reducing first would unfold the
                            // proof itself, which can be arbitrarily expensive (e.g. `Nat.eq_of_beq_eq_true`
                            // on 13-digit numbers in `decide +kernel` proofs).
                            let raw_major = spine[len - 1 - major_idx];
                            let major = raw_major;
                            if rec.k && rec.rules.len() == 1 && rec.rules[0].num_fields == 0 {
                                let rule = &rec.rules[0];
                                if let Some(Declaration::Constructor(c)) = self.decls.get(&rule.ctor_name) {
                                    if let Ok(major_ty) = self.infer_type_only(major) {
                                        let mut ctor_ty = if c.level_params.is_empty() {
                                            c.ty
                                        } else {
                                            let ls = self.arena.get_level_list(lvls_id);
                                            let start = ls.len() - c.level_params.len();
                                            if c.level_params.len() == 1 {
                                                let l0 = ls[start];
                                                self.inst_levels_cached(c.ty, &c.level_params, &[l0])
                                            } else {
                                                let ind_lvls: Box<[LevelId]> = ls[start..].into();
                                                self.inst_levels_cached(c.ty, &c.level_params, &ind_lvls)
                                            }
                                        };
                                        let mut ok = true;
                                        for i in 0..rec.num_params as usize {
                                            ctor_ty = self.whnf(ctor_ty);
                                            if let ExprData::Pi { body, .. } = self.arena.get_expr(ctor_ty) {
                                                ctor_ty = instantiate1(self.arena, *body, spine[len - 1 - i]);
                                            } else {
                                                ok = false;
                                                break;
                                            }
                                        }
                                        if ok && self.is_def_eq(major_ty, ctor_ty).unwrap_or(false) {
                                            cur = self.inst_levels_list(rule.rhs, &rec.level_params, lvls_id);
                                            spine.drain(len - 1 - major_idx..len - prefix_end);
                                            continue;
                                        }
                                    }
                                }
                            }
                            let mut major = self.whnf_lit_ctor(raw_major);
                            if let ExprData::Lit(lid) = *self.arena.get_expr(major) {
                                if let Literal::Nat(k) = self.arena.get_lit(lid) {
                                    let k = k.clone();
                                    major = self.expand_nat_lit(&k);
                                }
                            }
                            let (mut mhead, mut margs) = self.app_spine(major);
                            // Structure eta in WHNF (Lean 4 `to_ctor_when_structure`):
                            // expand opaque `x : S` to `S.mk p... (x.0) ...` for non-Prop structures.
                            if rec.rules.len() == 1 && rec.all.len() == 1 && rec.num_indices == 0
                                && !matches!(self.arena.get_expr(mhead), ExprData::Const(cn, _) if *cn == rec.rules[0].ctor_name || *cn == name)
                            {
                                if let Some(Declaration::Inductive(ind)) = self.decls.get(&rec.all[0]) {
                                    if !ind.is_prop && !ind.is_rec && ind.ctors.len() == 1 && ind.num_indices == 0 && ind.all.len() == 1 {
                                        if let Ok(mty) = self.infer_type_only(major) {
                                            let mty_w = self.whnf(mty);
                                            let (th, ta) = self.app_spine(mty_w);
                                            if let ExprData::Const(tn, tls) = *self.arena.get_expr(th) {
                                                if tn == ind.name && ta.len() == ind.num_params as usize {
                                                    mhead = self.arena.intern_expr(ExprData::Const(ind.ctors[0], tls));
                                                    margs = ta;
                                                    for fi in 0..rec.rules[0].num_fields {
                                                        margs.push(self.arena.proj(ind.name, fi, major));
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                            if let ExprData::Const(cname, _) = self.arena.get_expr(mhead) {
                                let cname = *cname;
                                if let Some(rule) = rec.rules.iter().find(|r| r.ctor_name == cname) {
                                    let ctor_np = match self.decls.get(&cname) {
                                        Some(Declaration::Constructor(c)) => c.num_params,
                                        _ => rec.num_params,
                                    };
                                    if margs.len() == (ctor_np + rule.num_fields) as usize {
                                        cur = self.inst_levels_list(rule.rhs, &rec.level_params, lvls_id);
                                        let keep_tail = len - 1 - major_idx;
                                        spine.splice(
                                            keep_tail..len - prefix_end,
                                            margs[ctor_np as usize..].iter().rev().copied(),
                                        );
                                        continue;
                                    }
                                }
                            }
                            break;
                        }
                        _ if allow_delta => {
                            if let Some((val, _)) = decl.delta_value() {
                                let params = decl.level_params();
                                if lvl_len == params.len() {
                                    cur = self.inst_levels_list(val, params, lvls_id);
                                    continue;
                                }
                            }
                            break;
                        }
                        _ => break,
                    }
                }
                _ => break,
            }
        }
        while let Some(arg) = spine.pop() {
            cur = self.arena.app(cur, arg);
        }
        cur
    }

    fn reduce_proj_head(&mut self, struct_name: NameId, idx: u32, expr: ExprId, cheap_proj: bool) -> Option<ExprId> {
        let ind = match self.decls.get(&struct_name)? {
            Declaration::Inductive(i) if i.ctors.len() == 1 && i.num_indices == 0 => i,
            _ => return None,
        };
        let val = if cheap_proj { self.whnf_no_delta(expr) } else { self.whnf_lit_ctor(expr) };
        let (vhead, vargs) = self.app_spine(val);
        if let ExprData::Const(cname, _) = self.arena.get_expr(vhead) {
            let pos = ind.num_params as usize + idx as usize;
            if *cname == ind.ctors[0] && pos < vargs.len() {
                return Some(vargs[pos]);
            }
        }
        None
    }

    pub(crate) fn app_spine(&self, mut e: ExprId) -> (ExprId, Vec<ExprId>) {
        if !matches!(self.arena.get_expr(e), ExprData::App(_, _)) {
            return (e, Vec::new());
        }
        let mut args = Vec::new();
        while let ExprData::App(f, a) = self.arena.get_expr(e) {
            args.push(*a);
            e = *f;
        }
        args.reverse();
        (e, args)
    }

    #[inline]
    fn expand_nat_lit(&mut self, k: &crate::nat::Nat) -> ExprId {
        if k.is_zero() {
            if let Some(z) = self.nat_zero { z } else {
                let z = self.arena.const_path("Nat.zero", []);
                self.nat_zero = Some(z);
                z
            }
        } else {
            let succ = if let Some(s) = self.nat_succ { s } else {
                let s = self.arena.const_path("Nat.succ", []);
                self.nat_succ = Some(s);
                s
            };
            let pred = self.arena.lit_nat_big(k.sub(&crate::nat::Nat::from_u128(1)));
            self.arena.app(succ, pred)
        }
    }

    /// Lean 4 kernel string literal expansion: `"ab"` is definitionally
    /// `String.ofList [Char.ofNat 97, Char.ofNat 98]`. Used only when a recursor, a projection or a
    /// definitional-equality check needs the structure of the literal.
    fn expand_str_lit(&mut self, s: &str) -> ExprId {
        let l0 = self.arena.lvl_nat(0);
        let char_t = self.arena.const_path("Char", []);
        let of_nat = self.arena.const_path("Char.ofNat", []);
        let nil = self.arena.const_path("List.nil", [l0]);
        let cons = self.arena.const_path("List.cons", [l0]);
        let mut list = self.arena.app(nil, char_t);
        for c in s.chars().rev() {
            let code = self.arena.lit_nat(c as u128);
            let ch = self.arena.app(of_nat, code);
            list = self.arena.app_n(cons, &[char_t, ch, list]);
        }
        let of_list = self.arena.const_path("String.ofList", []);
        self.arena.app(of_list, list)
    }

    /// WHNF that also opens a string literal into its constructor form.
    fn whnf_lit_ctor(&mut self, e: ExprId) -> ExprId {
        let w = self.whnf(e);
        if let ExprData::Lit(lid) = *self.arena.get_expr(w) {
            if let Literal::Str(s) = self.arena.get_lit(lid) {
                let s = s.clone();
                let ex = self.expand_str_lit(&s);
                return self.whnf(ex);
            }
        }
        w
    }

    /// Returns true if `e` is `eagerReduce _ _` (Lean's `is_eager_reduce`).
    #[inline]
    pub(crate) fn is_eager_reduce(&self, e: ExprId) -> bool {
        let ExprData::App(f1, _) = *self.arena.get_expr(e) else { return false };
        let ExprData::App(head, _) = *self.arena.get_expr(f1) else { return false };
        let ExprData::Const(name, _) = *self.arena.get_expr(head) else { return false };
        matches!(
            self.arena.get_name(name),
            crate::arena::NameData::Str(p, s) if *p == Arena::ANONYMOUS && s.as_ref() == "eagerReduce"
        )
    }

    fn is_bool_true(&self, e: ExprId) -> bool {
        let ExprData::Const(name, lvls) = *self.arena.get_expr(e) else { return false };
        if lvls != Arena::EMPTY_LEVELS { return false; }
        let crate::arena::NameData::Str(p, s) = self.arena.get_name(name) else { return false };
        if s.as_ref() != "true" { return false; }
        matches!(
            self.arena.get_name(*p),
            crate::arena::NameData::Str(g, ps) if *g == Arena::ANONYMOUS && ps.as_ref() == "Bool"
        )
    }

    fn is_nat_zero(&self, e: ExprId) -> bool {
        match *self.arena.get_expr(e) {
            ExprData::Lit(lid) => matches!(self.arena.get_lit(lid), Literal::Nat(n) if n.is_zero()),
            ExprData::Const(name, lvls) if lvls == Arena::EMPTY_LEVELS => {
                let crate::arena::NameData::Str(p, s) = self.arena.get_name(name) else { return false };
                if s.as_ref() != "zero" { return false; }
                matches!(
                    self.arena.get_name(*p),
                    crate::arena::NameData::Str(g, ps) if *g == Arena::ANONYMOUS && ps.as_ref() == "Nat"
                )
            }
            _ => false,
        }
    }

    fn nat_pred(&mut self, e: ExprId) -> Option<ExprId> {
        match *self.arena.get_expr(e) {
            ExprData::Lit(lid) => match self.arena.get_lit(lid) {
                Literal::Nat(n) if !n.is_zero() => {
                    let pred = n.sub(&crate::nat::Nat::from_u128(1));
                    Some(self.arena.lit_nat_big(pred))
                }
                _ => None,
            },
            ExprData::App(f, a) => {
                let ExprData::Const(name, lvls) = *self.arena.get_expr(f) else { return None };
                if lvls != Arena::EMPTY_LEVELS { return None; }
                let crate::arena::NameData::Str(p, s) = self.arena.get_name(name) else { return None };
                if s.as_ref() != "succ" { return None; }
                if matches!(
                    self.arena.get_name(*p),
                    crate::arena::NameData::Str(g, ps) if *g == Arena::ANONYMOUS && ps.as_ref() == "Nat"
                ) {
                    Some(a)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Lean 4 kernel `reduce_nat`: O(1) machine evaluation of `Nat` literal primitives.
    /// Does `e` mention a local without a `let` value?
    fn has_opaque_fvar(&self, e: ExprId) -> bool {
        if !self.arena.get_expr_meta(e).has_fvar() { return false; }
        let mut stack = vec![e];
        let mut seen = crate::hash::FxHashSet::default();
        while let Some(x) = stack.pop() {
            if !self.arena.get_expr_meta(x).has_fvar() || !seen.insert(x) { continue; }
            match self.arena.get_expr(x) {
                ExprData::FVar(fv) => match self.local_value(*fv) {
                    None => return true,
                    Some(v) => stack.push(v),
                },
                ExprData::App(f, a) => { stack.push(*f); stack.push(*a); }
                ExprData::Lam { ty, body, .. } | ExprData::Pi { ty, body, .. } => { stack.push(*ty); stack.push(*body); }
                ExprData::Let { ty, val, body, .. } => { stack.push(*ty); stack.push(*val); stack.push(*body); }
                ExprData::Proj { expr, .. } => stack.push(*expr),
                _ => {}
            }
        }
        false
    }

    fn try_reduce_nat(&mut self, name: NameId, spine: &[ExprId], allow_delta: bool) -> Option<(ExprId, usize)> {
        use crate::nat::{Nat, MAX_BITS};
        let len = spine.len();
        if len == 0 { return None; }
        let crate::arena::NameData::Str(parent, seg) = self.arena.get_name(name) else { return None };
        let crate::arena::NameData::Str(gp, pseg) = self.arena.get_name(*parent) else { return None };
        if *gp != crate::arena::Arena::ANONYMOUS || pseg.as_ref() != "Nat" { return None; }
        // The operations Lean's kernel evaluates on literals (GMP there, `Nat` here).
        let op: &'static str = match seg.as_ref() {
            "succ" if allow_delta => "succ", "log2" => "log2",
            "add" => "add", "sub" => "sub", "mul" => "mul", "pow" => "pow", "div" => "div", "mod" => "mod",
            "gcd" => "gcd", "beq" => "beq", "ble" => "ble", "land" => "land", "lor" => "lor", "xor" => "xor",
            "shiftLeft" => "shiftLeft", "shiftRight" => "shiftRight",
            _ => return None,
        };
        let as_nat = |tc: &mut Self, e: ExprId| -> Option<Nat> {
            let w = tc.whnf(e);
            match *tc.arena.get_expr(w) {
                ExprData::Lit(lid) => match tc.arena.get_lit(lid) {
                    Literal::Nat(n) => Some(n.clone()),
                    _ => None,
                },
                ExprData::Const(cn, _) => match tc.arena.get_name(cn) {
                    crate::arena::NameData::Str(p, s) if s.as_ref() == "zero" => match tc.arena.get_name(*p) {
                        crate::arena::NameData::Str(g, ps) if *g == crate::arena::Arena::ANONYMOUS && ps.as_ref() == "Nat" => Some(Nat::zero()),
                        _ => None,
                    },
                    _ => None,
                },
                _ => None,
            }
        };
        // Match Lean's `whnf` vs `lazy_delta_reduction`: in `whnf` (`allow_delta == true`),
        // always try `reduce_nat` even when an argument syntactically mentions an opaque fvar
        // (e.g. `ctorIdx (C x)` drops `x` and reduces to a literal, preventing `Nat.mod` from
        // unfolding into `Nat.modCore`). In non-delta reduction, skip open args unless eager.
        let arity = if op == "succ" || op == "log2" { 1 } else { 2 };
        if len < arity
            || (!allow_delta && !self.eager_reduce && spine[len - arity..].iter().any(|&x| self.has_opaque_fvar(x)))
        {
            return None;
        }
        if op == "succ" || op == "log2" {
            let a = as_nat(self, spine[len - 1])?;
            let r = if op == "succ" { a.add(&Nat::from_u128(1)) } else { a.log2() };
            return Some((self.arena.lit_nat_big(r), 1));
        }
        if len < 2 { return None; }
        let a = as_nat(self, spine[len - 1])?;
        let b = as_nat(self, spine[len - 2])?;
        let r = match op {
            "add" => a.add(&b),
            "sub" => a.sub(&b),
            "mul" => a.mul(&b),
            "pow" => a.pow(&b)?,
            "div" => a.div(&b),
            "mod" => a.rem(&b),
            "gcd" => a.gcd(&b),
            "land" => a.land(&b),
            "lor" => a.lor(&b),
            "xor" => a.xor(&b),
            "shiftLeft" => {
                let k = b.to_u64().filter(|k| a.bits().saturating_add(*k) <= MAX_BITS)?;
                a.shl(k)
            }
            "shiftRight" => a.shr(b.to_u64().unwrap_or(u64::MAX)),
            "beq" | "ble" => {
                let res = if op == "beq" { a == b } else { a <= b };
                let p = if res { "Bool.true" } else { "Bool.false" };
                return Some((self.arena.const_path(p, []), 2));
            }
            _ => return None,
        };
        Some((self.arena.lit_nat_big(r), 2))
    }

    fn delta_info(&self, head: ExprId) -> Option<(ExprId, u64, &'a [NameId], LevelListId)> {
        let ExprData::Const(name, lvls_id) = *self.arena.get_expr(head) else { return None };
        let decl = self.decls.get(&name)?;
        let (val, prio) = decl.delta_value()?;
        let params = decl.level_params();
        if self.arena.get_level_list(lvls_id).len() != params.len() { return None; }
        Some((val, prio, params, lvls_id))
    }

    fn unfold_delta_app(&mut self, val: ExprId, params: &[NameId], lvls_id: LevelListId, args: &[ExprId]) -> ExprId {
        let inst = self.inst_levels_list(val, params, lvls_id);
        let spine: Vec<ExprId> = args.iter().rev().copied().collect();
        self.whnf_spine_with(inst, spine, false, true)
    }

    fn is_proof(&mut self, e: ExprId) -> Result<Option<ExprId>, KernelError> {
        if matches!(self.arena.get_expr(e), ExprData::Sort(_) | ExprData::Pi { .. } | ExprData::Lit(_)) {
            return Ok(None);
        }
        let prev = self.infer_only;
        self.infer_only = true;
        let r = self.infer_type(e).and_then(|ty| self.infer_sort(ty).map(|s| (ty, s)));
        self.infer_only = prev;
        let (ty, sort) = r?;
        Ok(level_is_zero(self.arena, sort).then_some(ty))
    }

    /// Definitional equality `a ≡ b` with DAG memoization.
    pub fn is_def_eq(&mut self, a: ExprId, b: ExprId) -> Result<bool, KernelError> {
        if a == b { return Ok(true); }
        let key = if a.0 <= b.0 { (a, b) } else { (b, a) };
        if self.def_eq_cache.contains(&key) { return Ok(true); }
        if self.def_neq_cache.contains(&key) { return Ok(false); }
        let eq = self.is_def_eq_core(a, b)?;
        if eq { self.def_eq_cache.insert(key); } else { self.def_neq_cache.insert(key); }
        Ok(eq)
    }

    fn is_def_eq_core(&mut self, mut a: ExprId, mut b: ExprId) -> Result<bool, KernelError> {
        if a == b { return Ok(true); }
        // Lean's reflection fast path (e.g. `decide` / `decide +kernel`): when comparing a closed
        // (or `eagerReduce`) term against `Bool.true`, reduce it directly via `whnf`.
        if self.is_bool_true(b) && (self.eager_reduce || !self.has_opaque_fvar(a)) {
            let w = self.whnf(a);
            if self.is_bool_true(w) { return Ok(true); }
        }
        if self.is_bool_true(a) && (self.eager_reduce || !self.has_opaque_fvar(b)) {
            let w = self.whnf(b);
            if self.is_bool_true(w) { return Ok(true); }
        }
        a = self.whnf_no_delta(a);
        b = self.whnf_no_delta(b);
        let mut checked_proof = false;

        loop {
            if a == b { return Ok(true); }
            match (self.arena.get_expr(a), self.arena.get_expr(b)) {
                (ExprData::Sort(u), ExprData::Sort(v)) => {
                    let (u, v) = (*u, *v);
                    return Ok(level_eq(self.arena, u, v));
                }
                (ExprData::Lit(x), ExprData::Lit(y)) => return Ok(x == y),
                (ExprData::Pi { name, binder_info, ty: t1, body: b1 }, ExprData::Pi { ty: t2, body: b2, .. }) => {
                    let (name, bi, t1, b1, t2, b2) = (*name, *binder_info, *t1, *b1, *t2, *b2);
                    if !self.is_def_eq(t1, t2)? { return Ok(false); }
                    let fv = self.push_local(name, bi, t1, None);
                    let fve = self.arena.fvar(fv);
                    let (ib1, ib2) = (instantiate1(self.arena, b1, fve), instantiate1(self.arena, b2, fve));
                    let res = self.is_def_eq(ib1, ib2);
                    self.pop_local();
                    return res;
                }
                (ExprData::Lam { name, binder_info, ty: t1, body: b1 }, ExprData::Lam { ty: t2, body: b2, .. }) => {
                    let (name, bi, t1, b1, t2, b2) = (*name, *binder_info, *t1, *b1, *t2, *b2);
                    if self.is_def_eq(t1, t2)? {
                        let fv = self.push_local(name, bi, t1, None);
                        let fve = self.arena.fvar(fv);
                        let (ib1, ib2) = (instantiate1(self.arena, b1, fve), instantiate1(self.arena, b2, fve));
                        let res = self.is_def_eq(ib1, ib2)?;
                        self.pop_local();
                        if res { return Ok(true); }
                    }
                    if !checked_proof {
                        if let (Some(ta), Some(tb)) = (self.is_proof(a)?, self.is_proof(b)?) {
                            return self.is_def_eq(ta, tb);
                        }
                    }
                    return Ok(false);
                }
                (ExprData::Lam { name, binder_info, ty, body }, _) => {
                    let (name, bi, ty, body) = (*name, *binder_info, *ty, *body);
                    if self.try_fun_eta(name, bi, ty, body, b)? { return Ok(true); }
                }
                (_, ExprData::Lam { name, binder_info, ty, body }) => {
                    let (name, bi, ty, body) = (*name, *binder_info, *ty, *body);
                    if self.try_fun_eta(name, bi, ty, body, a)? { return Ok(true); }
                }
                _ => {}
            }

            // Proof irrelevance before any structural comparison or unfolding, as in Lean's
            // `is_def_eq_core`: comparing two proofs' internals can force huge computations.
            if !checked_proof {
                checked_proof = true;
                if let (Some(ta), Some(tb)) = (self.is_proof(a)?, self.is_proof(b)?) {
                    return self.is_def_eq(ta, tb);
                }
            }

            // Lean's `is_def_eq_offset`: match `Nat` literals against `Nat.zero`/`Nat.succ`
            // without eagerly expanding literals before delta/Nat-primitive reduction.
            if self.is_nat_zero(a) && self.is_nat_zero(b) {
                return Ok(true);
            }
            if let (Some(pa), Some(pb)) = (self.nat_pred(a), self.nat_pred(b)) {
                return self.is_def_eq(pa, pb);
            }

            let (ha, args_a) = self.app_spine(a);
            let (hb, args_b) = self.app_spine(b);
            if args_a.is_empty() && args_b.is_empty() && self.heads_equal(ha, hb) {
                return Ok(true);
            }

            match (self.delta_info(ha), self.delta_info(hb)) {
                (Some((va, pa, ppa, la)), Some((vb, pb, ppb, lb))) => {
                    // Try congruence (`is_def_eq_args`) before unfolding when both sides share a
                    // head. Skip for `Abbrev`s with differing `Lam` arguments (e.g. `casesOn` /
                    // `dite`), which must unfold directly so recursors reduce on concrete
                    // scrutinees rather than comparing lambda branches under an opaque fvar.
                    if pa == pb
                        && args_a.len() == args_b.len()
                        && (pa < u64::MAX
                            || !args_a.iter().zip(&args_b).any(|(&xa, &xb)| {
                                xa != xb
                                    && (matches!(self.arena.get_expr(xa), ExprData::Lam { .. })
                                        || matches!(self.arena.get_expr(xb), ExprData::Lam { .. }))
                            }))
                        && self.heads_equal(ha, hb)
                    {
                        let mut all_eq = true;
                        for (&xa, &xb) in args_a.iter().zip(&args_b) {
                            if !self.is_def_eq(xa, xb)? { all_eq = false; break; }
                        }
                        if all_eq { return Ok(true); }
                    }
                    if pa >= pb { a = self.unfold_delta_app(va, ppa, la, &args_a); }
                    if pb >= pa { b = self.unfold_delta_app(vb, ppb, lb, &args_b); }
                }
                (Some((va, _, ppa, la)), None) => {
                    if let Some(b2) = self.try_unfold_proj_app(b) {
                        b = self.whnf_no_delta(b2);
                    } else {
                        a = self.unfold_delta_app(va, ppa, la, &args_a);
                    }
                }
                (None, Some((vb, _, ppb, lb))) => {
                    if let Some(a2) = self.try_unfold_proj_app(a) {
                        a = self.whnf_no_delta(a2);
                    } else {
                        b = self.unfold_delta_app(vb, ppb, lb, &args_b);
                    }
                }
                (None, None) => {
                    if args_a.len() == args_b.len() && self.heads_equal(ha, hb) {
                        let mut all_eq = true;
                        for (&xa, &xb) in args_a.iter().zip(&args_b) {
                            if !self.is_def_eq(xa, xb)? { all_eq = false; break; }
                        }
                        if all_eq { return Ok(true); }
                    }
                    let a2 = self.try_unfold_proj_app(a);
                    let b2 = self.try_unfold_proj_app(b);
                    if a2.is_some() || b2.is_some() {
                        if let Some(x) = a2 { a = self.whnf_no_delta(x); }
                        if let Some(x) = b2 { b = self.whnf_no_delta(x); }
                        continue;
                    }
                    if self.try_struct_eta(a, b)? || self.try_struct_eta(b, a)? {
                        return Ok(true);
                    }
                    if let ExprData::Lit(lid) = *self.arena.get_expr(a) {
                        if let Literal::Str(sv) = self.arena.get_lit(lid) {
                            let sv = sv.clone();
                            let ex = self.expand_str_lit(&sv);
                            a = self.whnf_no_delta(ex);
                            continue;
                        }
                    }
                    if let ExprData::Lit(lid) = *self.arena.get_expr(b) {
                        if let Literal::Str(sv) = self.arena.get_lit(lid) {
                            let sv = sv.clone();
                            let ex = self.expand_str_lit(&sv);
                            b = self.whnf_no_delta(ex);
                            continue;
                        }
                    }
                    return Ok(self.try_unit_like(a, b)?);
                }
            }
        }
    }

    fn try_fun_eta(&mut self, name: NameId, bi: BinderInfo, ty: ExprId, body: ExprId, other: ExprId) -> Result<bool, KernelError> {
        if matches!(self.arena.get_expr(other), ExprData::Sort(_) | ExprData::Pi { .. } | ExprData::Lit(_) | ExprData::Lam { .. }) {
            return Ok(false);
        }
        let other_ty = self.infer_type_only(other)?;
        let other_ty_w = self.whnf(other_ty);
        let ExprData::Pi { ty: dom, .. } = *self.arena.get_expr(other_ty_w) else { return Ok(false) };
        if !self.is_def_eq(ty, dom)? { return Ok(false); }
        let fv: FVarId = self.push_local(name, bi, ty, None);
        let fve = self.arena.fvar(fv);
        let (lhs, rhs) = (instantiate1(self.arena, body, fve), self.arena.app(other, fve));
        let res = self.is_def_eq(lhs, rhs);
        self.pop_local();
        res
    }

    /// Lean's `is_def_eq_unit_like`: any two terms of a non-recursive structure whose single
    /// constructor has no fields are equal (for example `Std.Rii α`), provided their types are.
    fn try_unit_like(&mut self, a: ExprId, b: ExprId) -> Result<bool, KernelError> {
        let a_ty = self.infer_type_only(a)?;
        let a_ty_w = self.whnf(a_ty);
        let (head, _) = self.app_spine(a_ty_w);
        let ExprData::Const(iname, _) = *self.arena.get_expr(head) else { return Ok(false) };
        let Some(Declaration::Inductive(ind)) = self.decls.get(&iname) else { return Ok(false) };
        if ind.is_rec || ind.ctors.len() != 1 || ind.num_indices != 0 || ind.all.len() != 1 {
            return Ok(false);
        }
        let Some(Declaration::Constructor(c)) = self.decls.get(&ind.ctors[0]) else { return Ok(false) };
        if c.num_fields != 0 {
            return Ok(false);
        }
        let b_ty = self.infer_type_only(b)?;
        self.is_def_eq(a_ty_w, b_ty)
    }

    fn try_struct_eta(&mut self, ctor_side: ExprId, other: ExprId) -> Result<bool, KernelError> {
        let (head, args) = self.app_spine(ctor_side);
        let ExprData::Const(cname, _) = *self.arena.get_expr(head) else { return Ok(false) };
        let Some(Declaration::Constructor(c)) = self.decls.get(&cname) else { return Ok(false) };
        let Some(Declaration::Inductive(ind)) = self.decls.get(&c.ind_name) else { return Ok(false) };
        if ind.is_prop || ind.is_rec || ind.ctors.len() != 1 || ind.num_indices != 0 || ind.all.len() != 1
            || args.len() != (c.num_params + c.num_fields) as usize
        {
            return Ok(false);
        }
        let other_ty = self.infer_type_only(other)?;
        let other_ty_w = self.whnf(other_ty);
        let (ohead, oargs) = self.app_spine(other_ty_w);
        if !matches!(self.arena.get_expr(ohead), ExprData::Const(n, _) if *n == ind.name && oargs.len() == ind.num_params as usize) {
            return Ok(false);
        }
        for fi in 0..c.num_fields {
            let rhs = self.arena.proj(ind.name, fi, other);
            if !self.is_def_eq(args[c.num_params as usize + fi as usize], rhs)? { return Ok(false); }
        }
        Ok(true)
    }

    fn heads_equal(&mut self, ha: ExprId, hb: ExprId) -> bool {
        if ha == hb { return true; }
        match (*self.arena.get_expr(ha), *self.arena.get_expr(hb)) {
            (ExprData::Const(na, la), ExprData::Const(nb, lb)) if na == nb => {
                if la == lb { return true; }
                let (sa, sb) = (self.arena.get_level_list(la), self.arena.get_level_list(lb));
                if sa.len() != sb.len() { return false; }
                let (la, lb): (Box<[LevelId]>, Box<[LevelId]>) = (sa.into(), sb.into());
                la.iter().zip(lb.iter()).all(|(&x, &y)| level_eq(self.arena, x, y))
            }
            (ExprData::Proj { struct_name: sa, idx: ia, expr: ea }, ExprData::Proj { struct_name: sb, idx: ib, expr: eb })
                if sa == sb && ia == ib =>
            {
                self.is_def_eq(ea, eb).unwrap_or(false)
            }
            _ => false,
        }
    }
}


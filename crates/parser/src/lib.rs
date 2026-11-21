//! Streaming, zero-copy-token parser for Lean 4's `lean4export` text format.
//!
//! Supports all 22 `lean4export` directives (`#NS`, `#NI`, `#US`, `#UM`, `#UIM`, `#UP`,
//! `#EV`, `#ES`, `#EC`, `#EA`, `#EL`, `#EP`, `#EZ`, `#EJ`, `#ELN`, `#ELS`,
//! `#AX`, `#DEF`, `#THM`, `#OPAQ`, `#QUOT`, `#IND`), plus mutual `#INDM` and
//! `lean4export` v3 `#IND`/`#CTOR`/`#REC` blocks (always validated by Rigor's kernel
//! rather than trusting exported recursor rules).

#![forbid(unsafe_code)]

use std::fmt;
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::path::Path;

mod ndjson;

pub use rigor_kernel as kernel;

use rigor_kernel::{
    Arena, BinderInfo, Declaration, Environment, ExprId, InductiveSpec, InductiveTypeSpec,
    KernelError, LevelId, NameId, ReducibilityHint,
};

#[derive(Debug)]
pub enum ParseError {
    Io(std::io::Error),
    Syntax { line: usize, message: String },
    UnknownNameId { line: usize, id: usize },
    UnknownLevelId { line: usize, id: usize },
    UnknownExprId { line: usize, id: usize },
    InvalidUtf8 { line: usize },
    Kernel { line: usize, err: KernelError },
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParseError::Io(e) => write!(f, "I/O error: {e}"),
            ParseError::Syntax { line, message } => write!(f, "line {line}: syntax error: {message}"),
            ParseError::UnknownNameId { line, id } => write!(f, "line {line}: undefined name id {id}"),
            ParseError::UnknownLevelId { line, id } => write!(f, "line {line}: undefined level id {id}"),
            ParseError::UnknownExprId { line, id } => write!(f, "line {line}: undefined expr id {id}"),
            ParseError::InvalidUtf8 { line } => write!(f, "line {line}: invalid UTF-8 in #ELS literal"),
            ParseError::Kernel { line, err } => write!(f, "line {line}: kernel rejected declaration: {err}"),
        }
    }
}

impl std::error::Error for ParseError {}

impl From<std::io::Error> for ParseError {
    fn from(e: std::io::Error) -> Self {
        ParseError::Io(e)
    }
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct ParseStats {
    pub version: Option<String>,
    pub lines: usize,
    pub names: usize,
    pub levels: usize,
    pub exprs: usize,
    pub axioms: usize,
    pub defs: usize,
    pub theorems: usize,
    pub opaques: usize,
    pub inductives: usize,
    pub quots: usize,
}

impl ParseStats {
    #[inline]
    pub fn total_decls(&self) -> usize {
        self.axioms + self.defs + self.theorems + self.opaques + self.inductives + self.quots
    }
}

/// Pending state for `lean4export` v3 multi-line `#IND` + `#CTOR` blocks.
struct PendingV3Ind {
    line: usize,
    level_params: Box<[NameId]>,
    num_params: u32,
    expected_all: Vec<NameId>,
    expected_ctors: Vec<(NameId, Vec<NameId>)>,
    types: Vec<(NameId, ExprId)>,
    ctors: Vec<(NameId, NameId, ExprId)>,
}

impl PendingV3Ind {
    fn is_ready(&self) -> bool {
        let total_expected_ctors: usize = self.expected_ctors.iter().map(|(_, cs)| cs.len()).sum();
        self.types.len() == self.expected_all.len() && self.ctors.len() == total_expected_ctors
    }

    fn flush(self, env: &mut Environment) -> Result<(), ParseError> {
        let mut type_specs = Vec::with_capacity(self.expected_all.len());
        for &ind_name in &self.expected_all {
            let ty = self
                .types
                .iter()
                .find(|(n, _)| *n == ind_name)
                .map(|(_, t)| *t)
                .ok_or_else(|| ParseError::Syntax {
                    line: self.line,
                    message: "incomplete v3 mutual inductive block (missing #IND)".into(),
                })?;
            let expected_cs = self
                .expected_ctors
                .iter()
                .find(|(n, _)| *n == ind_name)
                .map(|(_, cs)| cs.as_slice())
                .unwrap_or(&[]);
            let mut ctors = Vec::with_capacity(expected_cs.len());
            for &cn in expected_cs {
                let cty = self
                    .ctors
                    .iter()
                    .find(|(n, ind, _)| *n == cn && *ind == ind_name)
                    .map(|(_, _, t)| *t)
                    .ok_or_else(|| ParseError::Syntax {
                        line: self.line,
                        message: "incomplete v3 inductive block (missing #CTOR)".into(),
                    })?;
                ctors.push((cn, cty));
            }
            type_specs.push(InductiveTypeSpec {
                name: ind_name,
                ty,
                ctors,
            });
        }
        let spec = InductiveSpec {
            level_params: self.level_params,
            num_params: self.num_params,
            types: type_specs,
        };
        env.add_inductive(spec)
            .map_err(|err| ParseError::Kernel { line: self.line, err })
    }
}

/// Streaming parser state mapping `lean4export` integer IDs directly into Rigor's hash-consed arena.
pub struct StreamParser {
    pub(crate) names: Vec<Option<NameId>>,
    pub(crate) levels: Vec<Option<LevelId>>,
    pub(crate) exprs: Vec<Option<ExprId>>,
    pub(crate) stats: ParseStats,
    v3_mode: bool,
    ndjson_mode: bool,
    pending_ind: Option<PendingV3Ind>,
}

impl Default for StreamParser {
    fn default() -> Self {
        Self::new()
    }
}

impl StreamParser {
    pub fn new() -> Self {
        let mut names = Vec::with_capacity(1024);
        names.push(Some(Arena::ANONYMOUS));
        let mut levels = Vec::with_capacity(256);
        levels.push(Some(Arena::LEVEL_ZERO));
        Self {
            names,
            levels,
            exprs: Vec::with_capacity(4096),
            stats: ParseStats::default(),
            v3_mode: false,
            ndjson_mode: false,
            pending_ind: None,
        }
    }

    /// Stream-parse and verify all declarations from `reader` into `env`.
    pub fn parse_reader<R: BufRead>(
        mut self,
        mut reader: R,
        env: &mut Environment,
    ) -> Result<ParseStats, ParseError> {
        let mut buf = String::with_capacity(256);
        let mut line_no = 0usize;
        let mut saw_content = false;

        loop {
            buf.clear();
            let n = reader.read_line(&mut buf)?;
            if n == 0 {
                break;
            }
            line_no += 1;
            self.stats.lines = line_no;

            let line = buf.trim_end_matches(['\r', '\n']);
            let trimmed = line.trim_start_matches([' ', '\t']);
            if trimmed.is_empty() || trimmed.starts_with("--") || trimmed.starts_with("//") {
                continue;
            }

            if !saw_content {
                saw_content = true;
                if trimmed.starts_with('{') {
                    self.ndjson_mode = true;
                } else if is_version_header(trimmed) {
                    self.v3_mode = trimmed.starts_with("3.");
                    self.stats.version = Some(trimmed.to_owned());
                    continue;
                }
            }

            if self.ndjson_mode {
                self.parse_ndjson_line(line_no, trimmed, env)?;
            } else {
                self.parse_line(line_no, trimmed, env)?;
            }
        }

        if let Some(pending) = self.pending_ind.take() {
            pending.flush(env)?;
            self.stats.inductives += 1;
        }
        Ok(self.stats)
    }

    fn flush_pending_if_needed(&mut self, env: &mut Environment) -> Result<(), ParseError> {
        if let Some(pending) = self.pending_ind.take() {
            pending.flush(env)?;
            self.stats.inductives += 1;
        }
        Ok(())
    }

    fn parse_line(&mut self, line: usize, text: &str, env: &mut Environment) -> Result<(), ParseError> {
        if text.starts_with('#') {
            return self.parse_decl_line(line, text, env);
        }

        // Indexed item: `<id> #<TAG> ...`
        let (id_tok, rest) = split_first_ws(text).ok_or_else(|| syntax(line, "expected item id"))?;
        let id = parse_usize(line, id_tok, "item id")?;
        let (tag, after_tag) = split_first_ws(rest).ok_or_else(|| syntax(line, "expected directive tag"))?;

        match tag {
            "#NS" => {
                // `<id> #NS <parent_id> <string_segment>` (rest of line after single space)
                let (p_tok, seg) = split_parent_and_str(after_tag)
                    .ok_or_else(|| syntax(line, "#NS expects <parent> <str>"))?;
                let pid = self.get_name(line, parse_usize(line, p_tok, "parent name id")?)?;
                let nid = env.arena.name_str(pid, seg);
                set_slot(&mut self.names, id, nid);
                self.stats.names += 1;
            }
            "#NI" => {
                let mut it = after_tag.split_ascii_whitespace();
                let pid = self.next_name(line, &mut it, "parent name id")?;
                let num = parse_u64(line, next_tok(line, &mut it, "#NI number")?, "#NI number")?;
                expect_end(line, &mut it, "#NI")?;
                let nid = env.arena.name_num(pid, num);
                set_slot(&mut self.names, id, nid);
                self.stats.names += 1;
            }
            "#US" => {
                let mut it = after_tag.split_ascii_whitespace();
                let l = self.next_level(line, &mut it, "#US level")?;
                expect_end(line, &mut it, "#US")?;
                let lid = env.arena.lvl_succ(l);
                set_slot(&mut self.levels, id, lid);
                self.stats.levels += 1;
            }
            "#UM" => {
                let mut it = after_tag.split_ascii_whitespace();
                let l1 = self.next_level(line, &mut it, "#UM lhs")?;
                let l2 = self.next_level(line, &mut it, "#UM rhs")?;
                expect_end(line, &mut it, "#UM")?;
                let lid = env.arena.lvl_max(l1, l2);
                set_slot(&mut self.levels, id, lid);
                self.stats.levels += 1;
            }
            "#UIM" => {
                let mut it = after_tag.split_ascii_whitespace();
                let l1 = self.next_level(line, &mut it, "#UIM lhs")?;
                let l2 = self.next_level(line, &mut it, "#UIM rhs")?;
                expect_end(line, &mut it, "#UIM")?;
                let lid = env.arena.lvl_imax(l1, l2);
                set_slot(&mut self.levels, id, lid);
                self.stats.levels += 1;
            }
            "#UP" => {
                let mut it = after_tag.split_ascii_whitespace();
                let nm = self.next_name(line, &mut it, "#UP name")?;
                expect_end(line, &mut it, "#UP")?;
                let lid = env.arena.lvl_param(nm);
                set_slot(&mut self.levels, id, lid);
                self.stats.levels += 1;
            }
            "#EV" => {
                let mut it = after_tag.split_ascii_whitespace();
                let idx = parse_u32(line, next_tok(line, &mut it, "#EV index")?, "#EV index")?;
                expect_end(line, &mut it, "#EV")?;
                let eid = env.arena.bvar(idx);
                set_slot(&mut self.exprs, id, eid);
                self.stats.exprs += 1;
            }
            "#ES" => {
                let mut it = after_tag.split_ascii_whitespace();
                let l = self.next_level(line, &mut it, "#ES level")?;
                expect_end(line, &mut it, "#ES")?;
                let eid = env.arena.sort(l);
                set_slot(&mut self.exprs, id, eid);
                self.stats.exprs += 1;
            }
            "#EC" => {
                let mut it = after_tag.split_ascii_whitespace();
                let nm = self.next_name(line, &mut it, "#EC name")?;
                let mut lvls = Vec::new();
                for tok in it {
                    lvls.push(self.get_level(line, parse_usize(line, tok, "#EC level")?)?);
                }
                let eid = env.arena.const_(nm, lvls);
                set_slot(&mut self.exprs, id, eid);
                self.stats.exprs += 1;
            }
            "#EA" => {
                let mut it = after_tag.split_ascii_whitespace();
                let f = self.next_expr(line, &mut it, "#EA fn")?;
                let a = self.next_expr(line, &mut it, "#EA arg")?;
                expect_end(line, &mut it, "#EA")?;
                let eid = env.arena.app(f, a);
                set_slot(&mut self.exprs, id, eid);
                self.stats.exprs += 1;
            }
            "#EL" => {
                let mut it = after_tag.split_ascii_whitespace();
                let bi = parse_binder_info(line, next_tok(line, &mut it, "#EL binder info")?)?;
                let nm = self.next_name(line, &mut it, "#EL name")?;
                let ty = self.next_expr(line, &mut it, "#EL type")?;
                let body = self.next_expr(line, &mut it, "#EL body")?;
                expect_end(line, &mut it, "#EL")?;
                let eid = env.arena.lam(nm, bi, ty, body);
                set_slot(&mut self.exprs, id, eid);
                self.stats.exprs += 1;
            }
            "#EP" => {
                let mut it = after_tag.split_ascii_whitespace();
                let bi = parse_binder_info(line, next_tok(line, &mut it, "#EP binder info")?)?;
                let nm = self.next_name(line, &mut it, "#EP name")?;
                let ty = self.next_expr(line, &mut it, "#EP type")?;
                let body = self.next_expr(line, &mut it, "#EP body")?;
                expect_end(line, &mut it, "#EP")?;
                let eid = env.arena.pi(nm, bi, ty, body);
                set_slot(&mut self.exprs, id, eid);
                self.stats.exprs += 1;
            }
            "#EZ" => {
                let mut it = after_tag.split_ascii_whitespace();
                let nm = self.next_name(line, &mut it, "#EZ name")?;
                let ty = self.next_expr(line, &mut it, "#EZ type")?;
                let val = self.next_expr(line, &mut it, "#EZ val")?;
                let body = self.next_expr(line, &mut it, "#EZ body")?;
                expect_end(line, &mut it, "#EZ")?;
                let eid = env.arena.let_(nm, ty, val, body);
                set_slot(&mut self.exprs, id, eid);
                self.stats.exprs += 1;
            }
            "#EJ" => {
                let mut it = after_tag.split_ascii_whitespace();
                let sname = self.next_name(line, &mut it, "#EJ struct name")?;
                let idx = parse_u32(line, next_tok(line, &mut it, "#EJ field idx")?, "#EJ field idx")?;
                let expr = self.next_expr(line, &mut it, "#EJ expr")?;
                expect_end(line, &mut it, "#EJ")?;
                let eid = env.arena.proj(sname, idx, expr);
                set_slot(&mut self.exprs, id, eid);
                self.stats.exprs += 1;
            }
            "#ELN" => {
                let mut it = after_tag.split_ascii_whitespace();
                let n = parse_u128(line, next_tok(line, &mut it, "#ELN nat")?, "#ELN nat")?;
                expect_end(line, &mut it, "#ELN")?;
                let eid = env.arena.lit_nat(n);
                set_slot(&mut self.exprs, id, eid);
                self.stats.exprs += 1;
            }
            "#ELS" => {
                let mut bytes = Vec::new();
                for tok in after_tag.split_ascii_whitespace() {
                    let b = u8::from_str_radix(tok, 16)
                        .map_err(|_| syntax(line, &format!("invalid hex byte '{tok}' in #ELS")))?;
                    bytes.push(b);
                }
                let s = std::str::from_utf8(&bytes).map_err(|_| ParseError::InvalidUtf8 { line })?;
                let eid = env.arena.lit_str(s);
                set_slot(&mut self.exprs, id, eid);
                self.stats.exprs += 1;
            }
            other => {
                return Err(syntax(line, &format!("unknown indexed directive '{other}'")));
            }
        }
        Ok(())
    }

    fn parse_decl_line(&mut self, line: usize, text: &str, env: &mut Environment) -> Result<(), ParseError> {
        let mut it = text.split_ascii_whitespace();
        let tag = it.next().ok_or_else(|| syntax(line, "empty declaration line"))?;

        if !matches!(tag, "#IND" | "#CTOR") {
            self.flush_pending_if_needed(env)?;
        }

        match tag {
            "#AX" => {
                let name = self.next_name(line, &mut it, "#AX name")?;
                let ty = self.next_expr(line, &mut it, "#AX type")?;
                let level_params = self.collect_name_list(line, &mut it)?;
                env.add_decl(Declaration::Axiom { name, level_params, ty })
                    .map_err(|err| ParseError::Kernel { line, err })?;
                self.stats.axioms += 1;
            }
            "#DEF" => {
                let name = self.next_name(line, &mut it, "#DEF name")?;
                let ty = self.next_expr(line, &mut it, "#DEF type")?;
                let val = self.next_expr(line, &mut it, "#DEF val")?;
                let hint = parse_hint(line, &mut it)?;
                let level_params = self.collect_name_list(line, &mut it)?;
                env.add_decl(Declaration::Definition {
                    name,
                    level_params,
                    ty,
                    val,
                    hint,
                })
                .map_err(|err| ParseError::Kernel { line, err })?;
                self.stats.defs += 1;
            }
            "#THM" => {
                let name = self.next_name(line, &mut it, "#THM name")?;
                let ty = self.next_expr(line, &mut it, "#THM type")?;
                let val = self.next_expr(line, &mut it, "#THM val")?;
                let level_params = self.collect_name_list(line, &mut it)?;
                env.add_decl(Declaration::Theorem {
                    name,
                    level_params,
                    ty,
                    val,
                })
                .map_err(|err| ParseError::Kernel { line, err })?;
                self.stats.theorems += 1;
            }
            "#OPAQ" => {
                let name = self.next_name(line, &mut it, "#OPAQ name")?;
                let ty = self.next_expr(line, &mut it, "#OPAQ type")?;
                let val = self.next_expr(line, &mut it, "#OPAQ val")?;
                let level_params = self.collect_name_list(line, &mut it)?;
                env.add_decl(Declaration::Opaque {
                    name,
                    level_params,
                    ty,
                    val,
                })
                .map_err(|err| ParseError::Kernel { line, err })?;
                self.stats.opaques += 1;
            }
            "#QUOT" => {
                expect_end(line, &mut it, "#QUOT")?;
                env.add_quot()
                    .map_err(|err| ParseError::Kernel { line, err })?;
                self.stats.quots += 1;
            }
            "#IND" => {
                if self.v3_mode {
                    self.parse_v3_ind(line, &mut it, env)?;
                } else {
                    self.flush_pending_if_needed(env)?;
                    self.parse_classic_ind(line, &mut it, env)?;
                }
            }
            "#INDM" => {
                self.flush_pending_if_needed(env)?;
                self.parse_mutual_ind(line, &mut it, env)?;
            }
            "#CTOR" => {
                self.parse_v3_ctor(line, &mut it, env)?;
            }
            "#REC" => {
                // Never trust exported recursor rules; verify the kernel generated a matching recursor.
                let name = self.next_name(line, &mut it, "#REC name")?;
                let _ty = self.next_expr(line, &mut it, "#REC type")?;
                if !matches!(env.get(name), Some(Declaration::Recursor(_))) {
                    return Err(ParseError::Kernel {
                        line,
                        err: KernelError::UnknownConstant(name),
                    });
                }
            }
            other => {
                return Err(syntax(line, &format!("unknown declaration directive '{other}'")));
            }
        }
        Ok(())
    }

    fn parse_classic_ind(
        &mut self,
        line: usize,
        it: &mut std::str::SplitAsciiWhitespace<'_>,
        env: &mut Environment,
    ) -> Result<(), ParseError> {
        let num_params = parse_u32(line, next_tok(line, it, "#IND num_params")?, "#IND num_params")?;
        let name = self.next_name(line, it, "#IND name")?;
        let ty = self.next_expr(line, it, "#IND type")?;
        let num_ctors = parse_usize(line, next_tok(line, it, "#IND num_ctors")?, "#IND num_ctors")?;
        let mut ctors = Vec::with_capacity(num_ctors);
        for _ in 0..num_ctors {
            let cn = self.next_name(line, it, "#IND ctor name")?;
            let cty = self.next_expr(line, it, "#IND ctor type")?;
            ctors.push((cn, cty));
        }
        let level_params = self.collect_name_list(line, it)?;
        env.add_inductive(InductiveSpec {
            level_params,
            num_params,
            types: vec![InductiveTypeSpec { name, ty, ctors }],
        })
        .map_err(|err| ParseError::Kernel { line, err })?;
        self.stats.inductives += 1;
        Ok(())
    }

    fn parse_mutual_ind(
        &mut self,
        line: usize,
        it: &mut std::str::SplitAsciiWhitespace<'_>,
        env: &mut Environment,
    ) -> Result<(), ParseError> {
        let num_params = parse_u32(line, next_tok(line, it, "#INDM num_params")?, "#INDM num_params")?;
        let num_types = parse_usize(line, next_tok(line, it, "#INDM num_types")?, "#INDM num_types")?;
        let mut types = Vec::with_capacity(num_types);
        for _ in 0..num_types {
            let name = self.next_name(line, it, "#INDM type name")?;
            let ty = self.next_expr(line, it, "#INDM type")?;
            let num_ctors = parse_usize(line, next_tok(line, it, "#INDM num_ctors")?, "#INDM num_ctors")?;
            let mut ctors = Vec::with_capacity(num_ctors);
            for _ in 0..num_ctors {
                let cn = self.next_name(line, it, "#INDM ctor name")?;
                let cty = self.next_expr(line, it, "#INDM ctor type")?;
                ctors.push((cn, cty));
            }
            types.push(InductiveTypeSpec { name, ty, ctors });
        }
        let level_params = self.collect_name_list(line, it)?;
        env.add_inductive(InductiveSpec {
            level_params,
            num_params,
            types,
        })
        .map_err(|err| ParseError::Kernel { line, err })?;
        self.stats.inductives += 1;
        Ok(())
    }

    fn parse_v3_ind(
        &mut self,
        line: usize,
        it: &mut std::str::SplitAsciiWhitespace<'_>,
        env: &mut Environment,
    ) -> Result<(), ParseError> {
        // `#IND <name> <ty> <is_rec> <is_nested> <num_params> <num_indices> <num_all> <all>* <num_ctors> <ctor>* <is_unsafe> <uparam>*`
        let name = self.next_name(line, it, "v3 #IND name")?;
        let ty = self.next_expr(line, it, "v3 #IND type")?;
        let _is_rec = parse_u32(line, next_tok(line, it, "v3 #IND is_rec")?, "is_rec")?;
        let _is_nested = parse_u32(line, next_tok(line, it, "v3 #IND is_nested")?, "is_nested")?;
        let num_params = parse_u32(line, next_tok(line, it, "v3 #IND num_params")?, "num_params")?;
        let _num_indices = parse_u32(line, next_tok(line, it, "v3 #IND num_indices")?, "num_indices")?;
        let num_all = parse_usize(line, next_tok(line, it, "v3 #IND num_all")?, "num_all")?;
        let mut all = Vec::with_capacity(num_all);
        for _ in 0..num_all {
            all.push(self.next_name(line, it, "v3 #IND all member")?);
        }
        let num_ctors = parse_usize(line, next_tok(line, it, "v3 #IND num_ctors")?, "num_ctors")?;
        let mut ctor_names = Vec::with_capacity(num_ctors);
        for _ in 0..num_ctors {
            ctor_names.push(self.next_name(line, it, "v3 #IND ctor name")?);
        }
        let is_unsafe = parse_u32(line, next_tok(line, it, "v3 #IND is_unsafe")?, "is_unsafe")?;
        if is_unsafe != 0 {
            return Err(syntax(line, "unsafe inductives are rejected by Rigor's sound kernel"));
        }
        let level_params = self.collect_name_list(line, it)?;

        if let Some(p) = &mut self.pending_ind {
            if p.expected_all != all {
                let prev = self.pending_ind.take().unwrap();
                prev.flush(env)?;
                self.stats.inductives += 1;
            }
        }
        let p = self.pending_ind.get_or_insert_with(|| PendingV3Ind {
            line,
            level_params,
            num_params,
            expected_all: all,
            expected_ctors: Vec::new(),
            types: Vec::new(),
            ctors: Vec::new(),
        });
        p.expected_ctors.push((name, ctor_names));
        p.types.push((name, ty));
        if p.is_ready() {
            let ready = self.pending_ind.take().unwrap();
            ready.flush(env)?;
            self.stats.inductives += 1;
        }
        Ok(())
    }

    fn parse_v3_ctor(
        &mut self,
        line: usize,
        it: &mut std::str::SplitAsciiWhitespace<'_>,
        env: &mut Environment,
    ) -> Result<(), ParseError> {
        // `#CTOR <name> <ty> <ind_name> <cidx> <num_params> <num_fields> <is_unsafe> <uparam>*`
        let name = self.next_name(line, it, "#CTOR name")?;
        let ty = self.next_expr(line, it, "#CTOR type")?;
        let ind_name = self.next_name(line, it, "#CTOR ind_name")?;
        let _cidx = parse_u32(line, next_tok(line, it, "#CTOR cidx")?, "#CTOR cidx")?;
        let _np = parse_u32(line, next_tok(line, it, "#CTOR num_params")?, "#CTOR num_params")?;
        let _nf = parse_u32(line, next_tok(line, it, "#CTOR num_fields")?, "#CTOR num_fields")?;
        let is_unsafe = parse_u32(line, next_tok(line, it, "#CTOR is_unsafe")?, "#CTOR is_unsafe")?;
        if is_unsafe != 0 {
            return Err(syntax(line, "unsafe constructors are rejected by Rigor's sound kernel"));
        }
        let _uparams = self.collect_name_list(line, it)?;

        let p = self.pending_ind.as_mut().ok_or_else(|| {
            syntax(line, "#CTOR encountered without preceding v3 #IND")
        })?;
        p.ctors.push((name, ind_name, ty));
        if p.is_ready() {
            let ready = self.pending_ind.take().unwrap();
            ready.flush(env)?;
            self.stats.inductives += 1;
        }
        Ok(())
    }

    #[inline]
    pub(crate) fn get_name(&self, line: usize, id: usize) -> Result<NameId, ParseError> {
        self.names
            .get(id)
            .and_then(|o| *o)
            .ok_or(ParseError::UnknownNameId { line, id })
    }

    #[inline]
    pub(crate) fn get_level(&self, line: usize, id: usize) -> Result<LevelId, ParseError> {
        self.levels
            .get(id)
            .and_then(|o| *o)
            .ok_or(ParseError::UnknownLevelId { line, id })
    }

    #[inline]
    pub(crate) fn get_expr(&self, line: usize, id: usize) -> Result<ExprId, ParseError> {
        self.exprs
            .get(id)
            .and_then(|o| *o)
            .ok_or(ParseError::UnknownExprId { line, id })
    }

    fn next_name(
        &self,
        line: usize,
        it: &mut std::str::SplitAsciiWhitespace<'_>,
        what: &str,
    ) -> Result<NameId, ParseError> {
        let tok = next_tok(line, it, what)?;
        self.get_name(line, parse_usize(line, tok, what)?)
    }

    fn next_level(
        &self,
        line: usize,
        it: &mut std::str::SplitAsciiWhitespace<'_>,
        what: &str,
    ) -> Result<LevelId, ParseError> {
        let tok = next_tok(line, it, what)?;
        self.get_level(line, parse_usize(line, tok, what)?)
    }

    fn next_expr(
        &self,
        line: usize,
        it: &mut std::str::SplitAsciiWhitespace<'_>,
        what: &str,
    ) -> Result<ExprId, ParseError> {
        let tok = next_tok(line, it, what)?;
        self.get_expr(line, parse_usize(line, tok, what)?)
    }

    fn collect_name_list(
        &self,
        line: usize,
        it: &mut std::str::SplitAsciiWhitespace<'_>,
    ) -> Result<Box<[NameId]>, ParseError> {
        let mut out = Vec::new();
        for tok in it {
            out.push(self.get_name(line, parse_usize(line, tok, "universe param name id")?)?);
        }
        Ok(out.into_boxed_slice())
    }
}

/// Stream-parse and verify a `lean4export` stream into an existing `Environment`.
pub fn parse_and_check<R: BufRead>(
    reader: R,
    env: &mut Environment,
) -> Result<ParseStats, ParseError> {
    StreamParser::new().parse_reader(reader, env)
}

/// Parse and verify an in-memory `lean4export` string into a fresh `Environment`.
pub fn parse_str(input: &str) -> Result<(Environment, ParseStats), ParseError> {
    let mut env = Environment::new();
    let stats = parse_and_check(input.as_bytes(), &mut env)?;
    Ok((env, stats))
}

/// Stream-parse and verify a `lean4export` file from disk using a 64 KiB buffered reader.
pub fn parse_file(
    path: impl AsRef<Path>,
    env: &mut Environment,
) -> Result<ParseStats, ParseError> {
    let file = File::open(path)?;
    let reader = BufReader::with_capacity(64 * 1024, file);
    parse_and_check(reader, env)
}

#[inline]
pub(crate) fn set_slot<T: Copy>(table: &mut Vec<Option<T>>, id: usize, val: T) {
    if id >= table.len() {
        table.resize(id + 1, None);
    }
    table[id] = Some(val);
}

pub(crate) fn syntax(line: usize, msg: &str) -> ParseError {
    ParseError::Syntax {
        line,
        message: msg.to_owned(),
    }
}

fn is_version_header(s: &str) -> bool {
    let mut parts = 0usize;
    for part in s.split('.') {
        if part.is_empty() || !part.bytes().all(|b| b.is_ascii_digit()) {
            return false;
        }
        parts += 1;
    }
    parts >= 2
}

fn split_first_ws(s: &str) -> Option<(&str, &str)> {
    let bytes = s.as_bytes();
    let mut i = 0;
    while i < bytes.len() && !bytes[i].is_ascii_whitespace() {
        i += 1;
    }
    if i == 0 {
        return None;
    }
    let head = &s[..i];
    let mut j = i;
    while j < bytes.len() && bytes[j].is_ascii_whitespace() {
        j += 1;
    }
    Some((head, &s[j..]))
}

fn split_parent_and_str(s: &str) -> Option<(&str, &str)> {
    let bytes = s.as_bytes();
    let mut i = 0;
    while i < bytes.len() && !bytes[i].is_ascii_whitespace() {
        i += 1;
    }
    if i == 0 {
        return None;
    }
    let parent = &s[..i];
    if i < bytes.len() && bytes[i] == b' ' {
        Some((parent, &s[i + 1..]))
    } else if i == bytes.len() {
        Some((parent, ""))
    } else {
        Some((parent, s[i..].trim_start()))
    }
}

fn next_tok<'a>(
    line: usize,
    it: &mut std::str::SplitAsciiWhitespace<'a>,
    what: &str,
) -> Result<&'a str, ParseError> {
    it.next()
        .ok_or_else(|| syntax(line, &format!("missing {what}")))
}

fn expect_end(
    line: usize,
    it: &mut std::str::SplitAsciiWhitespace<'_>,
    tag: &str,
) -> Result<(), ParseError> {
    if let Some(extra) = it.next() {
        return Err(syntax(
            line,
            &format!("unexpected trailing token '{extra}' in {tag}"),
        ));
    }
    Ok(())
}

fn parse_usize(line: usize, tok: &str, what: &str) -> Result<usize, ParseError> {
    tok.parse::<usize>()
        .map_err(|_| syntax(line, &format!("invalid integer '{tok}' for {what}")))
}

fn parse_u32(line: usize, tok: &str, what: &str) -> Result<u32, ParseError> {
    tok.parse::<u32>()
        .map_err(|_| syntax(line, &format!("invalid u32 '{tok}' for {what}")))
}

fn parse_u64(line: usize, tok: &str, what: &str) -> Result<u64, ParseError> {
    tok.parse::<u64>()
        .map_err(|_| syntax(line, &format!("invalid u64 '{tok}' for {what}")))
}

fn parse_u128(line: usize, tok: &str, what: &str) -> Result<u128, ParseError> {
    tok.parse::<u128>()
        .map_err(|_| syntax(line, &format!("invalid u128 '{tok}' for {what}")))
}

fn parse_binder_info(line: usize, tok: &str) -> Result<BinderInfo, ParseError> {
    match tok {
        "#BD" => Ok(BinderInfo::Default),
        "#BI" => Ok(BinderInfo::Implicit),
        "#BS" => Ok(BinderInfo::StrictImplicit),
        "#BC" => Ok(BinderInfo::InstImplicit),
        other => Err(syntax(line, &format!("unknown binder info '{other}'"))),
    }
}

fn parse_hint(
    line: usize,
    it: &mut std::str::SplitAsciiWhitespace<'_>,
) -> Result<ReducibilityHint, ParseError> {
    let tok = next_tok(line, it, "#DEF hint")?;
    match tok {
        "O" => Ok(ReducibilityHint::Opaque),
        "A" => Ok(ReducibilityHint::Abbrev),
        "R" => {
            let h = parse_u32(line, next_tok(line, it, "#DEF regular height")?, "#DEF height")?;
            Ok(ReducibilityHint::Regular(h))
        }
        other => {
            if let Ok(h) = other.parse::<u32>() {
                Ok(ReducibilityHint::Regular(h))
            } else {
                Err(syntax(line, &format!("invalid #DEF hint '{other}'")))
            }
        }
    }
}

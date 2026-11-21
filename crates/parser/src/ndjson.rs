//! Streaming zero-dependency parser for Lean 4's `lean4export` v3.1.0 NDJSON format.

use std::borrow::Cow;

use rigor_kernel::{
    BinderInfo, Declaration, Environment, InductiveSpec, InductiveTypeSpec, NameId,
    ReducibilityHint,
};

use crate::{set_slot, syntax, ParseError, ParseStats, StreamParser};

#[derive(Debug)]
enum JVal<'a> {
    Null,
    Bool(bool),
    Int(u64),
    Str(Cow<'a, str>),
    Arr(Vec<JVal<'a>>),
    Obj(Vec<(Cow<'a, str>, JVal<'a>)>),
}

impl<'a> JVal<'a> {
    fn as_obj(&self, line: usize, what: &str) -> Result<&[(Cow<'a, str>, JVal<'a>)], ParseError> {
        match self {
            JVal::Obj(v) => Ok(v),
            _ => Err(syntax(line, &format!("expected JSON object for {what}"))),
        }
    }
    fn as_arr(&self, line: usize, what: &str) -> Result<&[JVal<'a>], ParseError> {
        match self {
            JVal::Arr(v) => Ok(v),
            _ => Err(syntax(line, &format!("expected JSON array for {what}"))),
        }
    }
    fn as_u64(&self, line: usize, what: &str) -> Result<u64, ParseError> {
        match self {
            JVal::Int(n) => Ok(*n),
            _ => Err(syntax(line, &format!("expected integer for {what}"))),
        }
    }
    fn as_usize(&self, line: usize, what: &str) -> Result<usize, ParseError> {
        self.as_u64(line, what).map(|n| n as usize)
    }
    fn as_u32(&self, line: usize, what: &str) -> Result<u32, ParseError> {
        self.as_u64(line, what).map(|n| n as u32)
    }
    fn as_str(&self, line: usize, what: &str) -> Result<&str, ParseError> {
        match self {
            JVal::Str(s) => Ok(s.as_ref()),
            _ => Err(syntax(line, &format!("expected string for {what}"))),
        }
    }
    fn as_bool(&self, line: usize, what: &str) -> Result<bool, ParseError> {
        match self {
            JVal::Bool(b) => Ok(*b),
            _ => Err(syntax(line, &format!("expected boolean for {what}"))),
        }
    }
    fn field(&self, key: &str) -> Option<&JVal<'a>> {
        if let JVal::Obj(entries) = self {
            for (k, v) in entries {
                if k.as_ref() == key {
                    return Some(v);
                }
            }
        }
        None
    }
    fn req(&self, line: usize, key: &str) -> Result<&JVal<'a>, ParseError> {
        self.field(key)
            .ok_or_else(|| syntax(line, &format!("missing JSON field '{key}'")))
    }
}

struct JsonCursor<'a> {
    s: &'a str,
    b: &'a [u8],
    i: usize,
    line: usize,
}

impl<'a> JsonCursor<'a> {
    fn new(s: &'a str, line: usize) -> Self {
        Self { s, b: s.as_bytes(), i: 0, line }
    }
    #[inline]
    fn skip_ws(&mut self) {
        while self.i < self.b.len() && self.b[self.i].is_ascii_whitespace() {
            self.i += 1;
        }
    }
    fn parse_val(&mut self) -> Result<JVal<'a>, ParseError> {
        self.skip_ws();
        let ch = *self.b.get(self.i).ok_or_else(|| syntax(self.line, "unexpected EOF in JSON"))?;
        match ch {
            b'{' => self.parse_obj(),
            b'[' => self.parse_arr(),
            b'"' => self.parse_str().map(JVal::Str),
            b't' => {
                if self.s[self.i..].starts_with("true") {
                    self.i += 4;
                    Ok(JVal::Bool(true))
                } else {
                    Err(syntax(self.line, "invalid literal"))
                }
            }
            b'f' => {
                if self.s[self.i..].starts_with("false") {
                    self.i += 5;
                    Ok(JVal::Bool(false))
                } else {
                    Err(syntax(self.line, "invalid literal"))
                }
            }
            b'n' => {
                if self.s[self.i..].starts_with("null") {
                    self.i += 4;
                    Ok(JVal::Null)
                } else {
                    Err(syntax(self.line, "invalid literal"))
                }
            }
            b'0'..=b'9' => self.parse_uint(),
            b'-' => {
                // Skip negative numbers (not used for IDs, may appear in mdata).
                self.i += 1;
                let _ = self.parse_uint()?;
                Ok(JVal::Int(0))
            }
            _ => Err(syntax(self.line, "unexpected character in JSON")),
        }
    }
    fn parse_uint(&mut self) -> Result<JVal<'a>, ParseError> {
        let start = self.i;
        while self.i < self.b.len() && self.b[self.i].is_ascii_digit() {
            self.i += 1;
        }
        // Skip optional fractional/exponent part (only possible inside ignored mdata).
        if self.i < self.b.len() && (self.b[self.i] == b'.' || self.b[self.i] == b'e' || self.b[self.i] == b'E') {
            while self.i < self.b.len()
                && !matches!(self.b[self.i], b',' | b'}' | b']' | b' ' | b'\t' | b'\r' | b'\n')
            {
                self.i += 1;
            }
            return Ok(JVal::Int(0));
        }
        let n = self.s[start..self.i]
            .parse::<u64>()
            .map_err(|_| syntax(self.line, "integer overflow in JSON"))?;
        Ok(JVal::Int(n))
    }
    fn parse_str(&mut self) -> Result<Cow<'a, str>, ParseError> {
        self.i += 1; // opening '"'
        let start = self.i;
        let mut has_escape = false;
        while self.i < self.b.len() {
            match self.b[self.i] {
                b'"' => {
                    let slice = &self.s[start..self.i];
                    self.i += 1;
                    return if !has_escape {
                        Ok(Cow::Borrowed(slice))
                    } else {
                        unescape_json(self.line, slice).map(Cow::Owned)
                    };
                }
                b'\\' => {
                    has_escape = true;
                    self.i += 2;
                }
                _ => self.i += 1,
            }
        }
        Err(syntax(self.line, "unterminated JSON string"))
    }
    fn parse_arr(&mut self) -> Result<JVal<'a>, ParseError> {
        self.i += 1; // '['
        let mut out = Vec::new();
        self.skip_ws();
        if self.b.get(self.i) == Some(&b']') {
            self.i += 1;
            return Ok(JVal::Arr(out));
        }
        loop {
            out.push(self.parse_val()?);
            self.skip_ws();
            match self.b.get(self.i) {
                Some(&b',') => self.i += 1,
                Some(&b']') => {
                    self.i += 1;
                    return Ok(JVal::Arr(out));
                }
                _ => return Err(syntax(self.line, "expected ',' or ']' in JSON array")),
            }
        }
    }
    fn parse_obj(&mut self) -> Result<JVal<'a>, ParseError> {
        self.i += 1; // '{'
        let mut out = Vec::new();
        self.skip_ws();
        if self.b.get(self.i) == Some(&b'}') {
            self.i += 1;
            return Ok(JVal::Obj(out));
        }
        loop {
            self.skip_ws();
            if self.b.get(self.i) != Some(&b'"') {
                return Err(syntax(self.line, "expected JSON object key"));
            }
            let k = self.parse_str()?;
            self.skip_ws();
            if self.b.get(self.i) != Some(&b':') {
                return Err(syntax(self.line, "expected ':' after JSON key"));
            }
            self.i += 1;
            let v = self.parse_val()?;
            out.push((k, v));
            self.skip_ws();
            match self.b.get(self.i) {
                Some(&b',') => self.i += 1,
                Some(&b'}') => {
                    self.i += 1;
                    return Ok(JVal::Obj(out));
                }
                _ => return Err(syntax(self.line, "expected ',' or '}' in JSON object")),
            }
        }
    }
}

fn unescape_json(line: usize, s: &str) -> Result<String, ParseError> {
    let mut out = String::with_capacity(s.len());
    let mut chars = s.chars();
    while let Some(c) = chars.next() {
        if c != '\\' {
            out.push(c);
            continue;
        }
        match chars.next().ok_or_else(|| syntax(line, "trailing backslash in string"))? {
            '"' => out.push('"'),
            '\\' => out.push('\\'),
            '/' => out.push('/'),
            'b' => out.push('\u{0008}'),
            'f' => out.push('\u{000C}'),
            'n' => out.push('\n'),
            'r' => out.push('\r'),
            't' => out.push('\t'),
            'u' => {
                let code = parse_hex4(line, &mut chars)?;
                if (0xD800..=0xDBFF).contains(&code) {
                    if chars.next() != Some('\\') || chars.next() != Some('u') {
                        return Err(syntax(line, "unpaired UTF-16 high surrogate"));
                    }
                    let low = parse_hex4(line, &mut chars)?;
                    if !(0xDC00..=0xDFFF).contains(&low) {
                        return Err(syntax(line, "invalid UTF-16 low surrogate"));
                    }
                    let cp = 0x10000 + (((code as u32 - 0xD800) << 10) | (low as u32 - 0xDC00));
                    out.push(char::from_u32(cp).ok_or_else(|| syntax(line, "invalid unicode scalar"))?);
                } else {
                    out.push(char::from_u32(code as u32).ok_or_else(|| syntax(line, "invalid unicode scalar"))?);
                }
            }
            _ => return Err(syntax(line, "invalid JSON escape")),
        }
    }
    Ok(out)
}

fn parse_hex4(line: usize, chars: &mut std::str::Chars<'_>) -> Result<u16, ParseError> {
    let mut v = 0u16;
    for _ in 0..4 {
        let ch = chars.next().ok_or_else(|| syntax(line, "truncated \\u escape"))?;
        let d = ch.to_digit(16).ok_or_else(|| syntax(line, "invalid hex digit in \\u"))?;
        v = (v << 4) | (d as u16);
    }
    Ok(v)
}

fn parse_ndjson_bi(line: usize, s: &str) -> Result<BinderInfo, ParseError> {
    match s {
        "default" => Ok(BinderInfo::Default),
        "implicit" => Ok(BinderInfo::Implicit),
        "strictImplicit" => Ok(BinderInfo::StrictImplicit),
        "instImplicit" => Ok(BinderInfo::InstImplicit),
        other => Err(syntax(line, &format!("unknown binderInfo '{other}'"))),
    }
}

fn parse_ndjson_hints(line: usize, v: &JVal<'_>) -> Result<ReducibilityHint, ParseError> {
    match v {
        JVal::Str(s) if s == "opaque" => Ok(ReducibilityHint::Opaque),
        JVal::Str(s) if s == "abbrev" => Ok(ReducibilityHint::Abbrev),
        JVal::Obj(_) => Ok(ReducibilityHint::Regular(v.req(line, "regular")?.as_u32(line, "regular")?)),
        _ => Err(syntax(line, "invalid hints field in def")),
    }
}

impl StreamParser {
    pub(crate) fn parse_ndjson_line(
        &mut self,
        line: usize,
        text: &str,
        env: &mut Environment,
    ) -> Result<(), ParseError> {
        let mut cur = JsonCursor::new(text, line);
        let root = cur.parse_val()?;
        let _ = root.as_obj(line, "root")?;

        if let Some(meta) = root.field("meta") {
            if let Some(fmt) = meta.field("format") {
                if let Some(ver) = fmt.field("version") {
                    self.stats.version = Some(ver.as_str(line, "format.version")?.to_owned());
                }
            }
            return Ok(());
        }

        // Names
        if let Some(id_v) = root.field("in") {
            let id = id_v.as_usize(line, "in")?;
            if let Some(o) = root.field("str") {
                let pre = self.get_name(line, o.req(line, "pre")?.as_usize(line, "str.pre")?)?;
                let seg = o.req(line, "str")?.as_str(line, "str.str")?;
                let nid = env.arena.name_str(pre, seg);
                set_slot(&mut self.names, id, nid);
            } else if let Some(o) = root.field("num") {
                let pre = self.get_name(line, o.req(line, "pre")?.as_usize(line, "num.pre")?)?;
                let num = o.req(line, "i")?.as_u64(line, "num.i")?;
                let nid = env.arena.name_num(pre, num);
                set_slot(&mut self.names, id, nid);
            } else {
                return Err(syntax(line, "unknown name object in NDJSON"));
            }
            self.stats.names += 1;
            return Ok(());
        }

        // Levels
        if let Some(id_v) = root.field("il") {
            let id = id_v.as_usize(line, "il")?;
            let lid = if let Some(v) = root.field("succ") {
                let l = self.get_level(line, v.as_usize(line, "succ")?)?;
                env.arena.lvl_succ(l)
            } else if let Some(v) = root.field("max") {
                let a = v.as_arr(line, "max")?;
                if a.len() != 2 { return Err(syntax(line, "max expects 2 elements")); }
                let l1 = self.get_level(line, a[0].as_usize(line, "max[0]")?)?;
                let l2 = self.get_level(line, a[1].as_usize(line, "max[1]")?)?;
                env.arena.lvl_max(l1, l2)
            } else if let Some(v) = root.field("imax") {
                let a = v.as_arr(line, "imax")?;
                if a.len() != 2 { return Err(syntax(line, "imax expects 2 elements")); }
                let l1 = self.get_level(line, a[0].as_usize(line, "imax[0]")?)?;
                let l2 = self.get_level(line, a[1].as_usize(line, "imax[1]")?)?;
                env.arena.lvl_imax(l1, l2)
            } else if let Some(v) = root.field("param") {
                let n = self.get_name(line, v.as_usize(line, "param")?)?;
                env.arena.lvl_param(n)
            } else {
                return Err(syntax(line, "unknown level object in NDJSON"));
            };
            set_slot(&mut self.levels, id, lid);
            self.stats.levels += 1;
            return Ok(());
        }

        // Expressions
        if let Some(id_v) = root.field("ie") {
            let id = id_v.as_usize(line, "ie")?;
            let eid = if let Some(v) = root.field("bvar") {
                env.arena.bvar(v.as_u32(line, "bvar")?)
            } else if let Some(v) = root.field("sort") {
                let l = self.get_level(line, v.as_usize(line, "sort")?)?;
                env.arena.sort(l)
            } else if let Some(o) = root.field("const") {
                let nm = self.get_name(line, o.req(line, "name")?.as_usize(line, "const.name")?)?;
                let us = o.req(line, "us")?.as_arr(line, "const.us")?;
                let mut lvls = Vec::with_capacity(us.len());
                for u in us {
                    lvls.push(self.get_level(line, u.as_usize(line, "const.us[]")?)?);
                }
                env.arena.const_(nm, lvls)
            } else if let Some(o) = root.field("app") {
                let f = self.get_expr(line, o.req(line, "fn")?.as_usize(line, "app.fn")?)?;
                let a = self.get_expr(line, o.req(line, "arg")?.as_usize(line, "app.arg")?)?;
                env.arena.app(f, a)
            } else if let Some(o) = root.field("lam") {
                let nm = self.get_name(line, o.req(line, "name")?.as_usize(line, "lam.name")?)?;
                let ty = self.get_expr(line, o.req(line, "type")?.as_usize(line, "lam.type")?)?;
                let body = self.get_expr(line, o.req(line, "body")?.as_usize(line, "lam.body")?)?;
                let bi = parse_ndjson_bi(line, o.req(line, "binderInfo")?.as_str(line, "lam.binderInfo")?)?;
                env.arena.lam(nm, bi, ty, body)
            } else if let Some(o) = root.field("forallE") {
                let nm = self.get_name(line, o.req(line, "name")?.as_usize(line, "forallE.name")?)?;
                let ty = self.get_expr(line, o.req(line, "type")?.as_usize(line, "forallE.type")?)?;
                let body = self.get_expr(line, o.req(line, "body")?.as_usize(line, "forallE.body")?)?;
                let bi = parse_ndjson_bi(line, o.req(line, "binderInfo")?.as_str(line, "forallE.binderInfo")?)?;
                env.arena.pi(nm, bi, ty, body)
            } else if let Some(o) = root.field("letE") {
                let nm = self.get_name(line, o.req(line, "name")?.as_usize(line, "letE.name")?)?;
                let ty = self.get_expr(line, o.req(line, "type")?.as_usize(line, "letE.type")?)?;
                let val = self.get_expr(line, o.req(line, "value")?.as_usize(line, "letE.value")?)?;
                let body = self.get_expr(line, o.req(line, "body")?.as_usize(line, "letE.body")?)?;
                env.arena.let_(nm, ty, val, body)
            } else if let Some(o) = root.field("proj") {
                let tn = self.get_name(line, o.req(line, "typeName")?.as_usize(line, "proj.typeName")?)?;
                let idx = o.req(line, "idx")?.as_u32(line, "proj.idx")?;
                let st = self.get_expr(line, o.req(line, "struct")?.as_usize(line, "proj.struct")?)?;
                env.arena.proj(tn, idx, st)
            } else if let Some(v) = root.field("natVal") {
                let s = v.as_str(line, "natVal")?;
                let n = s.parse::<u128>().map_err(|_| syntax(line, &format!("natVal '{s}' exceeds u128")))?;
                env.arena.lit_nat(n)
            } else if let Some(v) = root.field("strVal") {
                env.arena.lit_str(v.as_str(line, "strVal")?)
            } else if let Some(o) = root.field("mdata") {
                self.get_expr(line, o.req(line, "expr")?.as_usize(line, "mdata.expr")?)?
            } else {
                return Err(syntax(line, "unknown expr object in NDJSON"));
            };
            set_slot(&mut self.exprs, id, eid);
            self.stats.exprs += 1;
            return Ok(());
        }

        // Declarations
        if let Some(o) = root.field("axiom") {
            if o.field("isUnsafe").and_then(|v| v.as_bool(line, "isUnsafe").ok()).unwrap_or(false) {
                return Err(syntax(line, "unsafe axiom rejected by Rigor kernel"));
            }
            let name = self.get_name(line, o.req(line, "name")?.as_usize(line, "axiom.name")?)?;
            let ty = self.get_expr(line, o.req(line, "type")?.as_usize(line, "axiom.type")?)?;
            let level_params = self.ndjson_names(line, o.req(line, "levelParams")?)?;
            env.add_decl(Declaration::Axiom { name, level_params, ty })
                .map_err(|err| ParseError::Kernel { line, err })?;
            self.stats.axioms += 1;
        } else if let Some(o) = root.field("def") {
            if o.field("safety").and_then(|v| v.as_str(line, "safety").ok()) == Some("unsafe") {
                return Err(syntax(line, "unsafe def rejected by Rigor kernel"));
            }
            let name = self.get_name(line, o.req(line, "name")?.as_usize(line, "def.name")?)?;
            let ty = self.get_expr(line, o.req(line, "type")?.as_usize(line, "def.type")?)?;
            let val = self.get_expr(line, o.req(line, "value")?.as_usize(line, "def.value")?)?;
            let hint = parse_ndjson_hints(line, o.req(line, "hints")?)?;
            let level_params = self.ndjson_names(line, o.req(line, "levelParams")?)?;
            env.add_decl(Declaration::Definition { name, level_params, ty, val, hint })
                .map_err(|err| ParseError::Kernel { line, err })?;
            self.stats.defs += 1;
        } else if let Some(o) = root.field("thm") {
            let name = self.get_name(line, o.req(line, "name")?.as_usize(line, "thm.name")?)?;
            let ty = self.get_expr(line, o.req(line, "type")?.as_usize(line, "thm.type")?)?;
            let val = self.get_expr(line, o.req(line, "value")?.as_usize(line, "thm.value")?)?;
            let level_params = self.ndjson_names(line, o.req(line, "levelParams")?)?;
            env.add_decl(Declaration::Theorem { name, level_params, ty, val })
                .map_err(|err| ParseError::Kernel { line, err })?;
            self.stats.theorems += 1;
        } else if let Some(o) = root.field("opaque") {
            if o.field("isUnsafe").and_then(|v| v.as_bool(line, "isUnsafe").ok()).unwrap_or(false) {
                return Err(syntax(line, "unsafe opaque rejected by Rigor kernel"));
            }
            let name = self.get_name(line, o.req(line, "name")?.as_usize(line, "opaque.name")?)?;
            let ty = self.get_expr(line, o.req(line, "type")?.as_usize(line, "opaque.type")?)?;
            let val = self.get_expr(line, o.req(line, "value")?.as_usize(line, "opaque.value")?)?;
            let level_params = self.ndjson_names(line, o.req(line, "levelParams")?)?;
            env.add_decl(Declaration::Opaque { name, level_params, ty, val })
                .map_err(|err| ParseError::Kernel { line, err })?;
            self.stats.opaques += 1;
        } else if root.field("quot").is_some() {
            env.add_quot().map_err(|err| ParseError::Kernel { line, err })?;
            self.stats.quots += 1;
        } else if let Some(o) = root.field("inductive") {
            let types_arr = o.req(line, "types")?.as_arr(line, "inductive.types")?;
            let ctors_arr = o.req(line, "ctors")?.as_arr(line, "inductive.ctors")?;
            if types_arr.is_empty() {
                return Err(syntax(line, "inductive block has empty types array"));
            }
            let first = &types_arr[0];
            let level_params = self.ndjson_names(line, first.req(line, "levelParams")?)?;
            let num_params = first.req(line, "numParams")?.as_u32(line, "inductive.numParams")?;
            let mut parsed_ctors: Vec<(NameId, NameId, u32, rigor_kernel::ExprId)> = Vec::with_capacity(ctors_arr.len());
            for c in ctors_arr {
                if c.field("isUnsafe").and_then(|v| v.as_bool(line, "isUnsafe").ok()).unwrap_or(false) {
                    return Err(syntax(line, "unsafe constructor rejected by Rigor kernel"));
                }
                let cname = self.get_name(line, c.req(line, "name")?.as_usize(line, "ctor.name")?)?;
                let ind_name = self.get_name(line, c.req(line, "induct")?.as_usize(line, "ctor.induct")?)?;
                let cidx = c.req(line, "cidx")?.as_u32(line, "ctor.cidx")?;
                let cty = self.get_expr(line, c.req(line, "type")?.as_usize(line, "ctor.type")?)?;
                parsed_ctors.push((cname, ind_name, cidx, cty));
            }
            let mut type_specs = Vec::with_capacity(types_arr.len());
            for t in types_arr {
                if t.field("isUnsafe").and_then(|v| v.as_bool(line, "isUnsafe").ok()).unwrap_or(false) {
                    return Err(syntax(line, "unsafe inductive rejected by Rigor kernel"));
                }
                let name = self.get_name(line, t.req(line, "name")?.as_usize(line, "ind.name")?)?;
                let ty = self.get_expr(line, t.req(line, "type")?.as_usize(line, "ind.type")?)?;
                let mut mine: Vec<(u32, NameId, rigor_kernel::ExprId)> = parsed_ctors
                    .iter()
                    .filter(|(_, ind, _, _)| *ind == name)
                    .map(|(cn, _, cidx, cty)| (*cidx, *cn, *cty))
                    .collect();
                mine.sort_by_key(|(cidx, _, _)| *cidx);
                let ctors = mine.into_iter().map(|(_, cn, cty)| (cn, cty)).collect();
                type_specs.push(InductiveTypeSpec { name, ty, ctors });
            }
            env.add_inductive(InductiveSpec {
                level_params,
                num_params,
                types: type_specs,
            })
            .map_err(|err| ParseError::Kernel { line, err })?;
            self.stats.inductives += 1;
        } else {
            let _ = ParseStats::default();
            return Err(syntax(line, "unrecognized NDJSON top-level object"));
        }
        Ok(())
    }

    fn ndjson_names(&self, line: usize, v: &JVal<'_>) -> Result<Box<[NameId]>, ParseError> {
        let arr = v.as_arr(line, "levelParams")?;
        let mut out = Vec::with_capacity(arr.len());
        for item in arr {
            out.push(self.get_name(line, item.as_usize(line, "levelParams[]")?)?);
        }
        Ok(out.into_boxed_slice())
    }
}

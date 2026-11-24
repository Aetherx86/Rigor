//! Bounded, human-readable pretty-printer for Rigor `Name`, `Level`, `Expr`, and `KernelError`.
//! Lives outside `crates/kernel` so the Trusted Computing Base stays small.

use rigor_kernel::arena::{BinderInfo, LevelData, NameData};
use rigor_kernel::{Arena, ExprData, ExprId, KernelError, LevelId, Literal, NameId, Nat};

use crate::ParseError;

/// Default maximum structural depth when rendering an expression.
pub const DEFAULT_MAX_DEPTH: usize = 24;
/// Default maximum output byte/character budget when rendering an expression.
pub const DEFAULT_MAX_CHARS: usize = 512;

/// Render a hierarchical Lean `Name` (iterative, stack-safe on deep name chains).
pub fn format_name(arena: &Arena, mut id: NameId) -> String {
    if id == Arena::ANONYMOUS {
        return "[anonymous]".into();
    }
    enum Seg<'a> {
        Str(&'a str),
        Num(u64),
    }
    let mut parts = Vec::new();
    while id != Arena::ANONYMOUS {
        if id.0 >= arena.name_len() {
            return format!("<name #{}>", id.0);
        }
        match arena.get_name(id) {
            NameData::Anonymous => break,
            NameData::Str(parent, s) => {
                parts.push(Seg::Str(s.as_ref()));
                id = *parent;
            }
            NameData::Num(parent, n) => {
                parts.push(Seg::Num(*n));
                id = *parent;
            }
        }
    }
    if parts.is_empty() {
        return "[anonymous]".into();
    }
    let mut out = String::new();
    for (i, seg) in parts.into_iter().rev().enumerate() {
        if i > 0 {
            out.push('.');
        }
        match seg {
            Seg::Str(s) => out.push_str(s),
            Seg::Num(n) => out.push_str(&n.to_string()),
        }
    }
    out
}

/// Convert an arbitrary-precision kernel [`Nat`] to a decimal string.
pub fn format_nat(n: &Nat) -> String {
    if let Some(v) = n.to_u128() {
        return v.to_string();
    }
    let base = Nat::from_u128(1_000_000_000_000_000_000);
    let mut cur = n.clone();
    let mut chunks = Vec::new();
    while !cur.is_zero() {
        let (q, r) = cur.divmod(&base).expect("non-zero base");
        chunks.push(r.to_u64().unwrap_or(0));
        cur = q;
    }
    let mut out = chunks.pop().unwrap_or(0).to_string();
    for c in chunks.into_iter().rev() {
        out.push_str(&format!("{c:018}"));
    }
    out
}

/// Render a universe [`LevelId`] in readable Lean syntax (bounded recursion depth).
pub fn format_level(arena: &Arena, id: LevelId) -> String {
    let mut out = String::new();
    write_level(arena, id, 0, &mut out);
    out
}

fn write_level(arena: &Arena, mut id: LevelId, depth: usize, out: &mut String) {
    if depth >= 32 {
        out.push_str("...");
        return;
    }
    if id.0 >= arena.level_len() {
        out.push_str(&format!("<level #{}>", id.0));
        return;
    }
    let mut offset = 0u32;
    while id.0 < arena.level_len() {
        if let LevelData::Succ(inner) = *arena.get_level(id) {
            offset = offset.saturating_add(1);
            id = inner;
        } else {
            break;
        }
    }
    if id.0 >= arena.level_len() {
        out.push_str(&format!("<level #{}>", id.0));
        return;
    }
    match *arena.get_level(id) {
        LevelData::Zero => out.push_str(&offset.to_string()),
        LevelData::Param(n) => {
            out.push_str(&format_name(arena, n));
            if offset > 0 {
                out.push_str(&format!("+{offset}"));
            }
        }
        LevelData::Max(a, b) => {
            if offset > 0 {
                out.push('(');
            }
            out.push_str("max ");
            write_level_atom(arena, a, depth + 1, out);
            out.push(' ');
            write_level_atom(arena, b, depth + 1, out);
            if offset > 0 {
                out.push_str(&format!(")+{offset}"));
            }
        }
        LevelData::IMax(a, b) => {
            if offset > 0 {
                out.push('(');
            }
            out.push_str("imax ");
            write_level_atom(arena, a, depth + 1, out);
            out.push(' ');
            write_level_atom(arena, b, depth + 1, out);
            if offset > 0 {
                out.push_str(&format!(")+{offset}"));
            }
        }
        LevelData::Succ(_) => unreachable!(),
    }
}

fn write_level_atom(arena: &Arena, id: LevelId, depth: usize, out: &mut String) {
    let needs_parens = id.0 < arena.level_len()
        && matches!(
            arena.get_level(id),
            LevelData::Max(_, _) | LevelData::IMax(_, _)
        );
    if needs_parens {
        out.push('(');
    }
    write_level(arena, id, depth, out);
    if needs_parens {
        out.push(')');
    }
}

/// Render an expression with default depth and length bounds.
pub fn format_expr(arena: &Arena, id: ExprId) -> String {
    format_expr_bounded(arena, id, DEFAULT_MAX_DEPTH, DEFAULT_MAX_CHARS)
}

/// Render an expression with explicit `max_depth` and `max_chars` limits so huge DAGs
/// never cause runaway formatting or memory blowup.
pub fn format_expr_bounded(
    arena: &Arena,
    id: ExprId,
    max_depth: usize,
    max_chars: usize,
) -> String {
    let mut ctx = PrettyCtx {
        arena,
        max_depth,
        max_chars,
        out: String::new(),
        truncated: false,
        binders: Vec::new(),
    };
    ctx.write_expr(id, 0, false);
    if ctx.truncated {
        ctx.out.push_str("...");
    }
    ctx.out
}

struct PrettyCtx<'a> {
    arena: &'a Arena,
    max_depth: usize,
    max_chars: usize,
    out: String,
    truncated: bool,
    binders: Vec<String>,
}

impl<'a> PrettyCtx<'a> {
    fn push_str(&mut self, s: &str) -> bool {
        if self.truncated {
            return false;
        }
        if self.out.len() + s.len() > self.max_chars {
            self.truncated = true;
            return false;
        }
        self.out.push_str(s);
        true
    }

    fn write_expr(&mut self, id: ExprId, depth: usize, as_atom: bool) {
        if self.truncated {
            return;
        }
        if depth >= self.max_depth {
            let _ = self.push_str("...");
            return;
        }
        if id.0 >= self.arena.expr_len() {
            let _ = self.push_str(&format!("<temp expr #{}>", id.0));
            return;
        }
        match *self.arena.get_expr(id) {
            ExprData::BVar(i) => {
                let idx = i as usize;
                if let Some(name) = self
                    .binders
                    .len()
                    .checked_sub(1 + idx)
                    .and_then(|pos| self.binders.get(pos))
                    .filter(|s| *s != "_")
                    .cloned()
                {
                    let _ = self.push_str(&name);
                } else {
                    let _ = self.push_str(&format!("#{i}"));
                }
            }
            ExprData::FVar(fv) => {
                let _ = self.push_str(&format!("?fv_{}", fv.0));
            }
            ExprData::Sort(l) => {
                let s = format_sort(self.arena, l);
                let compound = s.contains(' ');
                if as_atom && compound {
                    let _ = self.push_str("(");
                }
                let _ = self.push_str(&s);
                if as_atom && compound {
                    let _ = self.push_str(")");
                }
            }
            ExprData::Const(name, lvls_id) => {
                let _ = self.push_str(&format_name(self.arena, name));
                if lvls_id.0 < self.arena.level_list_len() {
                    let lvls = self.arena.get_level_list(lvls_id);
                    if !lvls.is_empty() {
                        let _ = self.push_str(".{");
                        for (i, &l) in lvls.iter().enumerate() {
                            if i > 0 {
                                let _ = self.push_str(", ");
                            }
                            let _ = self.push_str(&format_level(self.arena, l));
                        }
                        let _ = self.push_str("}");
                    }
                }
            }
            ExprData::App(_, _) => {
                let mut args = Vec::new();
                let mut head = id;
                while let ExprData::App(f, a) = *self.arena.get_expr(head) {
                    args.push(a);
                    head = f;
                    if args.len() > 64 {
                        break;
                    }
                }
                args.reverse();
                if as_atom {
                    let _ = self.push_str("(");
                }
                self.write_expr(head, depth + 1, true);
                for a in args {
                    if !self.push_str(" ") {
                        break;
                    }
                    self.write_expr(a, depth + 1, true);
                }
                if as_atom {
                    let _ = self.push_str(")");
                }
            }
            ExprData::Pi {
                name,
                binder_info,
                ty,
                body,
            } => {
                if as_atom {
                    let _ = self.push_str("(");
                }
                let dependent = self.arena.get_expr_meta(body).loose_bvar_range > 0;
                if !dependent && binder_info == BinderInfo::Default {
                    let dom_needs_parens = matches!(
                        self.arena.get_expr(ty),
                        ExprData::Pi { .. } | ExprData::Lam { .. } | ExprData::Let { .. }
                    );
                    self.write_expr(ty, depth + 1, dom_needs_parens);
                    let _ = self.push_str(" -> ");
                    self.binders.push("_".into());
                    self.write_expr(body, depth + 1, false);
                    self.binders.pop();
                } else {
                    let (open, close) = binder_delims(binder_info);
                    let _ = self.push_str("forall ");
                    let _ = self.push_str(open);
                    let bname = if name == Arena::ANONYMOUS {
                        "_".into()
                    } else {
                        format_name(self.arena, name)
                    };
                    let _ = self.push_str(&bname);
                    let _ = self.push_str(" : ");
                    self.write_expr(ty, depth + 1, false);
                    let _ = self.push_str(close);
                    let _ = self.push_str(", ");
                    self.binders.push(bname);
                    self.write_expr(body, depth + 1, false);
                    self.binders.pop();
                }
                if as_atom {
                    let _ = self.push_str(")");
                }
            }
            ExprData::Lam {
                name,
                binder_info,
                ty,
                body,
            } => {
                if as_atom {
                    let _ = self.push_str("(");
                }
                let (open, close) = binder_delims(binder_info);
                let _ = self.push_str("fun ");
                let _ = self.push_str(open);
                let bname = if name == Arena::ANONYMOUS {
                    "_".into()
                } else {
                    format_name(self.arena, name)
                };
                let _ = self.push_str(&bname);
                let _ = self.push_str(" : ");
                self.write_expr(ty, depth + 1, false);
                let _ = self.push_str(close);
                let _ = self.push_str(" => ");
                self.binders.push(bname);
                self.write_expr(body, depth + 1, false);
                self.binders.pop();
                if as_atom {
                    let _ = self.push_str(")");
                }
            }
            ExprData::Let { ty, val, body } => {
                if as_atom {
                    let _ = self.push_str("(");
                }
                let _ = self.push_str("let _ : ");
                self.write_expr(ty, depth + 1, false);
                let _ = self.push_str(" := ");
                self.write_expr(val, depth + 1, false);
                let _ = self.push_str("; ");
                self.binders.push("_".into());
                self.write_expr(body, depth + 1, false);
                self.binders.pop();
                if as_atom {
                    let _ = self.push_str(")");
                }
            }
            ExprData::Lit(lid) => {
                if lid.0 >= self.arena.lit_len() {
                    let _ = self.push_str(&format!("<lit #{}>", lid.0));
                    return;
                }
                match self.arena.get_lit(lid) {
                    Literal::Nat(n) => {
                        let s = format_nat(n);
                        let _ = self.push_str(&s);
                    }
                    Literal::Str(s) => {
                        let escaped = format!("{s:?}");
                        let _ = self.push_str(&escaped);
                    }
                }
            }
            ExprData::Proj {
                struct_name,
                idx,
                expr,
            } => {
                self.write_expr(expr, depth + 1, true);
                let _ = self.push_str(&format!(
                    ".{}.{}",
                    format_name(self.arena, struct_name),
                    idx
                ));
            }
        }
    }
}

fn format_sort(arena: &Arena, id: LevelId) -> String {
    if id.0 >= arena.level_len() {
        return format!("Sort <level #{}>", id.0);
    }
    match *arena.get_level(id) {
        LevelData::Zero => "Prop".into(),
        LevelData::Succ(inner) if inner.0 < arena.level_len() => match *arena.get_level(inner) {
            LevelData::Zero => "Type".into(),
            _ => format!("Type {}", format_level(arena, inner)),
        },
        _ => format!("Sort {}", format_level(arena, id)),
    }
}

fn binder_delims(bi: BinderInfo) -> (&'static str, &'static str) {
    match bi {
        BinderInfo::Default => ("(", ")"),
        BinderInfo::Implicit => ("{", "}"),
        BinderInfo::StrictImplicit => ("{{", "}}"),
        BinderInfo::InstImplicit => ("[", "]"),
    }
}

/// Format a [`KernelError`] with human-readable constant names and bounded expression strings.
pub fn format_kernel_error(arena: &Arena, err: &KernelError) -> String {
    match err {
        KernelError::DuplicateDeclaration(n) => {
            format!("duplicate declaration '{}'", format_name(arena, *n))
        }
        KernelError::UnknownConstant(n) => {
            format!("unknown constant '{}'", format_name(arena, *n))
        }
        KernelError::DuplicateLevelParam(n) => {
            format!(
                "duplicate universe level parameter '{}'",
                format_name(arena, *n)
            )
        }
        KernelError::UnboundLevelParam(n) => {
            format!(
                "unbound universe level parameter '{}'",
                format_name(arena, *n)
            )
        }
        KernelError::LevelParamCountMismatch {
            constant,
            expected,
            got,
        } => format!(
            "universe parameter count mismatch for '{}': expected {expected}, got {got}",
            format_name(arena, *constant)
        ),
        KernelError::UnboundBVar(idx) => format!("unbound bound variable #{idx}"),
        KernelError::UnknownFVar(fv) => format!("unknown free variable ?fv_{}", fv.0),
        KernelError::ExpectedSort(e) => {
            format!("expected a Sort, got '{}'", format_expr(arena, *e))
        }
        KernelError::ExpectedPi(e) => {
            format!(
                "expected a function (Pi) type, got '{}'",
                format_expr(arena, *e)
            )
        }
        KernelError::TypeMismatch { expected, got } => format!(
            "type mismatch: expected '{}', got '{}'",
            format_expr(arena, *expected),
            format_expr(arena, *got)
        ),
        KernelError::TheoremNotInProp { name, sort } => format!(
            "theorem '{}' must live in Prop, got '{}'",
            format_name(arena, *name),
            format_expr(arena, *sort)
        ),
        KernelError::InvalidInductive(msg) => format!("invalid inductive declaration: {msg}"),
        KernelError::NonPositiveInductive { ind, ctor } => format!(
            "non-positive occurrence of inductive '{}' in constructor '{}'",
            format_name(arena, *ind),
            format_name(arena, *ctor)
        ),
        KernelError::UniverseTooSmall { ind, ctor } => format!(
            "universe level too small for inductive '{}' in constructor '{}'",
            format_name(arena, *ind),
            format_name(arena, *ctor)
        ),
        KernelError::InvalidProjection {
            struct_name,
            idx,
            reason,
        } => format!(
            "invalid projection {}.{idx}: {reason}",
            format_name(arena, *struct_name)
        ),
    }
}

/// Format a [`ParseError`] using `arena` to resolve names and expressions in kernel rejections.
pub fn format_parse_error(arena: &Arena, err: &ParseError) -> String {
    match err {
        ParseError::Kernel { line, err } => {
            format!(
                "line {line}: kernel rejected declaration: {}",
                format_kernel_error(arena, err)
            )
        }
        ParseError::DeferredKernel { name, err } => {
            format!(
                "kernel rejected declaration '{name}': {}",
                format_kernel_error(arena, err)
            )
        }
        other => other.to_string(),
    }
}

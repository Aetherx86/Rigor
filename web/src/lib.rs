//! Rigor in the browser: parse, verify, and audit a `lean4export` NDJSON/text file with the
//! same kernel and parser as the native checker (sequential mode; browsers give a page one thread).
use rigor_parser::kernel::Environment;
use rigor_parser::{
    audit_environment, format_parse_error, inspect_decl, lookup_name, parse_and_check,
    shortest_dependency_path,
};
use wasm_bindgen::prelude::*;

/// Return the Rigor WASM module version.
#[wasm_bindgen]
pub fn version() -> String {
    env!("CARGO_PKG_VERSION").to_owned()
}

/// Verify a `lean4export` text or NDJSON string and return a JSON status object.
/// Preserves the v0.1.x signature and JSON schema while emitting human-readable error diagnostics.
#[wasm_bindgen]
pub fn check(input: &str) -> String {
    let mut env = Environment::new();
    match parse_and_check(input.as_bytes(), &mut env) {
        Ok(stats) => format!(
            "{{\"ok\":true,\"decls\":{},\"env_decls\":{},\"lines\":{},\"theorems\":{},\"defs\":{},\"inductives\":{},\"axioms\":{}}}",
            stats.total_decls(), env.len(), stats.lines, stats.theorems, stats.defs, stats.inductives, stats.axioms
        ),
        Err(e) => {
            let msg = format_parse_error(&env.arena, &e);
            format!("{{\"ok\":false,\"error\":{}}}", json_str(&msg))
        }
    }
}

/// Verify a `lean4export` input and compute either a whole-environment axiom audit (when
/// `decl_name` is empty) or a single-declaration inspection + transitive axiom footprint.
#[wasm_bindgen]
pub fn audit(input: &str, decl_name: &str) -> String {
    let mut env = Environment::new();
    let stats = match parse_and_check(input.as_bytes(), &mut env) {
        Ok(s) => s,
        Err(e) => {
            let msg = format_parse_error(&env.arena, &e);
            return format!("{{\"ok\":false,\"error\":{}}}", json_str(&msg));
        }
    };
    let target = decl_name.trim();
    if !target.is_empty() {
        let Some(id) = lookup_name(&env, target) else {
            return format!(
                "{{\"ok\":false,\"error\":{}}}",
                json_str(&format!("declaration '{target}' not found"))
            );
        };
        let info = inspect_decl(&env, id).expect("looked up name must exist");
        return format!(
            "{{\"ok\":true,\"name\":{},\"kind\":{},\"level_params\":{},\"type\":{},\"direct_deps\":{},\"axioms\":{},\"non_standard_axioms\":{},\"uses_sorry\":{},\"uses_quot\":{}}}",
            json_str(&info.name),
            json_str(info.kind.as_str()),
            json_str_array(&info.level_params),
            json_str(&info.ty),
            json_str_array(&info.direct_deps),
            json_str_array(&info.axioms),
            json_str_array(&info.non_standard_axioms),
            info.uses_sorry,
            info.uses_quot,
        );
    }

    let report = audit_environment(&env);
    let mut axioms_json = String::from("[");
    for (i, ax) in report.axioms.iter().enumerate() {
        if i > 0 {
            axioms_json.push(',');
        }
        axioms_json.push_str(&format!(
            "{{\"name\":{},\"is_standard\":{},\"is_sorry\":{},\"is_trust_extending\":{},\"dependent_decls\":{},\"dependent_theorems\":{}}}",
            json_str(&ax.name),
            ax.is_standard,
            ax.is_sorry,
            ax.is_trust_extending,
            ax.dependent_decls,
            ax.dependent_theorems,
        ));
    }
    axioms_json.push(']');
    format!(
        "{{\"ok\":true,\"decls\":{},\"env_decls\":{},\"theorems\":{},\"uses_quot\":{},\"non_standard_axioms\":{},\"sorry_theorems\":{},\"axioms\":{}}}",
        stats.total_decls(),
        report.total_env_decls,
        report.theorems,
        report.uses_quot,
        json_str_array(&report.non_standard_axioms),
        json_str_array(&report.sorry_theorems),
        axioms_json,
    )
}

/// Verify a `lean4export` input and compute the shortest dependency chain from `from_name` to `to_name`.
#[wasm_bindgen]
pub fn why(input: &str, from_name: &str, to_name: &str) -> String {
    let mut env = Environment::new();
    if let Err(e) = parse_and_check(input.as_bytes(), &mut env) {
        let msg = format_parse_error(&env.arena, &e);
        return format!("{{\"ok\":false,\"error\":{}}}", json_str(&msg));
    }
    let from = from_name.trim();
    let to = to_name.trim();
    let Some(from_id) = lookup_name(&env, from) else {
        return format!(
            "{{\"ok\":false,\"error\":{}}}",
            json_str(&format!("declaration '{from}' not found"))
        );
    };
    let Some(to_id) = lookup_name(&env, to) else {
        return format!(
            "{{\"ok\":false,\"error\":{}}}",
            json_str(&format!("target dependency '{to}' not found"))
        );
    };
    match shortest_dependency_path(&env, from_id, to_id) {
        Some(path) => format!(
            "{{\"ok\":true,\"from\":{},\"to\":{},\"found\":true,\"path\":{}}}",
            json_str(from),
            json_str(to),
            json_str_array(&path)
        ),
        None => format!(
            "{{\"ok\":true,\"from\":{},\"to\":{},\"found\":false,\"path\":[]}}",
            json_str(from),
            json_str(to)
        ),
    }
}

fn json_str(s: &str) -> String {
    let mut out = String::from("\"");
    for c in s.chars().take(2000) {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

fn json_str_array(items: &[String]) -> String {
    let mut out = String::from("[");
    for (i, item) in items.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        out.push_str(&json_str(item));
    }
    out.push(']');
    out
}

//! Rigor in the browser: parse and verify a `lean4export` NDJSON file with the same kernel and
//! parser as the native checker (sequential mode; browsers give a page one thread here).
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub fn check(input: &str) -> String {
    match rigor_parser::parse_str(input) {
        Ok((env, stats)) => format!(
            "{{\"ok\":true,\"decls\":{},\"env_decls\":{},\"lines\":{},\"theorems\":{},\"defs\":{},\"inductives\":{},\"axioms\":{}}}",
            stats.total_decls(), env.len(), stats.lines, stats.theorems, stats.defs, stats.inductives, stats.axioms
        ),
        Err(e) => format!("{{\"ok\":false,\"error\":{}}}", json_str(&e.to_string())),
    }
}

fn json_str(s: &str) -> String {
    let mut out = String::from("\"");
    for c in s.chars().take(2000) {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

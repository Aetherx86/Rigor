//! Lean's own `Init.Prelude` (lean4export of Lean v4.36.0-rc1, 1,840 declarations): it must
//! verify, including nested inductives such as `Lean.Syntax` (`Array Syntax` fields) and the
//! quotient primitives, and the same file with one theorem given another theorem's proof must not.

use rigor_kernel::KernelError;
use rigor_parser::{parse_str, ParseError};

fn prelude() -> String {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data/Init.Prelude.ndjson.gz");
    let out = std::process::Command::new("gzip").args(["-dc", path]).output().expect("run gzip");
    assert!(out.status.success(), "gzip failed");
    String::from_utf8(out.stdout).expect("UTF-8 export")
}

#[test]
fn init_prelude_verifies() {
    let text = prelude();
    for name in ["\"Syntax\"", "\"Quot\""] {
        assert!(text.contains(name), "export should declare {name}");
    }
    let (env, stats) = parse_str(&text).expect("Init.Prelude must verify");
    assert_eq!(stats.total_decls(), 1840);
    assert!(env.len() > 2000, "constructors and recursors are generated too");
}

#[test]
fn borrowed_proof_is_rejected() {
    let text = prelude();
    let mut lines: Vec<String> = text.lines().map(str::to_owned).collect();
    // theorems without universe parameters, so the borrowed proof is closed in the target's context
    let thms: Vec<usize> = (0..lines.len())
        .filter(|&i| lines[i].starts_with("{\"thm\":") && lines[i].contains("\"levelParams\":[]"))
        .collect();
    // Give a later theorem the proof of the first one (the first one's value is already defined
    // when the later theorem is read, so only the kernel can object).
    let value = |l: &str| {
        let i = l.find("\"value\":").expect("value field") + 8;
        let j = i + l[i..].find(|c: char| !c.is_ascii_digit()).unwrap();
        l[i..j].to_owned()
    };
    let (donor, victim) = (thms[0], thms[thms.len() / 2]);
    let (dv, vv) = (value(&lines[donor]), value(&lines[victim]));
    assert_ne!(dv, vv);
    lines[victim] = lines[victim].replacen(&format!("\"value\":{vv}"), &format!("\"value\":{dv}"), 1);
    match parse_str(&lines.join("\n")) {
        Err(ParseError::Kernel { err: KernelError::TypeMismatch { .. }, line }) => assert_eq!(line, victim + 1),
        Err(e) => panic!("rejected for the wrong reason: {e}"),
        Ok(_) => panic!("a theorem with another theorem's proof was accepted"),
    }
}

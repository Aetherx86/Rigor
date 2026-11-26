//! End-to-end CLI tests for `rigor-bench` (`--check`, `--audit`, `--inspect`, `--json`, policies).

use std::fs;
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

const BIN: &str = env!("CARGO_BIN_EXE_rigor-bench");

const VALID_WITH_SORRY: &str = "\
0.1.4
1 #NS 0 Nat
2 #NS 1 zero
3 #NS 1 succ
4 #NS 0 Eq
5 #NS 4 refl
6 #NS 0 u
7 #NS 0 propext
8 #NS 0 sorryAx
9 #NS 0 pure_thm
10 #NS 0 sorry_thm
1 #US 0
2 #UP 6
0 #ES 0
1 #ES 1
2 #ES 2
3 #EV 0
4 #EV 1
5 #EC 1
6 #EP #BD 0 5 5
#IND 0 1 1 2 2 5 3 6
7 #EP #BD 0 4 0
8 #EP #BD 0 3 7
9 #EP #BI 0 2 8
10 #EC 4 2
11 #EA 10 4
12 #EA 11 3
13 #EA 12 3
14 #EP #BD 0 3 13
15 #EP #BI 0 2 14
#IND 2 4 9 1 5 15 6
#AX 7 0
16 #EP #BD 0 2 3
#AX 8 16 6
17 #EC 4 1
18 #EC 5 1
19 #ELN 0
20 #EA 17 5
21 #EA 20 19
22 #EA 21 19
23 #EA 18 5
24 #EA 23 19
#THM 9 22 24
25 #EC 8 0
26 #EA 25 22
#THM 10 22 26
";

const ILL_TYPED: &str = "\
0.1.4
1 #NS 0 BadThm
0 #ES 0
1 #US 0
1 #ES 1
#THM 1 1 0
";

fn write_temp(name: &str, content: &str) -> std::path::PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let path = std::env::temp_dir().join(format!("rigor_cli_{name}_{nanos}.export"));
    fs::write(&path, content).expect("write temp fixture");
    path
}

#[test]
fn cli_version_check_audit_inspect_and_policies() {
    let ver = Command::new(BIN).arg("--version").output().unwrap();
    assert!(ver.status.success());
    let ver_out = String::from_utf8(ver.stdout).unwrap();
    assert!(
        ver_out.starts_with("rigor "),
        "unexpected version output: {ver_out}"
    );

    let valid_path = write_temp("valid", VALID_WITH_SORRY);
    let bad_path = write_temp("bad", ILL_TYPED);

    // 1. Default --check preserves CHECK_OK output.
    let out = Command::new(BIN)
        .args(["--check", valid_path.to_str().unwrap()])
        .output()
        .unwrap();
    assert!(
        out.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let stdout = String::from_utf8(out.stdout).unwrap();
    assert!(stdout.contains("CHECK_OK "), "got: {stdout}");

    // 2. --check --json emits valid structured report.
    let out = Command::new(BIN)
        .args([
            "--check",
            valid_path.to_str().unwrap(),
            "--json",
            "--sequential",
        ])
        .output()
        .unwrap();
    assert!(out.status.success());
    let stdout = String::from_utf8(out.stdout).unwrap();
    assert!(stdout.contains("\"ok\":true"), "got: {stdout}");
    assert!(
        stdout.contains("\"sorry_theorems\":[\"sorry_thm\"]"),
        "got: {stdout}"
    );

    // 3. --check --forbid-sorry fails with exit code 1 and JSON policy_violations.
    let out = Command::new(BIN)
        .args([
            "--check",
            valid_path.to_str().unwrap(),
            "--forbid-sorry",
            "--json",
        ])
        .output()
        .unwrap();
    assert_eq!(out.status.code(), Some(1));
    let stdout = String::from_utf8(out.stdout).unwrap();
    assert!(stdout.contains("\"ok\":false"), "got: {stdout}");
    assert!(stdout.contains("sorryAx"), "got: {stdout}");

    // 4. --audit --decl pure_thm --forbid-sorry PASSES (pure_thm does not use sorryAx!).
    let out = Command::new(BIN)
        .args([
            "--audit",
            valid_path.to_str().unwrap(),
            "--decl",
            "pure_thm",
            "--forbid-sorry",
            "--json",
        ])
        .output()
        .unwrap();
    assert!(
        out.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let stdout = String::from_utf8(out.stdout).unwrap();
    assert!(stdout.contains("\"ok\":true"), "got: {stdout}");
    assert!(stdout.contains("\"axioms\":[]"), "got: {stdout}");

    // 5. --audit --decl sorry_thm --forbid-sorry FAILS.
    let out = Command::new(BIN)
        .args([
            "--audit",
            valid_path.to_str().unwrap(),
            "--decl",
            "sorry_thm",
            "--forbid-sorry",
        ])
        .output()
        .unwrap();
    assert_eq!(out.status.code(), Some(1));
    let stderr = String::from_utf8(out.stderr).unwrap();
    assert!(stderr.contains("POLICY_FAIL"), "got: {stderr}");

    // 6. --inspect emits pretty-printed type and dependencies.
    let out = Command::new(BIN)
        .args([
            "--inspect",
            valid_path.to_str().unwrap(),
            "pure_thm",
            "--json",
        ])
        .output()
        .unwrap();
    assert!(out.status.success());
    let stdout = String::from_utf8(out.stdout).unwrap();
    assert!(stdout.contains("\"name\":\"pure_thm\""), "got: {stdout}");
    assert!(stdout.contains("\"kind\":\"theorem\""), "got: {stdout}");
    assert!(stdout.contains("Eq.{1} Nat 0 0"), "got: {stdout}");

    // 7. --why traces shortest dependency chain (found and independent).
    let out = Command::new(BIN)
        .args([
            "--why",
            valid_path.to_str().unwrap(),
            "sorry_thm",
            "sorryAx",
            "--json",
        ])
        .output()
        .unwrap();
    assert!(out.status.success());
    let stdout = String::from_utf8(out.stdout).unwrap();
    assert!(
        stdout.contains("\"found\":true")
            && stdout.contains("\"path\":[\"sorry_thm\",\"sorryAx\"]"),
        "got: {stdout}"
    );

    let out = Command::new(BIN)
        .args([
            "--why",
            valid_path.to_str().unwrap(),
            "pure_thm",
            "sorryAx",
            "--json",
        ])
        .output()
        .unwrap();
    assert!(out.status.success());
    let stdout = String::from_utf8(out.stdout).unwrap();
    assert!(stdout.contains("\"found\":false"), "got: {stdout}");

    // 8. --rdeps and --list filter declarations cleanly.
    let out = Command::new(BIN)
        .args([
            "--rdeps",
            valid_path.to_str().unwrap(),
            "sorryAx",
            "--json",
        ])
        .output()
        .unwrap();
    assert!(out.status.success());
    let stdout = String::from_utf8(out.stdout).unwrap();
    assert!(
        stdout.contains("\"reverse_dependents\":[\"sorry_thm\"]"),
        "got: {stdout}"
    );

    let out = Command::new(BIN)
        .args([
            "--list",
            valid_path.to_str().unwrap(),
            "--kind",
            "theorem",
            "--prefix",
            "pure",
            "--json",
        ])
        .output()
        .unwrap();
    assert!(out.status.success());
    let stdout = String::from_utf8(out.stdout).unwrap();
    assert!(
        stdout.contains("\"count\":1") && stdout.contains("\"name\":\"pure_thm\""),
        "got: {stdout}"
    );

    // 9. Ill-typed export exits 1 cleanly (not panic 101) with human-readable error.
    let out = Command::new(BIN)
        .args(["--check", bad_path.to_str().unwrap(), "--json"])
        .output()
        .unwrap();
    assert_eq!(out.status.code(), Some(1));
    let stdout = String::from_utf8(out.stdout).unwrap();
    assert!(stdout.contains("\"ok\":false"), "got: {stdout}");
    assert!(stdout.contains("BadThm"), "got: {stdout}");
    assert!(stdout.contains("must live in Prop"), "got: {stdout}");

    let _ = fs::remove_file(valid_path);
    let _ = fs::remove_file(bad_path);
}

//! Tests for transitive axiom auditing, bounded pretty-printing, and hostile-input parser defense.

use rigor_kernel::{Arena, BinderInfo, Environment, KernelError};
use rigor_parser::{
    audit_environment, check_axiom_policy, check_decl_policy, format_expr_bounded,
    format_kernel_error, format_parse_error, inspect_decl, lookup_name, parse_and_check, parse_str,
    AxiomPolicy, DeclKind, ParseError, ParseLimits, StreamParser,
};

const AUDIT_FIXTURE: &str = "\
0.1.4
1 #NS 0 Nat
2 #NS 1 zero
3 #NS 1 succ
4 #NS 0 Eq
5 #NS 4 refl
6 #NS 0 u
7 #NS 0 propext
8 #NS 0 sorryAx
9 #NS 0 CustomAx
10 #NS 0 pure_thm
11 #NS 0 helper_sorry
12 #NS 0 thm_via_sorry
13 #NS 0 thm_via_custom
14 #NS 0 opaque_hiding_sorry
15 #NS 0 thm_via_opaque
16 #NS 0 Quot
17 #NS 16 mk
18 #NS 0 use_quot_def
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
#QUOT
-- Axioms:
-- propext : Prop
#AX 7 0
-- sorryAx.{u} : (α : Sort u) -> α
16 #EP #BD 0 2 3
#AX 8 16 6
-- CustomAx : Prop
#AX 9 0
-- pure_thm : Eq.{1} Nat 0 0 := Eq.refl.{1} Nat 0
17 #EC 4 1
18 #EC 5 1
19 #ELN 0
20 #EA 17 5
21 #EA 20 19
22 #EA 21 19
23 #EA 18 5
24 #EA 23 19
#THM 10 22 24
-- helper_sorry : Eq.{1} Nat 0 0 := sorryAx.{0} (Eq.{1} Nat 0 0)
25 #EC 8 0
26 #EA 25 22
#DEF 11 22 26 R 1
-- thm_via_sorry : Eq.{1} Nat 0 0 := helper_sorry
27 #EC 11
#THM 12 22 27
-- thm_via_custom : CustomAx := sorryAx.{0} CustomAx
28 #EC 9
29 #EA 25 28
#THM 13 28 29
-- opaque_hiding_sorry : Eq.{1} Nat 0 0 := sorryAx.{0} (Eq.{1} Nat 0 0)
#OPAQ 14 22 26
-- thm_via_opaque : Eq.{1} Nat 0 0 := opaque_hiding_sorry
30 #EC 14
#THM 15 22 30
-- use_quot_def : Quot.{1} Nat (fun _ _ => Eq.{1} Nat 0 0) := ...
31 #EL #BD 0 5 22
32 #EL #BD 0 5 31
33 #EC 16 1
34 #EA 33 5
35 #EA 34 32
36 #EC 17 1
37 #EA 36 5
38 #EA 37 32
39 #EA 38 19
#DEF 18 35 39 R 1
";

#[test]
fn axiom_auditing_transitive_footprint_and_policy() {
    let (env, stats) = parse_str(AUDIT_FIXTURE).expect("audit fixture must verify");
    assert_eq!(stats.axioms, 3);
    assert_eq!(stats.theorems, 4);

    // 1. Pure theorem has zero axiom dependencies.
    let pure_id = lookup_name(&env, "pure_thm").expect("pure_thm exists");
    let pure_info = inspect_decl(&env, pure_id).unwrap();
    assert_eq!(pure_info.kind, DeclKind::Theorem);
    assert!(pure_info.axioms.is_empty());
    assert!(!pure_info.uses_sorry);
    assert!(pure_info.ty.contains("Eq"));

    // 2. Indirect sorry through helper_sorry def is caught.
    let sorry_id = lookup_name(&env, "thm_via_sorry").unwrap();
    let sorry_info = inspect_decl(&env, sorry_id).unwrap();
    assert_eq!(sorry_info.axioms, vec!["sorryAx"]);
    assert!(sorry_info.uses_sorry);

    // 3. Opaque definition hiding sorryAx is STILL caught (auditor walks opaque values!).
    let opaq_thm_id = lookup_name(&env, "thm_via_opaque").unwrap();
    let opaq_info = inspect_decl(&env, opaq_thm_id).unwrap();
    assert_eq!(opaq_info.axioms, vec!["sorryAx"]);
    assert!(opaq_info.uses_sorry);

    // 4. Theorem whose type mentions CustomAx and proof uses sorryAx depends on BOTH.
    let custom_thm_id = lookup_name(&env, "thm_via_custom").unwrap();
    let custom_info = inspect_decl(&env, custom_thm_id).unwrap();
    assert_eq!(custom_info.axioms, vec!["CustomAx", "sorryAx"]);
    assert_eq!(custom_info.non_standard_axioms, vec!["CustomAx", "sorryAx"]);

    // 5. Quotient usage detection.
    let q_id = lookup_name(&env, "use_quot_def").unwrap();
    let q_info = inspect_decl(&env, q_id).unwrap();
    assert!(q_info.uses_quot);

    // 6. Whole-environment audit report.
    let report = audit_environment(&env);
    assert_eq!(report.theorems, 4);
    assert!(report.uses_quot);
    assert_eq!(report.axioms.len(), 3);
    assert_eq!(report.non_standard_axioms, vec!["CustomAx", "sorryAx"]);
    assert_eq!(
        report.sorry_theorems,
        vec!["thm_via_custom", "thm_via_opaque", "thm_via_sorry"]
    );
    let sorry_usage = report.axioms.iter().find(|a| a.name == "sorryAx").unwrap();
    assert!(sorry_usage.is_sorry);
    assert_eq!(sorry_usage.dependent_theorems, 3);
    assert_eq!(sorry_usage.dependent_decls, 5); // helper_sorry, opaque_hiding_sorry, 3 theorems

    // 7. Policy enforcement.
    let strict = AxiomPolicy {
        allow_axioms: Some(vec!["propext".into()]),
        forbid_sorry: true,
    };
    let violations = check_axiom_policy(&report, &strict);
    assert!(violations.iter().any(|v| v.axiom == "sorryAx"));
    assert!(violations.iter().any(|v| v.axiom == "CustomAx"));
    assert!(!violations.iter().any(|v| v.axiom == "propext"));

    // Per-decl policy passes on pure_thm, fails on thm_via_sorry.
    assert!(check_decl_policy(&pure_info, &strict).is_empty());
    assert!(!check_decl_policy(&sorry_info, &strict).is_empty());
}

#[test]
fn real_init_prelude_audit_and_pretty_print() {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/data/Init.Prelude.ndjson.gz"
    );
    let out = std::process::Command::new("gzip")
        .args(["-dc", path])
        .output()
        .expect("run gzip");
    assert!(out.status.success());
    let text = String::from_utf8(out.stdout).unwrap();
    let (env, _stats) = parse_str(&text).expect("Init.Prelude must verify");

    let report = audit_environment(&env);
    assert!(report.uses_quot);
    assert!(report
        .axioms
        .iter()
        .any(|a| a.name == "Classical.choice" && a.is_standard));
    assert!(report
        .axioms
        .iter()
        .any(|a| a.name == "Quot.sound" && a.is_standard));
    assert!(
        report.sorry_theorems.is_empty(),
        "Init.Prelude should have no sorry theorems, found {:?}",
        report.sorry_theorems
    );
    // Real Init.Prelude declares sorryAx with 0 dependents; strict standard policy must pass!
    let standard_policy = AxiomPolicy {
        allow_axioms: Some(vec![
            "propext".into(),
            "Quot.sound".into(),
            "Classical.choice".into(),
        ]),
        forbid_sorry: true,
    };
    assert!(
        check_axiom_policy(&report, &standard_policy).is_empty(),
        "Init.Prelude must satisfy standard classical axiom policy with forbid_sorry"
    );

    let symm = lookup_name(&env, "Eq.symm").expect("Eq.symm must exist in Init.Prelude");
    let symm_info = inspect_decl(&env, symm).unwrap();
    assert_eq!(symm_info.kind, DeclKind::Theorem);
    assert!(symm_info.axioms.is_empty(), "Eq.symm is axiom-free");
    assert!(
        symm_info.ty.contains("Eq.{u} α b a"),
        "expected named binder resolution in Eq.symm type, got: {}",
        symm_info.ty
    );

    // Verify shortest_dependency_path, reverse_dependents, and list_decls on real Init.Prelude!
    let eq_id = lookup_name(&env, "Eq").expect("Eq must exist");
    let chain = rigor_parser::shortest_dependency_path(&env, symm, eq_id)
        .expect("Eq.symm must depend on Eq");
    assert_eq!(chain.first().map(String::as_str), Some("Eq.symm"));
    assert_eq!(chain.last().map(String::as_str), Some("Eq"));
    assert!(rigor_parser::reverse_dependents(&env, eq_id).contains(&"Eq.symm".to_string()));
    let eq_theorems = rigor_parser::list_decls(&env, Some(DeclKind::Theorem), Some("Eq."));
    assert!(eq_theorems.iter().any(|(n, _)| n == "Eq.symm"));
}

#[test]
fn pretty_printer_handles_exponential_dag_and_kernel_errors() {
    let mut arena = Arena::new();
    let nat_n = arena.name_from_path("Nat");
    let f_n = arena.name_from_path("MyMod.combine");
    let nat = arena.const_(nat_n, []);
    let f = arena.const_(f_n, []);
    // Build a 32-level diamond DAG (2^32 tree nodes, only 34 arena nodes!).
    let mut cur = nat;
    for _ in 0..32 {
        let app1 = arena.app(f, cur);
        cur = arena.app(app1, cur);
    }
    let rendered = format_expr_bounded(&arena, cur, 16, 128);
    assert!(
        rendered.len() <= 136,
        "bounded render must respect char limit: {rendered}"
    );
    assert!(rendered.ends_with("..."));

    // Verify format_kernel_error resolves names and expressions cleanly.
    let p_ty = arena.pi(nat_n, BinderInfo::Default, nat, nat);
    let err = KernelError::TypeMismatch {
        expected: p_ty,
        got: nat,
    };
    let msg = format_kernel_error(&arena, &err);
    assert!(
        msg.contains("Nat -> Nat"),
        "expected readable arrow type, got: {msg}"
    );
    assert!(!msg.contains("ExprId("));
}

#[test]
fn hostile_inputs_rejected_without_panic_or_oom() {
    // 1. Deeply nested JSON array -> LimitExceeded (no stack overflow).
    let deep_json = format!("{{\"meta\":{}{}}}", "[".repeat(300), "]".repeat(300));
    assert!(matches!(
        parse_str(&deep_json),
        Err(ParseError::LimitExceeded { .. })
    ));

    // 2. Sparse-ID OOM bomb in NDJSON -> LimitExceeded.
    let sparse_ndjson = "{\"in\":99999999,\"str\":{\"pre\":0,\"str\":\"boom\"}}";
    assert!(matches!(
        parse_str(sparse_ndjson),
        Err(ParseError::LimitExceeded { .. })
    ));

    // 3. Sparse-ID OOM bomb in text format -> LimitExceeded.
    let sparse_txt = "0.1.4\n99999999 #NS 0 boom\n";
    assert!(matches!(
        parse_str(sparse_txt),
        Err(ParseError::LimitExceeded { .. })
    ));

    // 4. Negative integer or float in ID/bvar fields -> Syntax error (not coerced to 0!).
    assert!(matches!(
        parse_str("{\"ie\":0,\"bvar\":-1}"),
        Err(ParseError::Syntax { .. })
    ));
    assert!(matches!(
        parse_str("{\"ie\":0,\"bvar\":1.5}"),
        Err(ParseError::Syntax { .. })
    ));
    // Negative/float inside ignored mdata IS still accepted.
    let valid_mdata =
        "{\"ie\":0,\"sort\":0}\n{\"ie\":1,\"mdata\":{\"data\":[{\"k\":-42,\"f\":1.5}],\"expr\":0}}";
    parse_str(valid_mdata).expect("negative/float inside mdata must remain valid");

    // 5. u32 overflow in bvar / proj.idx -> Syntax error (not silently truncated!).
    assert!(matches!(
        parse_str("{\"ie\":0,\"bvar\":4294967296}"),
        Err(ParseError::Syntax { .. })
    ));

    // 6. Trailing garbage after JSON root object -> Syntax error.
    assert!(matches!(
        parse_str("{\"meta\":{}} trailing_garbage"),
        Err(ParseError::Syntax { .. })
    ));

    // 7. Malformed escapes including backslash before multi-byte UTF-8 and at EOF -> Syntax error (no panic).
    for bad in [
        "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"abc\\",
        "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"\\é\"}}",
        "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"\\uD800\"}}",
        "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"\\uZZZZ\"}}",
    ] {
        assert!(
            matches!(parse_str(bad), Err(ParseError::Syntax { .. })),
            "must reject: {bad}"
        );
    }

    // 8. Allocation bomb in text #IND num_ctors -> Syntax error (no capacity overflow panic).
    let alloc_bomb = "0.1.4\n1 #NS 0 A\n0 #ES 0\n#IND 0 1 0 999999999999\n";
    assert!(matches!(
        parse_str(alloc_bomb),
        Err(ParseError::Syntax { .. })
    ));

    // 9. Oversized Nat literal exceeding custom ParseLimits -> LimitExceeded.
    let mut env = Environment::new();
    let limits = ParseLimits {
        max_nat_digits: 32,
        ..ParseLimits::default()
    };
    let big_nat = format!("{{\"ie\":0,\"natVal\":\"{}\"}}", "9".repeat(64));
    let res = StreamParser::with_limits(limits).parse_reader(big_nat.as_bytes(), &mut env);
    assert!(matches!(res, Err(ParseError::LimitExceeded { .. })));

    // 10. NDJSON mutual inductive consistency checks: orphan ctor, duplicate cidx, mismatched numParams.
    let orphan_ctor = "\
{\"in\":1,\"str\":{\"pre\":0,\"str\":\"A\"}}
{\"in\":2,\"str\":{\"pre\":0,\"str\":\"B\"}}
{\"in\":3,\"str\":{\"pre\":1,\"str\":\"mk\"}}
{\"ie\":0,\"sort\":0}
{\"ie\":1,\"const\":{\"name\":1,\"us\":[]}}
{\"inductive\":{\"types\":[{\"name\":1,\"levelParams\":[],\"type\":0,\"numParams\":0,\"numIndices\":0,\"all\":[1],\"ctors\":[3],\"numNested\":0,\"isRec\":false,\"isUnsafe\":false,\"isReflexive\":false}],\"ctors\":[{\"name\":3,\"levelParams\":[],\"type\":1,\"induct\":2,\"cidx\":0,\"numParams\":0,\"numFields\":0,\"isUnsafe\":false}],\"recs\":[]}}
";
    assert!(matches!(
        parse_str(orphan_ctor),
        Err(ParseError::Syntax { .. })
    ));

    let dup_cidx = "\
{\"in\":1,\"str\":{\"pre\":0,\"str\":\"A\"}}
{\"in\":2,\"str\":{\"pre\":1,\"str\":\"c0\"}}
{\"in\":3,\"str\":{\"pre\":1,\"str\":\"c1\"}}
{\"ie\":0,\"sort\":0}
{\"ie\":1,\"const\":{\"name\":1,\"us\":[]}}
{\"inductive\":{\"types\":[{\"name\":1,\"levelParams\":[],\"type\":0,\"numParams\":0,\"numIndices\":0,\"all\":[1],\"ctors\":[2,3],\"numNested\":0,\"isRec\":false,\"isUnsafe\":false,\"isReflexive\":false}],\"ctors\":[{\"name\":2,\"levelParams\":[],\"type\":1,\"induct\":1,\"cidx\":0,\"numParams\":0,\"numFields\":0,\"isUnsafe\":false},{\"name\":3,\"levelParams\":[],\"type\":1,\"induct\":1,\"cidx\":0,\"numParams\":0,\"numFields\":0,\"isUnsafe\":false}],\"recs\":[]}}
";
    assert!(matches!(
        parse_str(dup_cidx),
        Err(ParseError::Syntax { .. })
    ));

    // 11. Readable error formatting on kernel rejection.
    let bad_thm = "0.1.4\n1 #NS 0 T\n0 #ES 0\n1 #US 0\n1 #ES 1\n#THM 1 1 0\n";
    let mut env = Environment::new();
    let err = parse_and_check(bad_thm.as_bytes(), &mut env).unwrap_err();
    let rendered = format_parse_error(&env.arena, &err);
    assert!(
        rendered.contains("theorem 'T' must live in Prop"),
        "got: {rendered}"
    );
}

#[test]
fn deterministic_fuzz_mutated_inputs_never_panic() {
    let seeds = [
        "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"Nat\"}}\n{\"il\":1,\"succ\":0}\n{\"ie\":0,\"sort\":1}",
        "0.1.4\n1 #NS 0 Nat\n0 #ES 0\n#AX 1 0\n",
    ];
    let mut rng = 0x9E37_79B9_7F4A_7C15u64;
    let mut next = || {
        rng ^= rng << 13;
        rng ^= rng >> 7;
        rng ^= rng << 17;
        rng
    };
    let alphabet = b"{}[]:,\"\\-0123456789#NSIEAPZ \n\t\x7f";
    for i in 0..200 {
        let base = seeds[i % seeds.len()].as_bytes().to_vec();
        let mut mutated = base;
        let ops = (next() % 6) + 1;
        for _ in 0..ops {
            if mutated.is_empty() {
                break;
            }
            let pos = (next() as usize) % mutated.len();
            match next() % 3 {
                0 => mutated[pos] = alphabet[(next() as usize) % alphabet.len()],
                1 => mutated.truncate(pos),
                _ => mutated.insert(pos, alphabet[(next() as usize) % alphabet.len()]),
            }
        }
        if let Ok(s) = std::str::from_utf8(&mutated) {
            let _ = parse_str(s);
        }
    }
}

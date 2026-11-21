//! Phase 3 integration & soundness tests for the streaming `lean4export` parser.

use rigor_kernel::KernelError;
use rigor_parser::{parse_str, ParseError};

/// Full `Init`/`Std`-style `lean4export` module exercising ALL 22 directives:
/// `#NS`, `#NI`, `#US`, `#UM`, `#UIM`, `#UP`,
/// `#EV`, `#ES`, `#EC`, `#EA`, `#EL` (`#BD`/`#BI`/`#BS`/`#BC`), `#EP`, `#EZ`, `#EJ`, `#ELN`, `#ELS`,
/// `#AX`, `#DEF` (`O`/`A`/`R`), `#THM`, `#OPAQ`, `#QUOT`, `#IND`.
const INIT_STD_EXPORT: &str = "\
0.1.4
-- Names (#NS and #NI)
1 #NS 0 Nat
2 #NS 1 zero
3 #NS 1 succ
4 #NS 1 rec
5 #NS 1 add
6 #NS 0 Eq
7 #NS 6 refl
8 #NS 0 u
9 #NS 0 v
10 #NS 0 Prod
11 #NS 10 mk
12 #NS 0 String
13 #NS 0 Bool
14 #NS 13 false
15 #NS 13 true
16 #NS 0 Quot
17 #NS 16 mk
18 #NS 16 lift
19 #NS 0 Option
20 #NS 19 none
21 #NS 19 some
22 #NS 0 List
23 #NS 22 nil
24 #NS 22 cons
25 #NS 0 Std
26 #NS 25 greeting
27 #NS 25 pair_fst
28 #NS 25 add_2_3_eq_5
29 #NS 25 quot_compute
30 #NS 25 opaque_five
31 #NS 25 my_axiom
32 #NS 25 poly_id
33 #NS 25 binder_showcase
34 #NI 25 42
35 #NS 0 x
36 #NS 0 y
37 #NS 0 α
38 #NS 0 β
39 #NS 0 a
40 #NS 0 b
41 #NS 0 f
42 #NS 0 h
43 #NS 0 r
44 #NS 25 abbrev_two
45 #NS 25 opaque_hint_def

-- Universe levels (#US, #UM, #UIM, #UP)
1 #US 0
2 #US 1
3 #UP 8
4 #UP 9
5 #UM 3 4
6 #US 5
7 #UIM 3 4
8 #UM 1 1

-- Core sorts and bvars (#ES, #EV)
0 #ES 0
1 #ES 1
2 #ES 3
3 #ES 4
4 #ES 5
5 #EV 0
6 #EV 1
7 #EV 2
8 #EV 3
9 #EV 4

-- 1. Nat inductive (#IND with 0 params, 2 ctors)
10 #EC 1
11 #EP #BD 0 10 10
#IND 0 1 1 2 2 10 3 11

-- 2. Bool inductive
12 #EC 13
#IND 0 13 1 2 14 12 15 12

-- 3. Eq.{u} inductive (#IND with 2 params, 1 ctor, universe param u)
-- Eq : {α : Sort u} → α → α → Prop
13 #EP #BD 0 6 0
14 #EP #BD 0 5 13
15 #EP #BI 37 2 14
-- Eq.refl : {α : Sort u} → (a : α) → Eq.{u} α a a
16 #EC 6 3
17 #EA 16 6
18 #EA 17 5
19 #EA 18 5
20 #EP #BD 39 5 19
21 #EP #BI 37 2 20
#IND 2 6 15 1 7 21 8

-- 4. Quotient primitives (#QUOT)
#QUOT

-- 5. String (abstract type via #AX) + #ELS UTF-8 literal \"hello\"
#AX 12 1
22 #EC 12
23 #ELS 68 65 6c 6c 6f
24 #ELS
-- Std.greeting : String := \"hello\"
#DEF 26 22 23 R 1

-- 6. Prod.{u, v} inductive using #UM level
-- Prod : Type u → Type v → Type (max u v)  (here Sort u → Sort v → Sort (max u v) at Type level: u+1, v+1)
9 #US 3
10 #US 4
11 #UM 9 10
25 #ES 9
26 #ES 10
27 #ES 11
28 #EP #BD 38 26 27
29 #EP #BD 37 25 28
-- Prod.mk : (α : Type u) → (β : Type v) → α → β → Prod.{u,v} α β
30 #EC 10 3 4
31 #EA 30 8
32 #EA 31 7
33 #EP #BD 40 6 32
34 #EP #BD 39 6 33
35 #EP #BD 38 26 34
36 #EP #BD 37 25 35
#IND 2 10 29 1 11 36 8 9

-- 7. Option.{u} and List.{u} (#IND with 1 param)
-- Option : Type u → Type u
37 #EP #BD 37 25 25
38 #EC 19 3
39 #EA 38 5
40 #EP #BD 37 25 39
41 #EA 38 6
42 #EP #BD 39 5 41
43 #EP #BD 37 25 42
#IND 1 19 37 2 20 40 21 43 8

-- List : Type u → Type u
44 #EC 22 3
45 #EA 44 5
46 #EP #BD 37 25 45
-- cons : (α : Type u) → α → List α → List α
47 #EA 44 7
48 #EA 44 6
49 #EP #BD 0 48 47
50 #EP #BD 39 5 49
51 #EP #BD 37 25 50
#IND 1 22 37 2 23 46 24 51 8

-- 8. Nat.add via Nat.rec + #ELN literals
52 #EC 2
53 #EC 3
54 #EC 4 1
-- motive = λ (_ : Nat), Nat
55 #EL #BD 0 10 10
-- step = λ (_ : Nat) (ih : Nat), Nat.succ ih
56 #EA 53 5
57 #EL #BD 0 10 56
58 #EL #BD 0 10 57
-- body = Nat.rec.{1} motive #1 step #0
59 #EA 54 55
60 #EA 59 6
61 #EA 60 58
62 #EA 61 5
63 #EL #BD 36 10 62
64 #EL #BD 35 10 63
-- Nat → Nat → Nat
65 #EP #BD 0 10 11
#DEF 5 65 64 R 1

-- #ELN literals 2, 3, 5 + #DEF (A / O hints) + #OPAQ + #EZ let-expression
66 #ELN 2
67 #ELN 3
68 #ELN 5
-- Std.abbrev_two : Nat := 2 (hint A = Abbrev)
#DEF 44 10 66 A
-- Std.opaque_hint_def : Nat := 3 (hint O = Opaque)
#DEF 45 10 67 O
-- Std.opaque_five : Nat := let x : Nat := 2; Nat.add x 3 (#EZ + #OPAQ)
69 #EC 5
70 #EA 69 5
71 #EA 70 67
72 #EZ 35 10 66 71
#OPAQ 30 10 72

-- Theorem: Eq.{1} Nat (Nat.add 2 3) 5 (#THM using #ELN reduction!)
73 #EC 6 1
74 #EC 7 1
75 #EA 69 66
76 #EA 75 67
77 #EA 73 10
78 #EA 77 76
79 #EA 78 68
80 #EA 74 10
81 #EA 80 68
#THM 28 79 81

-- 9. Structure projection (#EJ) theorem:
-- (Prod.mk.{0,0} Nat Bool 2 Bool.true).0 = 2
82 #EC 11 0 0
83 #EC 15
84 #EA 82 10
85 #EA 84 12
86 #EA 85 66
87 #EA 86 83
88 #EJ 10 0 87
89 #EA 77 88
90 #EA 89 66
91 #EA 80 66
#THM 27 90 91

-- 10. Polymorphic identity + all 4 binder infos (#BD, #BI, #BS, #BC) + #UIM + #NI name
-- Std.poly_id.{u} : {α : Sort u} → α → α
92 #EP #BD 35 5 6
93 #EP #BI 37 2 92
94 #EL #BD 35 5 5
95 #EL #BI 37 2 94
#DEF 32 93 95 R 1 8

-- Std.42 : ∀ {{α : Sort u}} [x : α], α (exercises #NI, #BS, #BC, #UIM indirectly)
96 #EP #BC 35 5 6
97 #EP #BS 37 2 96
98 #EL #BC 35 5 5
99 #EL #BS 37 2 98
#DEF 34 97 99 R 1 8

-- 11. Quotient computation theorem:
-- Quot.lift.{1,1} (λ x : Nat, x) (λ a b (_ : Eq Nat a b), h) (Quot.mk Nat Eq 5) = 5
-- Here r = Eq.{1} Nat : Nat → Nat → Prop, f = λ x : Nat, x
-- h : ∀ (a b : Nat), Eq Nat a b → Eq Nat a b  := λ a b p, p
100 #EC 18 1 1
101 #EC 17 1
102 #EL #BD 35 10 5
-- h_val = λ (a : Nat) (b : Nat) (p : Eq Nat a b), p
103 #EA 77 6
104 #EA 103 5
105 #EL #BD 42 104 5
106 #EL #BD 40 10 105
107 #EL #BD 39 10 106
-- qmk = Quot.mk.{1} Nat (Eq.{1} Nat) 5
108 #EA 101 10
109 #EA 108 77
110 #EA 109 68
-- qlift = Quot.lift.{1,1} Nat (Eq.{1} Nat) Nat f h qmk
111 #EA 100 10
112 #EA 111 77
113 #EA 112 10
114 #EA 113 102
115 #EA 114 107
116 #EA 115 110
-- Eq.{1} Nat qlift 5 := Eq.refl.{1} Nat 5
117 #EA 77 116
118 #EA 117 68
#THM 29 118 81

-- 12. Axiom using #UIM sort
119 #ES 7
#AX 31 119 8 9
";

#[test]
fn test_full_init_std_lean4export_all_22_directives() {
    let (env, stats) = parse_str(INIT_STD_EXPORT).expect("full lean4export stream must verify cleanly");
    assert_eq!(stats.version.as_deref(), Some("0.1.4"));
    assert_eq!(stats.inductives, 6); // Nat, Bool, Eq, Prod, Option, List
    assert_eq!(stats.quots, 1);
    assert_eq!(stats.axioms, 2); // String, my_axiom
    assert_eq!(stats.defs, 6); // greeting, Nat.add, abbrev_two, opaque_hint_def, poly_id, Std.42
    assert_eq!(stats.opaques, 1); // opaque_five
    assert_eq!(stats.theorems, 3); // add_2_3_eq_5, pair_fst, quot_compute
    assert!(env.len() > 25);
}

#[test]
fn test_v3_lean4export_inductive_ctor_rec() {
    // Tests lean4export 3.x multi-line #IND + #CTOR + #REC format (validated by kernel).
    let src = "\
3.1.0
1 #NS 0 Nat
2 #NS 1 zero
3 #NS 1 succ
4 #NS 1 rec
1 #US 0
0 #ES 1
1 #EC 1
2 #EP #BD 0 1 1
#IND 1 0 1 0 0 0 1 1 2 2 3 0
#CTOR 2 1 1 0 0 0 0
#CTOR 3 2 1 1 0 1 0
#REC 4 0
";
    let (env, stats) = parse_str(src).expect("v3 #IND/#CTOR/#REC must verify via kernel");
    assert_eq!(stats.version.as_deref(), Some("3.1.0"));
    assert_eq!(stats.inductives, 1);
    assert!(env.len() == 4); // Nat, Nat.zero, Nat.succ, Nat.rec
}

#[test]
fn test_mutual_indm_even_odd() {
    let src = "\
0.1.4
1 #NS 0 Even
2 #NS 1 ez
3 #NS 1 es
4 #NS 0 Odd
5 #NS 4 os
1 #US 0
0 #ES 1
1 #EC 1
2 #EC 4
3 #EP #BD 0 2 1
4 #EP #BD 0 1 2
#INDM 0 2 1 0 2 2 1 3 3 4 0 1 5 4
";
    let (env, stats) = parse_str(src).expect("mutual #INDM Even/Odd must verify");
    assert_eq!(stats.inductives, 1);
    assert!(env.len() >= 7); // Even, Odd, ez, es, os, Even.rec, Odd.rec
}

#[test]
fn test_negative_lean4export_soundness_rejections() {
    // 1. Non-positive inductive via #IND MUST be rejected
    let non_pos = "\
0.1.4
1 #NS 0 False
2 #NS 0 Bad
3 #NS 2 mk
1 #US 0
0 #ES 0
1 #ES 1
2 #EC 1
3 #EC 2
4 #EP #BD 0 3 2
5 #EP #BD 0 4 3
#IND 0 1 0 0
#IND 0 2 1 1 3 5
";
    let err = parse_str(non_pos).unwrap_err();
    assert!(
        matches!(err, ParseError::Kernel { err: KernelError::NonPositiveInductive { .. }, .. }),
        "expected NonPositiveInductive, got {err}"
    );

    // 2. False Nat literal equality `2 = 3` MUST be rejected
    let bad_nat_eq = "\
0.1.4
1 #NS 0 Nat
2 #NS 1 zero
3 #NS 1 succ
4 #NS 0 Eq
5 #NS 4 refl
6 #NS 0 u
7 #NS 0 bad_thm
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
16 #ELN 2
17 #ELN 3
18 #EC 4 1
19 #EC 5 1
20 #EA 18 5
21 #EA 20 16
22 #EA 21 17
23 #EA 19 5
24 #EA 23 16
#THM 7 22 24
";
    let err = parse_str(bad_nat_eq).unwrap_err();
    assert!(
        matches!(err, ParseError::Kernel { err: KernelError::TypeMismatch { .. }, .. }),
        "expected TypeMismatch for 2 = 3, got {err}"
    );

    // 3. #THM whose type lives in Type 0 (not Prop) MUST be rejected
    let thm_in_type = "\
0.1.4
1 #NS 0 Nat
2 #NS 1 zero
3 #NS 1 succ
4 #NS 0 bad_thm
1 #US 0
0 #ES 1
1 #EC 1
2 #EP #BD 0 1 1
#IND 0 1 0 2 2 1 3 2
3 #ELN 0
#THM 4 1 3
";
    let err = parse_str(thm_in_type).unwrap_err();
    assert!(
        matches!(err, ParseError::Kernel { err: KernelError::TheoremNotInProp { .. }, .. }),
        "expected TheoremNotInProp, got {err}"
    );

    // 4. Bogus `Eq : Prop` followed by `#QUOT` MUST be rejected (kernel self-checks Quot types!)
    let bogus_quot = "\
0.1.4
1 #NS 0 Eq
0 #ES 0
#AX 1 0
#QUOT
";
    let err = parse_str(bogus_quot).unwrap_err();
    assert!(
        matches!(err, ParseError::Kernel { .. }),
        "expected Kernel error when Eq has bogus type before #QUOT, got {err}"
    );

    // 5. Type : Type (`Sort 1 : Sort 1`) MUST be rejected
    let type_in_type = "\
0.1.4
1 #NS 0 paradox
1 #US 0
0 #ES 1
#DEF 1 0 0 R 1
";
    let err = parse_str(type_in_type).unwrap_err();
    assert!(
        matches!(err, ParseError::Kernel { err: KernelError::TypeMismatch { .. }, .. }),
        "expected TypeMismatch for Type : Type, got {err}"
    );

    // 6. Malformed syntax / unknown ID / invalid UTF-8 in #ELS MUST be rejected
    assert!(matches!(parse_str("1 #EV 0\n2 #EA 1 99\n"), Err(ParseError::UnknownExprId { id: 99, .. })));
    assert!(matches!(parse_str("1 #ELS ff fe\n"), Err(ParseError::InvalidUtf8 { .. })));
    assert!(matches!(parse_str("1 #NOPE 0\n"), Err(ParseError::Syntax { .. })));
}

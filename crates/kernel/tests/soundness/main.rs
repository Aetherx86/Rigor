//! Phase 2 Soundness Torture Suite: negative tests that Rigor MUST strictly reject.
//!
//! Covers:
//! - Universe cycles (`Type : Type`, `Sort u : Sort u`, Girard's paradox via impredicative Type inductive)
//! - Non-strictly-positive inductive types (direct negative, double-negative, mutual negative, non-uniform params)
//! - Invalid large eliminations from `Prop` into `Type` (`Or.rec`, `Exists.rec`, `Proj` witness smuggling)
//! - Proof-irrelevance violations in `Type`
//! - Ill-typed recursor applications and malformed constructors

use rigor_kernel::{
    Arena, BinderInfo, Declaration, Environment, InductiveSpec, InductiveTypeSpec, KernelError,
    ReducibilityHint,
};

fn setup_false_bool_nat(env: &mut Environment) {
    let prop = env.arena.prop();
    let l1 = env.arena.lvl_nat(1);
    let type0 = env.arena.sort(l1);

    let false_n = env.arena.name_from_path("False");
    env.add_inductive(InductiveSpec {
        level_params: Box::new([]),
        num_params: 0,
        types: vec![InductiveTypeSpec { name: false_n, ty: prop, ctors: vec![] }],
    })
    .unwrap();

    let bool_n = env.arena.name_from_path("Bool");
    let true_n = env.arena.name_from_path("Bool.true");
    let false_b = env.arena.name_from_path("Bool.false");
    let bool_c = env.arena.const_(bool_n, []);
    env.add_inductive(InductiveSpec {
        level_params: Box::new([]),
        num_params: 0,
        types: vec![InductiveTypeSpec {
            name: bool_n,
            ty: type0,
            ctors: vec![(true_n, bool_c), (false_b, bool_c)],
        }],
    })
    .unwrap();

    let nat_n = env.arena.name_from_path("Nat");
    let z_n = env.arena.name_from_path("Nat.zero");
    let s_n = env.arena.name_from_path("Nat.succ");
    let nat_c = env.arena.const_(nat_n, []);
    let s_ty = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, nat_c, nat_c);
    env.add_inductive(InductiveSpec {
        level_params: Box::new([]),
        num_params: 0,
        types: vec![InductiveTypeSpec {
            name: nat_n,
            ty: type0,
            ctors: vec![(z_n, nat_c), (s_n, s_ty)],
        }],
    })
    .unwrap();
}

#[test]
fn rejects_universe_cycles_and_girard_impredicative_type_inductive() {
    let mut env = Environment::new();
    let l1 = env.arena.lvl_nat(1);
    let type0 = env.arena.sort(l1);
    let u = env.arena.name_from_path("u");
    let lu = env.arena.lvl_param(u);
    let su = env.arena.sort(lu);

    // 1. Direct `Type 0 : Type 0`
    let n1 = env.arena.name_from_path("bad_type_in_type");
    assert!(matches!(
        env.add_decl(Declaration::Definition {
            name: n1,
            level_params: Box::new([]),
            ty: type0,
            val: type0,
            hint: ReducibilityHint::Regular(0),
        }),
        Err(KernelError::TypeMismatch { .. })
    ));

    // 2. Polymorphic `Sort u : Sort u`
    let n2 = env.arena.name_from_path("bad_sort_u_in_u");
    assert!(matches!(
        env.add_decl(Declaration::Definition {
            name: n2,
            level_params: Box::new([u]),
            ty: su,
            val: su,
            hint: ReducibilityHint::Regular(0),
        }),
        Err(KernelError::TypeMismatch { .. })
    ));

    // 3. Girard's paradox via impredicative inductive in Type 0:
    //    inductive U : Type 0 | mk : Type 0 → U   (field `Type 0` has sort `Type 1` > `Type 0`!)
    let u_ind = env.arena.name_from_path("U");
    let u_mk = env.arena.name_from_path("U.mk");
    let u_c = env.arena.const_(u_ind, []);
    let mk_ty = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, type0, u_c);
    let err = env
        .add_inductive(InductiveSpec {
            level_params: Box::new([]),
            num_params: 0,
            types: vec![InductiveTypeSpec {
                name: u_ind,
                ty: type0,
                ctors: vec![(u_mk, mk_ty)],
            }],
        })
        .unwrap_err();
    assert_eq!(err, KernelError::UniverseTooSmall { ind: u_ind, ctor: u_mk });

    // 4. Polymorphic universe smuggling: `inductive Box.{u} : Sort u | mk : Sort u → Box.{u}`
    //    (`Sort u` has sort `Sort (u+1)`, NOT <= `u`!)
    let box_n = env.arena.name_from_path("Box");
    let box_mk = env.arena.name_from_path("Box.mk");
    let box_c = env.arena.const_(box_n, [lu]);
    let box_mk_ty = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, su, box_c);
    let err2 = env
        .add_inductive(InductiveSpec {
            level_params: Box::new([u]),
            num_params: 0,
            types: vec![InductiveTypeSpec {
                name: box_n,
                ty: su,
                ctors: vec![(box_mk, box_mk_ty)],
            }],
        })
        .unwrap_err();
    assert_eq!(err2, KernelError::UniverseTooSmall { ind: box_n, ctor: box_mk });
}

#[test]
fn rejects_non_positive_inductives_direct_double_mutual_and_non_uniform() {
    let mut env = Environment::new();
    setup_false_bool_nat(&mut env);
    let l1 = env.arena.lvl_nat(1);
    let type0 = env.arena.sort(l1);
    let false_c = env.arena.const_path("False", []);
    let nat_c = env.arena.const_path("Nat", []);

    // 1. Direct negative occurrence: `inductive Bad : Type 0 | mk : (Bad → False) → Bad`
    let bad = env.arena.name_from_path("Bad");
    let bad_mk = env.arena.name_from_path("Bad.mk");
    let bad_c = env.arena.const_(bad, []);
    let bad_to_false = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, bad_c, false_c);
    let bad_mk_ty = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, bad_to_false, bad_c);
    let err = env
        .add_inductive(InductiveSpec {
            level_params: Box::new([]),
            num_params: 0,
            types: vec![InductiveTypeSpec { name: bad, ty: type0, ctors: vec![(bad_mk, bad_mk_ty)] }],
        })
        .unwrap_err();
    assert_eq!(err, KernelError::NonPositiveInductive { ind: bad, ctor: bad_mk });

    // 2. Double-negative (positive but NOT strictly positive):
    //    `inductive Bad2 : Type 0 | mk : ((Bad2 → Nat) → Nat) → Bad2`
    let bad2 = env.arena.name_from_path("Bad2");
    let bad2_mk = env.arena.name_from_path("Bad2.mk");
    let bad2_c = env.arena.const_(bad2, []);
    let b2_to_nat = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, bad2_c, nat_c);
    let dbl_neg = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, b2_to_nat, nat_c);
    let bad2_mk_ty = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, dbl_neg, bad2_c);
    let err2 = env
        .add_inductive(InductiveSpec {
            level_params: Box::new([]),
            num_params: 0,
            types: vec![InductiveTypeSpec { name: bad2, ty: type0, ctors: vec![(bad2_mk, bad2_mk_ty)] }],
        })
        .unwrap_err();
    assert_eq!(err2, KernelError::NonPositiveInductive { ind: bad2, ctor: bad2_mk });

    // 3. Mutual negative cycle: A takes B positively, B takes (A → False) negatively!
    let ma = env.arena.name_from_path("MutA");
    let mb = env.arena.name_from_path("MutB");
    let ma_mk = env.arena.name_from_path("MutA.mk");
    let mb_mk = env.arena.name_from_path("MutB.mk");
    let ma_c = env.arena.const_(ma, []);
    let mb_c = env.arena.const_(mb, []);
    let ma_mk_ty = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, mb_c, ma_c);
    let ma_to_false = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, ma_c, false_c);
    let mb_mk_ty = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, ma_to_false, mb_c);
    let err3 = env
        .add_inductive(InductiveSpec {
            level_params: Box::new([]),
            num_params: 0,
            types: vec![
                InductiveTypeSpec { name: ma, ty: type0, ctors: vec![(ma_mk, ma_mk_ty)] },
                InductiveTypeSpec { name: mb, ty: type0, ctors: vec![(mb_mk, mb_mk_ty)] },
            ],
        })
        .unwrap_err();
    assert_eq!(err3, KernelError::NonPositiveInductive { ind: mb, ctor: mb_mk });

    // 4. Non-uniform parameter recursion:
    //    `inductive NonUnif (A : Type 0) : Type 0 | mk : NonUnif (A → A) → NonUnif A`
    let nu = env.arena.name_from_path("NonUnif");
    let nu_mk = env.arena.name_from_path("NonUnif.mk");
    let nu_c = env.arena.const_(nu, []);
    let b0 = env.arena.bvar(0);
    let b1 = env.arena.bvar(1);
    let nu_ty = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, type0, type0);
    let a_to_a = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, b0, b1);
    let nu_aa = env.arena.app(nu_c, a_to_a);
    let nu_a_shifted = env.arena.app(nu_c, b1);
    let nu_mk_body = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, nu_aa, nu_a_shifted);
    let nu_mk_ty = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, type0, nu_mk_body);
    let err4 = env
        .add_inductive(InductiveSpec {
            level_params: Box::new([]),
            num_params: 1,
            types: vec![InductiveTypeSpec { name: nu, ty: nu_ty, ctors: vec![(nu_mk, nu_mk_ty)] }],
        })
        .unwrap_err();
    assert_eq!(err4, KernelError::NonPositiveInductive { ind: nu, ctor: nu_mk });
}

#[test]
fn rejects_invalid_prop_to_type_large_eliminations_and_proj_witness_smuggling() {
    let mut env = Environment::new();
    setup_false_bool_nat(&mut env);
    let prop = env.arena.prop();
    let l1 = env.arena.lvl_nat(1);
    let type0 = env.arena.sort(l1);
    let bool_c = env.arena.const_path("Bool", []);
    let true_c = env.arena.const_path("Bool.true", []);
    let false_b = env.arena.const_path("Bool.false", []);
    let b0 = env.arena.bvar(0);
    let b1 = env.arena.bvar(1);
    let b2 = env.arena.bvar(2);
    let b3 = env.arena.bvar(3);

    // 1. `Or : Prop → Prop → Prop` has 2 constructors -> MUST NOT allow large elimination into Type!
    let or_n = env.arena.name_from_path("Or");
    let inl_n = env.arena.name_from_path("Or.inl");
    let inr_n = env.arena.name_from_path("Or.inr");
    let or_c = env.arena.const_(or_n, []);
    let or_ty = {
        let p2 = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, prop, prop);
        env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, prop, p2)
    };
    let inl_ty = {
        let ret = env.arena.app_n(or_c, &[b2, b1]);
        let fh = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, b1, ret);
        let pb = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, prop, fh);
        env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, prop, pb)
    };
    let inr_ty = {
        let ret = env.arena.app_n(or_c, &[b2, b1]);
        let fh = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, b0, ret);
        let pb = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, prop, fh);
        env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, prop, pb)
    };
    env.add_inductive(InductiveSpec {
        level_params: Box::new([]),
        num_params: 2,
        types: vec![InductiveTypeSpec {
            name: or_n,
            ty: or_ty,
            ctors: vec![(inl_n, inl_ty), (inr_n, inr_ty)],
        }],
    })
    .unwrap();

    // Or.rec must have 0 universe params (strictly Prop motive); passing level [1] must fail!
    let or_rec_n = env.arena.name_from_path("Or.rec");
    let or_rec_bad_lvl = env.arena.const_(or_rec_n, [l1]);
    let bad_or_n = env.arena.name_from_path("bad_or_large_elim");
    assert!(matches!(
        env.add_decl(Declaration::Definition {
            name: bad_or_n,
            level_params: Box::new([]),
            ty: type0,
            val: or_rec_bad_lvl,
            hint: ReducibilityHint::Regular(0),
        }),
        Err(KernelError::LevelParamCountMismatch { .. })
    ));

    // Trying to pass a Type-valued motive `fun _ => Bool` to `Or.rec` must fail with TypeMismatch!
    let p_ax = env.arena.name_from_path("P");
    env.add_decl(Declaration::Axiom { name: p_ax, level_params: Box::new([]), ty: prop }).unwrap();
    let p_c = env.arena.const_(p_ax, []);
    let or_pp = env.arena.app_n(or_c, &[p_c, p_c]);
    let bad_motive = env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, or_pp, bool_c);
    let or_rec0 = env.arena.const_(or_rec_n, []);
    let bad_call = env.arena.app_n(or_rec0, &[p_c, p_c, bad_motive]);
    let bad_or2 = env.arena.name_from_path("bad_or_motive");
    assert!(matches!(
        env.add_decl(Declaration::Definition {
            name: bad_or2,
            level_params: Box::new([]),
            ty: bool_c,
            val: bad_call,
            hint: ReducibilityHint::Regular(0),
        }),
        Err(KernelError::TypeMismatch { .. })
    ));

    // 2. `Exists (α : Type 0) (p : α → Prop) : Prop | intro (w : α) (h : p w) : Exists α p`
    //    Has 1 constructor, BUT field `w : α` is in Type 0 (not Prop) and NOT an index!
    let ex_n = env.arena.name_from_path("Exists");
    let ex_intro = env.arena.name_from_path("Exists.intro");
    let ex_c = env.arena.const_(ex_n, []);
    let ex_ty = {
        let p_ty = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, b0, prop);
        let pi_p = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, p_ty, prop);
        env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, type0, pi_p)
    };
    let ex_intro_ty = {
        // Under (α:#3) (p:#2) (w:#1) (h:#0): Exists α p
        let ret = env.arena.app_n(ex_c, &[b3, b2]);
        let pw = env.arena.app(b1, b0); // under α:#2, p:#1, w:#0
        let fh = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, pw, ret);
        let fw = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, b1, fh); // w : α (#1 under α, p)
        let p_ty = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, b0, prop);
        let fp = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, p_ty, fw);
        env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, type0, fp)
    };
    env.add_inductive(InductiveSpec {
        level_params: Box::new([]),
        num_params: 2,
        types: vec![InductiveTypeSpec {
            name: ex_n,
            ty: ex_ty,
            ctors: vec![(ex_intro, ex_intro_ty)],
        }],
    })
    .unwrap();

    // Verify Exists.rec has NO large-elimination universe parameter!
    let ex_rec_n = env.arena.name_from_path("Exists.rec");
    let ex_rec = env.get(ex_rec_n).unwrap();
    assert_eq!(ex_rec.level_params().len(), 0, "Exists.rec MUST NOT allow large elimination");

    // 3. Witness smuggling via `ExprData::Proj(Exists, 0, e)` MUST BE REJECTED!
    let always_true_n = env.arena.name_from_path("True");
    let trivial_n = env.arena.name_from_path("True.intro");
    let true_p = env.arena.const_(always_true_n, []);
    env.add_inductive(InductiveSpec {
        level_params: Box::new([]),
        num_params: 0,
        types: vec![InductiveTypeSpec {
            name: always_true_n,
            ty: prop,
            ctors: vec![(trivial_n, true_p)],
        }],
    })
    .unwrap();
    let trivial = env.arena.const_(trivial_n, []);
    let pred = env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, bool_c, true_p);
    let intro_c = env.arena.const_(ex_intro, []);
    let ex_proof = env.arena.app_n(intro_c, &[bool_c, pred, true_c, trivial]);
    let smuggled_bool = env.arena.proj(ex_n, 0, ex_proof);
    let smuggle_def = env.arena.name_from_path("smuggle_exists_witness");
    let err = env
        .add_decl(Declaration::Definition {
            name: smuggle_def,
            level_params: Box::new([]),
            ty: bool_c,
            val: smuggled_bool,
            hint: ReducibilityHint::Regular(0),
        })
        .unwrap_err();
    assert!(matches!(err, KernelError::InvalidProjection { .. }), "Proj must block Exists witness extraction, got {err:?}");
    let _ = false_b;
}

#[test]
fn rejects_proof_irrelevance_in_type_and_ill_typed_recursor_apps() {
    let mut env = Environment::new();
    setup_false_bool_nat(&mut env);

    // Add inductive Eq
    let u = env.arena.name_from_path("u");
    let lu = env.arena.lvl_param(u);
    let su = env.arena.sort(lu);
    let prop = env.arena.prop();
    let eq_n = env.arena.name_from_path("Eq");
    let refl_n = env.arena.name_from_path("Eq.refl");
    let b0 = env.arena.bvar(0);
    let b1 = env.arena.bvar(1);
    let eq_ty = {
        let tb = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, b1, prop);
        let ta = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, b0, tb);
        env.arena.pi(Arena::ANONYMOUS, BinderInfo::Implicit, su, ta)
    };
    let eq_c = env.arena.const_(eq_n, [lu]);
    let refl_ty = {
        let ret = env.arena.app_n(eq_c, &[b1, b0, b0]);
        let ta = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, b0, ret);
        env.arena.pi(Arena::ANONYMOUS, BinderInfo::Implicit, su, ta)
    };
    env.add_inductive(InductiveSpec {
        level_params: Box::new([u]),
        num_params: 2,
        types: vec![InductiveTypeSpec { name: eq_n, ty: eq_ty, ctors: vec![(refl_n, refl_ty)] }],
    })
    .unwrap();

    let l1 = env.arena.lvl_nat(1);
    let bool_c = env.arena.const_path("Bool", []);
    let true_c = env.arena.const_path("Bool.true", []);
    let false_c = env.arena.const_path("Bool.false", []);
    let nat_c = env.arena.const_path("Nat", []);
    let zero_c = env.arena.const_path("Nat.zero", []);

    // 1. Trying to prove `Eq Bool true false` by `Eq.refl Bool true` MUST fail!
    let eq1 = env.arena.const_(eq_n, [l1]);
    let refl1 = env.arena.const_(refl_n, [l1]);
    let bad_eq_ty = env.arena.app_n(eq1, &[bool_c, true_c, false_c]);
    let bad_eq_val = env.arena.app_n(refl1, &[bool_c, true_c]);
    let bad_eq_n = env.arena.name_from_path("true_eq_false");
    assert!(matches!(
        env.add_decl(Declaration::Theorem {
            name: bad_eq_n,
            level_params: Box::new([]),
            ty: bad_eq_ty,
            val: bad_eq_val,
        }),
        Err(KernelError::TypeMismatch { .. })
    ));

    // 2. Ill-typed Nat.rec application (minor premise for zero returns Bool instead of Nat)
    let nat_rec1 = env.arena.const_path("Nat.rec", [l1]);
    let motive = env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, nat_c, nat_c);
    let step_ih = env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, nat_c, b0);
    let step = env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, nat_c, step_ih);
    let ill_rec = env.arena.app_n(nat_rec1, &[motive, true_c, step, zero_c]);
    let ill_rec_n = env.arena.name_from_path("ill_typed_nat_rec");
    assert!(matches!(
        env.add_decl(Declaration::Definition {
            name: ill_rec_n,
            level_params: Box::new([]),
            ty: nat_c,
            val: ill_rec,
            hint: ReducibilityHint::Regular(0),
        }),
        Err(KernelError::TypeMismatch { .. })
    ));

    // 3. Ill-typed major premise (passing Bool to Nat.rec!)
    let ill_major = env.arena.app_n(nat_rec1, &[motive, zero_c, step, true_c]);
    let ill_major_n = env.arena.name_from_path("ill_major_nat_rec");
    assert!(matches!(
        env.add_decl(Declaration::Definition {
            name: ill_major_n,
            level_params: Box::new([]),
            ty: nat_c,
            val: ill_major,
            hint: ReducibilityHint::Regular(0),
        }),
        Err(KernelError::TypeMismatch { .. })
    ));
}

/// A field that only occurs *inside* a result index (`P (f n)`) is not determined by the index:
/// `f` need not be injective. Allowing large elimination there lets `P.rec` extract `n` from a
/// proof, and since any two proofs of `P (f 1)` and `P (f 2)` with `f 1 = f 2` are equal by proof
/// irrelevance, it would prove `1 = 2`. Lean only allows large elimination when the index *is*
/// the field. This is exactly the shape of `Int.NonNeg.mk (n : Nat) : Int.NonNeg (Int.ofNat n)`,
/// whose real Lean recursor has no universe parameter.
#[test]
fn rejects_large_elimination_when_a_field_only_occurs_inside_an_index() {
    let mut env = Environment::new();
    setup_false_bool_nat(&mut env);
    let prop = env.arena.prop();
    let l1 = env.arena.lvl_nat(1);
    let type0 = env.arena.sort(l1);
    let bool_c = env.arena.const_path("Bool", []);
    let nat_c = env.arena.const_path("Nat", []);
    let b0 = env.arena.bvar(0);

    // axiom f : Nat -> Bool (not injective in general)
    let f_n = env.arena.name_from_path("f");
    let f_ty = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, nat_c, bool_c);
    env.add_decl(Declaration::Axiom { name: f_n, level_params: Box::new([]), ty: f_ty }).unwrap();
    let f_c = env.arena.const_(f_n, []);

    // inductive P : Bool -> Prop | mk (n : Nat) : P (f n)
    let p_n = env.arena.name_from_path("P");
    let mk_n = env.arena.name_from_path("P.mk");
    let p_c = env.arena.const_(p_n, []);
    let p_ty = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, bool_c, prop);
    let f_n_app = env.arena.app(f_c, b0);
    let ret = env.arena.app(p_c, f_n_app);
    let mk_ty = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, nat_c, ret);
    env.add_inductive(InductiveSpec {
        level_params: Box::new([]),
        num_params: 0,
        types: vec![InductiveTypeSpec { name: p_n, ty: p_ty, ctors: vec![(mk_n, mk_ty)] }],
    })
    .unwrap();

    // P.rec must eliminate only into Prop: it has no universe parameter.
    let rec_n = env.arena.name_from_path("P.rec");
    let rec_large = env.arena.const_(rec_n, [l1]);
    let bad = env.arena.name_from_path("bad_nested_index_large_elim");
    assert!(matches!(
        env.add_decl(Declaration::Definition { name: bad, level_params: Box::new([]), ty: type0, val: rec_large, hint: ReducibilityHint::Regular(0) }),
        Err(KernelError::LevelParamCountMismatch { .. })
    ));

    // Control: when the index is the field itself (`Q n`), large elimination stays allowed.
    let q_n = env.arena.name_from_path("Q");
    let qmk_n = env.arena.name_from_path("Q.mk");
    let q_c = env.arena.const_(q_n, []);
    let q_ty = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, nat_c, prop);
    let q_ret = env.arena.app(q_c, b0);
    let qmk_ty = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, nat_c, q_ret);
    env.add_inductive(InductiveSpec {
        level_params: Box::new([]),
        num_params: 0,
        types: vec![InductiveTypeSpec { name: q_n, ty: q_ty, ctors: vec![(qmk_n, qmk_ty)] }],
    })
    .unwrap();
    let qrec_n = env.arena.name_from_path("Q.rec");
    assert_eq!(env.get(qrec_n).expect("Q.rec exists").level_params().len(), 1, "Q.rec eliminates into any Sort");
    assert_eq!(env.get(rec_n).expect("P.rec exists").level_params().len(), 0, "P.rec eliminates only into Prop");
}

/// Lean's unit-like rule: any two terms of a non-recursive structure with no fields are
/// definitionally equal (Lean's `Std.Rii α` relies on this). A structure *with* a field must not
/// get the same treatment.
#[test]
fn unit_like_structures_are_definitionally_equal_but_others_are_not() {
    let mut env = Environment::new();
    setup_false_bool_nat(&mut env);
    let prop = env.arena.prop();
    let l1 = env.arena.lvl_nat(1);
    let type0 = env.arena.sort(l1);
    let nat_c = env.arena.const_path("Nat", []);
    let b0 = env.arena.bvar(0);
    let b1 = env.arena.bvar(1);
    let b2 = env.arena.bvar(2);

    // structure U where (no fields);  structure W where val : Nat
    let u_n = env.arena.name_from_path("U");
    let umk_n = env.arena.name_from_path("U.mk");
    let u_c = env.arena.const_(u_n, []);
    env.add_inductive(InductiveSpec { level_params: Box::new([]), num_params: 0, types: vec![InductiveTypeSpec { name: u_n, ty: type0, ctors: vec![(umk_n, u_c)] }] }).unwrap();
    let w_n = env.arena.name_from_path("W");
    let wmk_n = env.arena.name_from_path("W.mk");
    let w_c = env.arena.const_(w_n, []);
    let wmk_ty = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, nat_c, w_c);
    env.add_inductive(InductiveSpec { level_params: Box::new([]), num_params: 0, types: vec![InductiveTypeSpec { name: w_n, ty: type0, ctors: vec![(wmk_n, wmk_ty)] }] }).unwrap();

    // For T in {U, W}: axiom P_T : T -> Prop, and  def cast_T : (a b : T) -> P_T a -> P_T b := fun a b h => h
    // type-checks exactly when `a` and `b` are definitionally equal.
    let check = |env: &mut Environment, t: rigor_kernel::ExprId, tag: &str| {
        let p_n = env.arena.name_from_path(&format!("P_{tag}"));
        let p_ty = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, t, prop);
        env.add_decl(Declaration::Axiom { name: p_n, level_params: Box::new([]), ty: p_ty }).unwrap();
        let p_c = env.arena.const_(p_n, []);
        // inside binders a(#1) b(#0): P a -> P b
        let pa = env.arena.app(p_c, b1);
        let pb_under = env.arena.app(p_c, b1); // under the extra `h` binder, b is #1
        let imp = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, pa, pb_under);
        let ty = {
            let inner = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, t, imp);
            env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, t, inner)
        };
        let val = {
            let pa_l = env.arena.app(p_c, b1);
            let h = env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, pa_l, b0);
            let lb = env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, t, h);
            env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, t, lb)
        };
        let _ = b2;
        let name = env.arena.name_from_path(&format!("cast_{tag}"));
        env.add_decl(Declaration::Definition { name, level_params: Box::new([]), ty, val, hint: ReducibilityHint::Regular(0) })
    };
    assert!(check(&mut env, u_c, "U").is_ok(), "terms of a field-less structure are equal");
    assert!(matches!(check(&mut env, w_c, "W"), Err(KernelError::TypeMismatch { .. })), "terms of a structure with a field are not");
}

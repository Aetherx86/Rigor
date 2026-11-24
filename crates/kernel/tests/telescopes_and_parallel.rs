//! Tests for batched `Lam`/`Pi`/`Let` telescopes, `infer_only` `App` spines,
//! trivial-case WHNF/infer fast paths, and deterministic coprime-stride parallel checking.

use rigor_kernel::{
    Arena, BinderInfo, Declaration, Environment, ExprId, InductiveSpec, InductiveTypeSpec,
    KernelError, ReducibilityHint, TypeChecker,
};

fn base_nat_eq_env() -> (Environment, ExprId, ExprId, ExprId, ExprId, ExprId) {
    let mut env = Environment::new();
    let l1 = env.arena.lvl_nat(1);
    let type0 = env.arena.sort(l1);
    let prop = env.arena.prop();

    let nat_n = env.arena.name_from_path("Nat");
    let z_n = env.arena.name_from_path("Nat.zero");
    let s_n = env.arena.name_from_path("Nat.succ");
    let nat = env.arena.const_(nat_n, []);
    let s_ty = env
        .arena
        .pi(Arena::ANONYMOUS, BinderInfo::Default, nat, nat);
    env.add_inductive(InductiveSpec {
        level_params: Box::new([]),
        num_params: 0,
        types: vec![InductiveTypeSpec {
            name: nat_n,
            ty: type0,
            ctors: vec![(z_n, nat), (s_n, s_ty)],
        }],
    })
    .unwrap();

    let u = env.arena.name_from_path("u");
    let lu = env.arena.lvl_param(u);
    let su = env.arena.sort(lu);
    let (b0, b1) = (env.arena.bvar(0), env.arena.bvar(1));
    let eq_n = env.arena.name_from_path("Eq");
    let refl_n = env.arena.name_from_path("Eq.refl");
    let eq_ty = {
        let tb = env
            .arena
            .pi(Arena::ANONYMOUS, BinderInfo::Default, b1, prop);
        let ta = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, b0, tb);
        env.arena.pi(Arena::ANONYMOUS, BinderInfo::Implicit, su, ta)
    };
    let eq_u = env.arena.const_(eq_n, [lu]);
    let refl_ty = {
        let ret = env.arena.app_n(eq_u, &[b1, b0, b0]);
        let ta = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, b0, ret);
        env.arena.pi(Arena::ANONYMOUS, BinderInfo::Implicit, su, ta)
    };
    env.add_inductive(InductiveSpec {
        level_params: Box::new([u]),
        num_params: 2,
        types: vec![InductiveTypeSpec {
            name: eq_n,
            ty: eq_ty,
            ctors: vec![(refl_n, refl_ty)],
        }],
    })
    .unwrap();

    let zero = env.arena.const_(z_n, []);
    let succ = env.arena.const_(s_n, []);
    let eq1 = env.arena.const_(eq_n, [l1]);
    let refl1 = env.arena.const_(refl_n, [l1]);
    (env, nat, zero, succ, eq1, refl1)
}

#[test]
fn batched_dependent_pi_lam_and_let_telescopes() {
    let (mut env, nat, zero, succ, eq1, refl1) = base_nat_eq_env();
    let prop = env.arena.prop();
    let b0 = env.arena.bvar(0);

    // 1. Deep dependent Pi + Lam telescope (16 binders):
    //    fun (x0 : Nat) (h0 : Eq Nat x0 x0) (x1 : Nat) (h1 : Eq Nat x1 x1) ... => Eq.refl Nat x0
    let mut ty = {
        // Under 16 binders (8 pairs of (x_i, h_i)), x0 is bvar(15)
        let x0 = env.arena.bvar(15);
        env.arena.app_n(eq1, &[nat, x0, x0])
    };
    let mut val = {
        let x0 = env.arena.bvar(15);
        env.arena.app_n(refl1, &[nat, x0])
    };
    for i in (0..8).rev() {
        let eq_self = env.arena.app_n(eq1, &[nat, b0, b0]);
        let xn = env.arena.name_from_path(&format!("x{i}"));
        let hn = env.arena.name_from_path(&format!("h{i}"));
        ty = env.arena.pi(hn, BinderInfo::Default, eq_self, ty);
        ty = env.arena.pi(xn, BinderInfo::Default, nat, ty);
        val = env.arena.lam(hn, BinderInfo::Default, eq_self, val);
        val = env.arena.lam(xn, BinderInfo::Default, nat, val);
    }
    let thm_name = env.arena.name_from_path("deep_dep_telescope");
    env.add_decl(Declaration::Theorem {
        name: thm_name,
        level_params: Box::new([]),
        ty,
        val,
    })
    .expect("16-binder dependent telescope theorem must verify");

    // 2. Chained dependent Let telescope where later lets and the return type reference earlier lets:
    //    let x0 : Nat := 0;
    //    let x1 : Nat := Nat.succ x0;
    //    let x2 : Nat := Nat.succ x1;
    //    Eq.refl Nat x2  :  Eq Nat (Nat.succ (Nat.succ 0)) (Nat.succ (Nat.succ 0))
    let one = env.arena.app(succ, zero);
    let two = env.arena.app(succ, one);
    let expected_ty = env.arena.app_n(eq1, &[nat, two, two]);
    let s_b0 = env.arena.app(succ, b0);
    let body = env.arena.app_n(refl1, &[nat, b0]);
    let let2 = env.arena.let_(Arena::ANONYMOUS, nat, s_b0, body);
    let let1 = env.arena.let_(Arena::ANONYMOUS, nat, s_b0, let2);
    let let0 = env.arena.let_(Arena::ANONYMOUS, nat, zero, let1);
    let let_thm = env.arena.name_from_path("chained_let_telescope");
    env.add_decl(Declaration::Theorem {
        name: let_thm,
        level_params: Box::new([]),
        ty: expected_ty,
        val: let0,
    })
    .expect("chained dependent let telescope must verify with zero dangling fvars");

    // 3. Ill-typed middle binder in a Let telescope must fail and leave TypeChecker locals clean.
    let bad_let = {
        let inner_ok = env.arena.let_(Arena::ANONYMOUS, nat, zero, b0);
        // Middle let gives `prop` (a Sort) as value of type `Nat`!
        let bad_mid = env.arena.let_(Arena::ANONYMOUS, nat, prop, inner_ok);
        env.arena.let_(Arena::ANONYMOUS, nat, zero, bad_mid)
    };
    let (mut arena, decls) = env.into_parts();
    let mut tc = TypeChecker::new(&decls, &mut arena);
    let err = tc.infer_type(bad_let).unwrap_err();
    assert!(matches!(err, KernelError::TypeMismatch { .. }));
    // Verify subsequent inference on a valid term succeeds (no leaked local context).
    let ok_ty = tc
        .infer_type(zero)
        .expect("locals must be clean after error");
    assert_eq!(ok_ty, nat);
}

#[test]
fn bindings_def_eq_and_proof_irrelevance_in_telescopes() {
    let (mut env, nat, zero, _succ, eq1, refl1) = base_nat_eq_env();
    let prop = env.arena.prop();
    let b0 = env.arena.bvar(0);
    let b1 = env.arena.bvar(1);

    // Two Pi telescopes differing only in binder names must be def-eq; differing in middle domain must not.
    let nx = env.arena.name_from_path("x");
    let ny = env.arena.name_from_path("y");
    let pi_1 = {
        let t2 = env.arena.app_n(eq1, &[nat, b1, b0]);
        let t1 = env.arena.pi(nx, BinderInfo::Default, nat, t2);
        env.arena.pi(nx, BinderInfo::Default, nat, t1)
    };
    let pi_2 = {
        let t2 = env.arena.app_n(eq1, &[nat, b1, b0]);
        let t1 = env.arena.pi(ny, BinderInfo::Implicit, nat, t2);
        env.arena.pi(ny, BinderInfo::Implicit, nat, t1)
    };
    let pi_bad = {
        let t1 = env.arena.pi(ny, BinderInfo::Default, prop, prop);
        env.arena.pi(ny, BinderInfo::Default, nat, t1)
    };

    // Two distinct proofs of the same universal Prop (`forall (x y : Nat), Eq Nat 0 0`) must be
    // def-eq via proof irrelevance even when their Lam bodies differ syntactically.
    let z_eq_z = env.arena.app_n(eq1, &[nat, zero, zero]);
    let r_z = env.arena.app_n(refl1, &[nat, zero]);
    let ax_n = env.arena.name_from_path("alt_proof");
    env.add_decl(Declaration::Axiom {
        name: ax_n,
        level_params: Box::new([]),
        ty: z_eq_z,
    })
    .unwrap();
    let alt_p = env.arena.const_(ax_n, []);
    let lam_p1 = {
        let inner = env.arena.lam(nx, BinderInfo::Default, nat, r_z);
        env.arena.lam(nx, BinderInfo::Default, nat, inner)
    };
    let lam_p2 = {
        let inner = env.arena.lam(ny, BinderInfo::Default, nat, alt_p);
        env.arena.lam(ny, BinderInfo::Default, nat, inner)
    };

    let (mut arena, decls) = env.into_parts();
    let mut tc = TypeChecker::new(&decls, &mut arena);
    assert!(tc.is_def_eq(pi_1, pi_2).unwrap());
    assert!(!tc.is_def_eq(pi_1, pi_bad).unwrap());
    assert!(tc.is_def_eq(lam_p1, lam_p2).unwrap());
}

#[test]
fn parallel_coprime_stride_matches_sequential_and_returns_earliest_error() {
    // Build an environment with 150 deferred theorems, injecting failures at indices 17, 63, and 121.
    // Every thread count (1, 2, 4, 8) MUST deterministically report the exact earliest failure (17).
    for threads in [1usize, 2, 4, 8] {
        let (mut env, nat, zero, succ, eq1, refl1) = base_nat_eq_env();
        let one = env.arena.app(succ, zero);
        env.set_deferred_checking(true);
        let mut expected_first_err = None;
        for i in 0..150usize {
            let name = env.arena.name_from_path(&format!("T.t{i}"));
            let k = env.arena.lit_nat(i as u128);
            let bad = matches!(i, 17 | 63 | 121);
            if i == 17 {
                expected_first_err = Some(name);
            }
            let (ty, val) = if bad {
                // Claim Eq Nat 0 1 with proof Eq.refl Nat 0 -> TypeMismatch
                (
                    env.arena.app_n(eq1, &[nat, zero, one]),
                    env.arena.app_n(refl1, &[nat, zero]),
                )
            } else {
                (
                    env.arena.app_n(eq1, &[nat, k, k]),
                    env.arena.app_n(refl1, &[nat, k]),
                )
            };
            env.add_decl(Declaration::Theorem {
                name,
                level_params: Box::new([]),
                ty,
                val,
            })
            .unwrap();
        }
        env.set_deferred_checking(false);
        let (err_name, err) = env
            .check_deferred(threads)
            .expect_err("batch with failing theorems must fail");
        assert_eq!(
            Some(err_name),
            expected_first_err,
            "threads={threads} must report exact earliest failing declaration (index 17)"
        );
        assert!(matches!(err, KernelError::TypeMismatch { .. }));
    }

    // Valid batch of 200 interdependent definitions and theorems across 1, 2, 4, 8 threads.
    for threads in [1usize, 2, 4, 8] {
        let (mut env, nat, _zero, _succ, eq1, refl1) = base_nat_eq_env();
        env.set_deferred_checking(true);
        for i in 0..200usize {
            let dn = env.arena.name_from_path(&format!("D.d{i}"));
            let tn = env.arena.name_from_path(&format!("D.t{i}"));
            let k = env.arena.lit_nat(i as u128);
            env.add_decl(Declaration::Definition {
                name: dn,
                level_params: Box::new([]),
                ty: nat,
                val: k,
                hint: ReducibilityHint::Regular(0),
            })
            .unwrap();
            let dc = env.arena.const_(dn, []);
            let ty = env.arena.app_n(eq1, &[nat, dc, k]);
            let val = env.arena.app_n(refl1, &[nat, k]);
            env.add_decl(Declaration::Theorem {
                name: tn,
                level_params: Box::new([]),
                ty,
                val,
            })
            .unwrap();
        }
        env.set_deferred_checking(false);
        env.check_deferred(threads)
            .expect("valid deferred batch must pass for all thread counts");
    }
}

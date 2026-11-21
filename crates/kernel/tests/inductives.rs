//! Phase 2 positive tests: inductive types, constructors, recursors, iota-reduction,
//! K-like reduction, structure projections, structure eta, indexed families, and mutual inductives.

use std::sync::Arc;

use rigor_kernel::{
    Arena, BinderInfo, Declaration, Environment, InductiveSpec, InductiveTypeSpec,
    ReducibilityHint, TypeChecker,
};

fn add_nat(env: &mut Environment) {
    let l1 = env.arena.lvl_nat(1);
    let type0 = env.arena.sort(l1);
    let nat_n = env.arena.name_from_path("Nat");
    let zero_n = env.arena.name_from_path("Nat.zero");
    let succ_n = env.arena.name_from_path("Nat.succ");
    let nat_c = env.arena.const_(nat_n, []);
    let succ_ty = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, nat_c, nat_c);
    env.add_inductive(InductiveSpec {
        level_params: Box::new([]),
        num_params: 0,
        types: vec![InductiveTypeSpec {
            name: nat_n,
            ty: type0,
            ctors: vec![(zero_n, nat_c), (succ_n, succ_ty)],
        }],
    })
    .expect("Nat inductive must succeed");
}

fn add_eq(env: &mut Environment) {
    // inductive Eq.{u} (α : Sort u) (a : α) : α → Prop | refl : Eq α a a
    let u = env.arena.name_from_path("u");
    let lu = env.arena.lvl_param(u);
    let su = env.arena.sort(lu);
    let prop = env.arena.prop();
    let eq_n = env.arena.name_from_path("Eq");
    let refl_n = env.arena.name_from_path("Eq.refl");
    let b0 = env.arena.bvar(0);
    let b1 = env.arena.bvar(1);

    let eq_ty_b = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, b1, prop);
    let eq_ty_a = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, b0, eq_ty_b);
    let eq_ty = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Implicit, su, eq_ty_a);

    let eq_c = env.arena.const_(eq_n, [lu]);
    let refl_ret = env.arena.app_n(eq_c, &[b1, b0, b0]);
    let refl_ty_a = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, b0, refl_ret);
    let refl_ty = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Implicit, su, refl_ty_a);

    env.add_inductive(InductiveSpec {
        level_params: Box::new([u]),
        num_params: 2,
        types: vec![InductiveTypeSpec {
            name: eq_n,
            ty: eq_ty,
            ctors: vec![(refl_n, refl_ty)],
        }],
    })
    .expect("Eq inductive must succeed");
}

#[test]
fn nat_recursor_iota_reduction_arithmetic_and_eq_k_reduction() {
    let mut env = Environment::new();
    add_nat(&mut env);
    add_eq(&mut env);

    let l1 = env.arena.lvl_nat(1);
    let type0 = env.arena.sort(l1);
    let nat_n = env.arena.name_from_path("Nat");
    let zero_n = env.arena.name_from_path("Nat.zero");
    let succ_n = env.arena.name_from_path("Nat.succ");
    let rec_n = env.arena.name_from_path("Nat.rec");
    let eq_n = env.arena.name_from_path("Eq");
    let refl_n = env.arena.name_from_path("Eq.refl");
    let eq_rec_n = env.arena.name_from_path("Eq.rec");

    let nat = env.arena.const_(nat_n, []);
    let zero = env.arena.const_(zero_n, []);
    let succ = env.arena.const_(succ_n, []);
    let rec1 = env.arena.const_(rec_n, [l1]);
    let b0 = env.arena.bvar(0);
    let b1 = env.arena.bvar(1);

    // def Nat.add : Nat → Nat → Nat :=
    //   fun a b => Nat.rec.{1} (fun _ => Nat) a (fun _ ih => Nat.succ ih) b
    let add_n = env.arena.name_from_path("Nat.add");
    let add_ty = {
        let inner = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, nat, nat);
        env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, nat, inner)
    };
    let motive = env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, nat, nat);
    let succ_b0 = env.arena.app(succ, b0);
    let step_ih = env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, nat, succ_b0);
    let step = env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, nat, step_ih);
    // Inside (a:#1) (b:#0): Nat.rec motive a step b
    let rec_call = env.arena.app_n(rec1, &[motive, b1, step, b0]);
    let add_lam_b = env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, nat, rec_call);
    let add_val = env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, nat, add_lam_b);
    env.add_decl(Declaration::Definition {
        name: add_n,
        level_params: Box::new([]),
        ty: add_ty,
        val: add_val,
        hint: ReducibilityHint::Regular(0),
    })
    .expect("Nat.add via Nat.rec must type-check");

    // def Nat.mul : Nat → Nat → Nat :=
    //   fun a b => Nat.rec.{1} (fun _ => Nat) zero (fun _ ih => Nat.add ih a) b
    let mul_n = env.arena.name_from_path("Nat.mul");
    let add_c = env.arena.const_(add_n, []);
    let b3 = env.arena.bvar(3);
    // Under (a:#3) (b:#2) (_:#1) (ih:#0): Nat.add ih a
    let add_ih_a = env.arena.app_n(add_c, &[b0, b3]);
    let m_ih = env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, nat, add_ih_a);
    let m_step = env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, nat, m_ih);
    let m_call = env.arena.app_n(rec1, &[motive, zero, m_step, b0]);
    let mul_b = env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, nat, m_call);
    let mul_val = env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, nat, mul_b);
    env.add_decl(Declaration::Definition {
        name: mul_n,
        level_params: Box::new([]),
        ty: add_ty,
        val: mul_val,
        hint: ReducibilityHint::Regular(0),
    })
    .expect("Nat.mul via Nat.rec must type-check");

    let mk_nat = |arena: &mut Arena, n: u32| {
        let mut x = zero;
        for _ in 0..n {
            x = arena.app(succ, x);
        }
        x
    };

    // Prove 3 * 4 + 2 = 14 by inductive Eq.refl!
    let n2 = mk_nat(&mut env.arena, 2);
    let n3 = mk_nat(&mut env.arena, 3);
    let n4 = mk_nat(&mut env.arena, 4);
    let n14 = mk_nat(&mut env.arena, 14);
    let mul_c = env.arena.const_(mul_n, []);
    let mul34 = env.arena.app_n(mul_c, &[n3, n4]);
    let lhs = env.arena.app_n(add_c, &[mul34, n2]);

    let eq1 = env.arena.const_(eq_n, [l1]);
    let refl1 = env.arena.const_(refl_n, [l1]);
    let thm_ty = env.arena.app_n(eq1, &[nat, lhs, n14]);
    let thm_val = env.arena.app_n(refl1, &[nat, n14]);
    let thm_n = env.arena.name_from_path("nat_arith_ok");
    env.add_decl(Declaration::Theorem {
        name: thm_n,
        level_params: Box::new([]),
        ty: thm_ty,
        val: thm_val,
    })
    .expect("3 * 4 + 2 = 14 must verify via iota reduction");

    // K-like reduction check: given an opaque axiom `h : Eq Nat 0 0`,
    // `Eq.rec.{1, 1} Nat 0 (fun _ _ => Nat) 4 0 h` must reduce definitionally to `4`!
    let h_ty = env.arena.app_n(eq1, &[nat, zero, zero]);
    let h_n = env.arena.name_from_path("h_opaque");
    env.add_decl(Declaration::Axiom { name: h_n, level_params: Box::new([]), ty: h_ty }).unwrap();
    let h_c = env.arena.const_(h_n, []);

    let eq_rec_11 = env.arena.const_(eq_rec_n, [l1, l1]);
    // motive : (x : Nat) → Eq Nat 0 x → Type 0 := fun _ _ => Nat
    let eq_0_x = env.arena.app_n(eq1, &[nat, zero, b0]);
    let m_inner = env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, eq_0_x, nat);
    let eq_motive = env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, nat, m_inner);
    let k_expr = env.arena.app_n(eq_rec_11, &[nat, zero, eq_motive, n4, zero, h_c]);
    let _ = type0;

    let frozen = env.freeze();
    let mut scratch = Arena::child(Arc::clone(&frozen.arena));
    let mut tc = TypeChecker::new(&frozen.decls, &mut scratch);
    assert!(
        tc.is_def_eq(k_expr, n4).unwrap(),
        "K-like reduction must reduce Eq.rec on opaque `h : 0 = 0` to minor premise"
    );
}

#[test]
fn structure_projections_and_structure_eta_on_prod() {
    let mut env = Environment::new();
    let u = env.arena.name_from_path("u");
    let v = env.arena.name_from_path("v");
    let lu = env.arena.lvl_param(u);
    let lv = env.arena.lvl_param(v);
    let lmax = env.arena.lvl_max(lu, lv);
    let su = env.arena.sort(lu);
    let sv = env.arena.sort(lv);
    let smax = env.arena.sort(lmax);

    let prod_n = env.arena.name_from_path("Prod");
    let mk_n = env.arena.name_from_path("Prod.mk");
    let b1 = env.arena.bvar(1);
    let b2 = env.arena.bvar(2);
    let b3 = env.arena.bvar(3);

    // inductive Prod.{u, v} (α : Sort u) (β : Sort v) : Sort (max u v)
    // | mk (fst : α) (snd : β) : Prod α β
    let prod_ty = {
        let p2 = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, sv, smax);
        env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, su, p2)
    };
    let prod_c = env.arena.const_(prod_n, [lu, lv]);
    let mk_ty = {
        // Under (α:#3) (β:#2) (fst:#1) (snd:#0): Prod α β
        let ret = env.arena.app_n(prod_c, &[b3, b2]);
        let f2 = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, b1, ret); // snd : β (#1 under α, β, fst)
        let f1 = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, b1, f2); // fst : α (#1 under α, β)
        let p2 = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, sv, f1);
        env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, su, p2)
    };
    env.add_inductive(InductiveSpec {
        level_params: Box::new([u, v]),
        num_params: 2,
        types: vec![InductiveTypeSpec {
            name: prod_n,
            ty: prod_ty,
            ctors: vec![(mk_n, mk_ty)],
        }],
    })
    .expect("Prod structure must succeed");

    // Concrete test with Nat
    add_nat(&mut env);
    let l1 = env.arena.lvl_nat(1);
    let nat = env.arena.const_path("Nat", []);
    let zero = env.arena.const_path("Nat.zero", []);
    let succ = env.arena.const_path("Nat.succ", []);
    let one = env.arena.app(succ, zero);

    let prod_11 = env.arena.const_(prod_n, [l1, l1]);
    let mk_11 = env.arena.const_(mk_n, [l1, l1]);
    let prod_nat = env.arena.app_n(prod_11, &[nat, nat]);

    let p_ax = env.arena.name_from_path("p");
    env.add_decl(Declaration::Axiom { name: p_ax, level_params: Box::new([]), ty: prod_nat }).unwrap();
    let p_c = env.arena.const_(p_ax, []);

    let pair = env.arena.app_n(mk_11, &[nat, nat, zero, one]);
    let proj0_pair = env.arena.proj(prod_n, 0, pair);
    let proj1_pair = env.arena.proj(prod_n, 1, pair);
    let p0 = env.arena.proj(prod_n, 0, p_c);
    let p1 = env.arena.proj(prod_n, 1, p_c);
    let eta_p = env.arena.app_n(mk_11, &[nat, nat, p0, p1]);

    let frozen = env.freeze();
    let mut scratch = Arena::child(Arc::clone(&frozen.arena));
    let mut tc = TypeChecker::new(&frozen.decls, &mut scratch);

    // Projection typing & reduction
    assert_eq!(tc.infer_type(proj0_pair).unwrap(), nat);
    assert!(tc.is_def_eq(proj0_pair, zero).unwrap());
    assert!(tc.is_def_eq(proj1_pair, one).unwrap());
    // Structure eta: Prod.mk (p.0) (p.1) ≡ p
    assert!(tc.is_def_eq(eta_p, p_c).unwrap());
    assert!(tc.is_def_eq(p_c, eta_p).unwrap());
}

#[test]
fn indexed_vec_and_mutual_even_odd_and_subsingleton_and() {
    let mut env = Environment::new();
    add_nat(&mut env);
    let l1 = env.arena.lvl_nat(1);
    let type0 = env.arena.sort(l1);
    let prop = env.arena.prop();
    let nat = env.arena.const_path("Nat", []);
    let zero = env.arena.const_path("Nat.zero", []);
    let succ = env.arena.const_path("Nat.succ", []);

    // 1. Indexed family: inductive Vec (α : Type 0) : Nat → Type 0
    //    | nil : Vec α 0
    //    | cons (n : Nat) (x : α) (xs : Vec α n) : Vec α (succ n)
    let vec_n = env.arena.name_from_path("Vec");
    let nil_n = env.arena.name_from_path("Vec.nil");
    let cons_n = env.arena.name_from_path("Vec.cons");
    let vec_c = env.arena.const_(vec_n, []);
    let b0 = env.arena.bvar(0);
    let b1 = env.arena.bvar(1);
    let b2 = env.arena.bvar(2);
    let b3 = env.arena.bvar(3);

    let vec_ty = {
        let idx = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, nat, type0);
        env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, type0, idx)
    };
    let nil_ty = {
        let ret = env.arena.app_n(vec_c, &[b0, zero]);
        env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, type0, ret)
    };
    let cons_ty = {
        // Under (α:#3) (n:#2) (x:#1) (xs:#0): Vec α (succ n)
        let sn = env.arena.app(succ, b2);
        let ret = env.arena.app_n(vec_c, &[b3, sn]);
        // xs : Vec α n (under α:#2, n:#1, x:#0)
        let xs_ty = env.arena.app_n(vec_c, &[b2, b1]);
        let f_xs = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, xs_ty, ret);
        let f_x = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, b1, f_xs);
        let f_n = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, nat, f_x);
        env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, type0, f_n)
    };
    env.add_inductive(InductiveSpec {
        level_params: Box::new([]),
        num_params: 1,
        types: vec![InductiveTypeSpec {
            name: vec_n,
            ty: vec_ty,
            ctors: vec![(nil_n, nil_ty), (cons_n, cons_ty)],
        }],
    })
    .expect("Indexed Vec inductive must succeed");

    // 2. Mutual inductive: Even / Odd : Nat → Prop
    let even_n = env.arena.name_from_path("Even");
    let odd_n = env.arena.name_from_path("Odd");
    let ev0_n = env.arena.name_from_path("Even.zero");
    let evs_n = env.arena.name_from_path("Even.succ");
    let ods_n = env.arena.name_from_path("Odd.succ");
    let even_c = env.arena.const_(even_n, []);
    let odd_c = env.arena.const_(odd_n, []);
    let nat_to_prop = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, nat, prop);

    let ev0_ty = env.arena.app(even_c, zero);
    let evs_ty = {
        // (n : Nat) → Odd n → Even (succ n)
        let odd_n_e = env.arena.app(odd_c, b0);
        let sn = env.arena.app(succ, b1);
        let ret = env.arena.app(even_c, sn);
        let pi_h = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, odd_n_e, ret);
        env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, nat, pi_h)
    };
    let ods_ty = {
        let even_n_e = env.arena.app(even_c, b0);
        let sn = env.arena.app(succ, b1);
        let ret = env.arena.app(odd_c, sn);
        let pi_h = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, even_n_e, ret);
        env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, nat, pi_h)
    };
    env.add_inductive(InductiveSpec {
        level_params: Box::new([]),
        num_params: 0,
        types: vec![
            InductiveTypeSpec { name: even_n, ty: nat_to_prop, ctors: vec![(ev0_n, ev0_ty), (evs_n, evs_ty)] },
            InductiveTypeSpec { name: odd_n, ty: nat_to_prop, ctors: vec![(ods_n, ods_ty)] },
        ],
    })
    .expect("Mutual Even/Odd inductive block must succeed");

    // 3. Subsingleton And : Prop → Prop → Prop CAN eliminate into Type!
    let and_n = env.arena.name_from_path("And");
    let intro_n = env.arena.name_from_path("And.intro");
    let and_c = env.arena.const_(and_n, []);
    let and_ty = {
        let p2 = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, prop, prop);
        env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, prop, p2)
    };
    let intro_ty = {
        let ret = env.arena.app_n(and_c, &[b3, b2]);
        let fb = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, b1, ret);
        let fa = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, b1, fb);
        let pb = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, prop, fa);
        env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, prop, pb)
    };
    env.add_inductive(InductiveSpec {
        level_params: Box::new([]),
        num_params: 2,
        types: vec![InductiveTypeSpec { name: and_n, ty: and_ty, ctors: vec![(intro_n, intro_ty)] }],
    })
    .expect("And inductive must succeed");
    let and_rec_n = env.arena.name_from_path("And.rec");
    let and_rec = env.get(and_rec_n).unwrap();
    assert_eq!(and_rec.level_params().len(), 1, "Subsingleton And.rec must allow large elimination");
}

#[test]
fn spine_machine_regression_overapplied_recursor_quot_and_lam_proof_irrelevance() {
    let mut env = Environment::new();
    add_nat(&mut env);
    add_eq(&mut env);
    env.add_quot().expect("add_quot must succeed");

    let l1 = env.arena.lvl_nat(1);
    let prop = env.arena.prop();
    let nat = env.arena.const_path("Nat", []);
    let zero = env.arena.const_path("Nat.zero", []);
    let succ = env.arena.const_path("Nat.succ", []);
    let rec1 = env.arena.const_path("Nat.rec", [l1]);
    let n2n = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, nat, nat);
    let b0 = env.arena.bvar(0);
    let b1 = env.arena.bvar(1);

    // 1. Over-applied higher-order `Nat.rec`: motive = (λ _, Nat → Nat), applied to trailing arg `7`!
    //    `Nat.rec (λ _, Nat → Nat) (λ x, x) (λ _ ih x, Nat.succ (ih x)) 3 7 == 10`
    //    Directly exercises `spine.splice` with non-empty `keep_tail` (`[7]`).
    let mot = env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, nat, n2n);
    let id_fn = env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, nat, b0);
    let ih_x = env.arena.app(b1, b0);
    let s_ih_x = env.arena.app(succ, ih_x);
    let st = env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, nat, s_ih_x);
    let st = env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, n2n, st);
    let st = env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, nat, st);
    let n3 = env.arena.lit_nat(3);
    let n7 = env.arena.lit_nat(7);
    let n10 = env.arena.lit_nat(10);
    let over_rec = env.arena.app_n(rec1, &[mot, id_fn, st, n3, n7]);

    // 2. Over-applied `Quot.lift`: returns `Nat → Nat` and is immediately applied to trailing arg `7`.
    //    `Quot.lift.{1,1} Nat (Eq.{1} Nat) (Nat → Nat) (λ x y, x) h (Quot.mk Nat (Eq Nat) 3) 7 == 3`
    let eq1 = env.arena.const_path("Eq", [l1]);
    let eq_nat = env.arena.app(eq1, nat);
    let eq_n2n = env.arena.app(eq1, n2n);
    let qmk = env.arena.const_path("Quot.mk", [l1]);
    let qlift = env.arena.const_path("Quot.lift", [l1, l1]);
    let eq_rec11 = env.arena.const_path("Eq.rec", [l1, l1]);
    // f : Nat → Nat → Nat := λ x _ => x
    let f_const = {
        let inner = env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, nat, b1);
        env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, nat, inner)
    };
    // h : ∀ a b, Eq Nat a b → Eq (Nat → Nat) (f a) (f b)
    //     := λ a b p => Eq.rec.{0,1} Nat a (λ y _, Eq (Nat → Nat) (f a) (f y)) (Eq.refl (Nat → Nat) (f a)) b p
    let eq_rec01 = env.arena.const_path("Eq.rec", [Arena::LEVEL_ZERO, l1]);
    let refl1 = env.arena.const_path("Eq.refl", [l1]);
    let h_proof = {
        // Under (a:#2) (b:#1) (p:#0):
        // motive (y:#1) (_:#0): Eq (Nat→Nat) (f a) (f y)  [a is #4 under y, _]
        let b2 = env.arena.bvar(2);
        let b3 = env.arena.bvar(3);
        let b4 = env.arena.bvar(4);
        let fa_m = env.arena.app(f_const, b4);
        let fy_m = env.arena.app(f_const, b1);
        let m_body = env.arena.app_n(eq_n2n, &[fa_m, fy_m]);
        let eq_a_y = env.arena.app_n(eq_nat, &[b3, b0]);
        let m_in = env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, eq_a_y, m_body);
        let m_out = env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, nat, m_in);
        let fa = env.arena.app(f_const, b2);
        let rfa = env.arena.app_n(refl1, &[n2n, fa]);
        let body = env.arena.app_n(eq_rec01, &[nat, b2, m_out, rfa, b1, b0]);
        let eq_ab = env.arena.app_n(eq_nat, &[b1, b0]);
        let lp = env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, eq_ab, body);
        let lb = env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, nat, lp);
        env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, nat, lb)
    };
    let _ = eq_rec11;
    let qmk3 = env.arena.app_n(qmk, &[nat, eq_nat, n3]);
    let over_quot = env.arena.app_n(qlift, &[nat, eq_nat, n2n, f_const, h_proof, qmk3, n7]);

    // 3. Proof irrelevance between two structurally distinct `Lam` proofs of `P → P` (deferred `is_proof` regression).
    let p_n = env.arena.name_from_path("P");
    let q_n = env.arena.name_from_path("Q");
    env.add_decl(Declaration::Axiom { name: p_n, level_params: Box::new([]), ty: prop }).unwrap();
    let p_c = env.arena.const_(p_n, []);
    env.add_decl(Declaration::Axiom { name: q_n, level_params: Box::new([]), ty: p_c }).unwrap();
    let q_c = env.arena.const_(q_n, []);
    let lam_proof_1 = env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, p_c, b0);
    let lam_proof_2 = env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, p_c, q_c);

    let frozen = env.freeze();
    let mut scratch = Arena::child(Arc::clone(&frozen.arena));
    let mut tc = TypeChecker::new(&frozen.decls, &mut scratch);
    assert!(tc.is_def_eq(over_rec, n10).unwrap(), "over-applied Nat.rec must reduce to 10");
    assert_eq!(tc.infer_type(over_quot).unwrap(), nat);
    assert!(tc.is_def_eq(over_quot, n3).unwrap(), "over-applied Quot.lift must reduce to 3");
    assert!(tc.is_def_eq(lam_proof_1, lam_proof_2).unwrap(), "distinct Lam proofs of P → P must be def-eq");
    let _ = zero;
}

//! Phase 1 unit & soundness tests: hash-consing, universe algebra, polymorphic identity,
//! dependent types (Leibniz equality), Church numerals, eta, proof irrelevance, and parallel checking.

use std::sync::Arc;

use rigor_kernel::{
    level_eq, level_is_nonzero, level_is_zero, level_leq, Arena, BinderInfo, Declaration,
    Environment, KernelError, ReducibilityHint, TypeChecker,
};

#[test]
fn arena_hash_consing_and_two_tier_child_sharing() {
    let mut base = Arena::new();
    let x = base.name_from_path("x");
    let x2 = base.name_str(Arena::ANONYMOUS, "x");
    assert_eq!(x, x2, "identical names must hash-cons to the same NameId");

    let l0 = base.lvl_zero();
    let l1 = base.lvl_succ(l0);
    let prop = base.sort(l0);
    let type0 = base.sort(l1);
    let id_ty = base.pi(x, BinderInfo::Default, prop, prop);
    let id_ty_2 = base.pi(x, BinderInfo::Default, prop, prop);
    assert_eq!(id_ty, id_ty_2, "structural equality is O(1) ExprId equality");
    assert_ne!(prop, type0);

    let shared = Arc::new(base);
    let mut child = Arena::child(Arc::clone(&shared));
    // Re-interning an existing node in a child arena reuses the exact parent ID.
    let prop_child = child.sort(Arena::LEVEL_ZERO);
    assert_eq!(prop_child, prop);
    let id_ty_child = child.pi(x, BinderInfo::Default, prop, prop);
    assert_eq!(id_ty_child, id_ty);
    // New nodes allocate above parent length without mutating parent.
    let fresh = child.pi(x, BinderInfo::Default, type0, type0);
    assert!(fresh.0 >= shared.expr_len());
}

#[test]
fn universe_level_normalization_and_inequality() {
    let mut a = Arena::new();
    let u_name = a.name_from_path("u");
    let v_name = a.name_from_path("v");
    let w_name = a.name_from_path("w");
    let z = a.lvl_zero();
    let one = a.lvl_nat(1);
    let two = a.lvl_nat(2);
    let u = a.lvl_param(u_name);
    let v = a.lvl_param(v_name);
    let w = a.lvl_param(w_name);
    let su = a.lvl_succ(u);
    let sv = a.lvl_succ(v);

    assert!(level_is_zero(&a, z));
    assert!(!level_is_zero(&a, u));
    assert!(level_is_nonzero(&a, one));
    assert!(level_is_nonzero(&a, su));
    assert!(!level_is_nonzero(&a, u));

    // imax(u, 0) = 0; imax(u, succ v) = max(u, succ v)
    assert_eq!(a.lvl_imax(u, z), z);
    let im_sv = a.lvl_imax(u, sv);
    let max_u_sv = a.lvl_max(u, sv);
    assert_eq!(im_sv, max_u_sv);

    // Commutativity and idempotence
    let max_uv = a.lvl_max(u, v);
    let max_vu = a.lvl_max(v, u);
    assert_eq!(max_uv, max_vu);
    assert!(level_eq(&mut a, max_uv, max_vu));

    // Inequalities
    assert!(level_leq(&mut a, z, u));
    assert!(level_leq(&mut a, u, su));
    assert!(!level_leq(&mut a, su, u));
    assert!(level_leq(&mut a, u, max_uv));
    assert!(!level_leq(&mut a, max_uv, u));
    assert!(level_leq(&mut a, one, two));
    assert!(!level_leq(&mut a, two, one));
    assert!(level_leq(&mut a, one, su));
    assert!(!level_leq(&mut a, two, su));

    // Non-trivial IMax case-splitting inequalities:
    // imax(u, v) <= max(u, v)
    let im_uv = a.lvl_imax(u, v);
    assert!(level_leq(&mut a, im_uv, max_uv));
    assert!(!level_leq(&mut a, max_uv, im_uv)); // fails when v = 0, u = 1

    // imax(u, max(v, w)) == max(imax(u, v), imax(u, w))
    let max_vw = a.lvl_max(v, w);
    let lhs = a.lvl_imax(u, max_vw);
    let im_uw = a.lvl_imax(u, w);
    let rhs = a.lvl_max(im_uv, im_uw);
    assert!(level_eq(&mut a, lhs, rhs));
}

#[test]
fn polymorphic_identity_and_composition() {
    let mut env = Environment::new();
    let u = env.arena.name_from_path("u");
    let v = env.arena.name_from_path("v");
    let w = env.arena.name_from_path("w");
    let lu = env.arena.lvl_param(u);
    let lv = env.arena.lvl_param(v);
    let lw = env.arena.lvl_param(w);
    let su = env.arena.sort(lu);
    let sv = env.arena.sort(lv);
    let sw = env.arena.sort(lw);

    let n_a = env.arena.name_from_path("α");
    let n_b = env.arena.name_from_path("β");
    let n_c = env.arena.name_from_path("γ");
    let n_x = env.arena.name_from_path("x");
    let n_f = env.arena.name_from_path("f");
    let n_g = env.arena.name_from_path("g");

    // def id.{u} : (α : Sort u) → α → α := fun α x => x
    let id_name = env.arena.name_from_path("id");
    let b0 = env.arena.bvar(0);
    let b1 = env.arena.bvar(1);
    let a_to_a = env.arena.pi(n_x, BinderInfo::Default, b0, b1);
    let id_ty = env.arena.pi(n_a, BinderInfo::Implicit, su, a_to_a);
    let lam_x = env.arena.lam(n_x, BinderInfo::Default, b0, b0);
    let id_val = env.arena.lam(n_a, BinderInfo::Implicit, su, lam_x);
    env.add_decl(Declaration::Definition {
        name: id_name,
        level_params: Box::new([u]),
        ty: id_ty,
        val: id_val,
        hint: ReducibilityHint::Regular(0),
    })
    .expect("polymorphic id must type-check");

    // def id_id.{u} : (α : Sort u) → α → α := id.{imax(u+1, u)} ((α : Sort u) → α → α) id.{u}
    // Note: `id_ty` has sort `Sort (imax (u+1) u)`, which collapses to `Prop` when `u = 0`.
    let id_id_name = env.arena.name_from_path("id_id");
    let lu_plus_1 = env.arena.lvl_succ(lu);
    let id_ty_lvl = env.arena.lvl_imax(lu_plus_1, lu);
    let id_at_ty = env.arena.const_(id_name, [id_ty_lvl]);
    let id_at_u = env.arena.const_(id_name, [lu]);
    let app1 = env.arena.app(id_at_ty, id_ty);
    let app2 = env.arena.app(app1, id_at_u);
    env.add_decl(Declaration::Definition {
        name: id_id_name,
        level_params: Box::new([u]),
        ty: id_ty,
        val: app2,
        hint: ReducibilityHint::Regular(0),
    })
    .expect("self-application of polymorphic id at Sort (imax (u+1) u) must type-check");

    // def comp.{u,v,w} : (α : Sort u) (β : Sort v) (γ : Sort w) (g : β → γ) (f : α → β) (x : α) → γ
    //   := fun α β γ g f x => g (f x)
    let comp_name = env.arena.name_from_path("comp");
    let b2 = env.arena.bvar(2);
    let b3 = env.arena.bvar(3);
    let b4 = env.arena.bvar(4);
    let b5 = env.arena.bvar(5);
    // Inside (α : Sort u) (β : Sort v) (γ : Sort w): α=#2, β=#1, γ=#0
    // Inside + (g : β → γ): α=#3, β=#2, γ=#1, g=#0
    // Inside + (f : α → β): α=#4, β=#3, γ=#2, g=#1, f=#0
    // Inside + (x : α): α=#5, β=#4, γ=#3, g=#2, f=#1, x=#0
    let g_ty = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, b1, b1); // β → γ (γ shifted by 1 -> b1!)
    let f_ty = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, b3, b3); // α → β (β shifted by 1 -> b3!)
    let x_to_c = env.arena.pi(n_x, BinderInfo::Default, b4, b3); // (x : α) → γ
    let pi_f = env.arena.pi(n_f, BinderInfo::Default, f_ty, x_to_c);
    let pi_g = env.arena.pi(n_g, BinderInfo::Default, g_ty, pi_f);
    let pi_c = env.arena.pi(n_c, BinderInfo::Implicit, sw, pi_g);
    let pi_b = env.arena.pi(n_b, BinderInfo::Implicit, sv, pi_c);
    let comp_ty = env.arena.pi(n_a, BinderInfo::Implicit, su, pi_b);

    let fx = env.arena.app(b1, b0);
    let gfx = env.arena.app(b2, fx);
    let lam_x = env.arena.lam(n_x, BinderInfo::Default, b4, gfx);
    let lam_f = env.arena.lam(n_f, BinderInfo::Default, f_ty, lam_x);
    let lam_g = env.arena.lam(n_g, BinderInfo::Default, g_ty, lam_f);
    let lam_c = env.arena.lam(n_c, BinderInfo::Implicit, sw, lam_g);
    let lam_b = env.arena.lam(n_b, BinderInfo::Implicit, sv, lam_c);
    let comp_val = env.arena.lam(n_a, BinderInfo::Implicit, su, lam_b);
    let _ = b5;

    env.add_decl(Declaration::Definition {
        name: comp_name,
        level_params: Box::new([u, v, w]),
        ty: comp_ty,
        val: comp_val,
        hint: ReducibilityHint::Regular(0),
    })
    .expect("polymorphic composition must type-check");
}

#[test]
fn leibniz_equality_and_church_numerals() {
    let mut env = Environment::new();
    let u = env.arena.name_from_path("u");
    let lu = env.arena.lvl_param(u);
    let su = env.arena.sort(lu);
    let prop = env.arena.prop();
    let l1 = env.arena.lvl_nat(1);
    let type0 = env.arena.sort(l1);

    let n_a = env.arena.name_from_path("α");
    let n_x = env.arena.name_from_path("x");
    let n_y = env.arena.name_from_path("y");
    let n_p = env.arena.name_from_path("P");
    let n_h = env.arena.name_from_path("h");
    let n_f = env.arena.name_from_path("f");
    let n_n = env.arena.name_from_path("n");
    let n_m = env.arena.name_from_path("m");

    let b0 = env.arena.bvar(0);
    let b1 = env.arena.bvar(1);
    let b2 = env.arena.bvar(2);
    let b3 = env.arena.bvar(3);
    let b4 = env.arena.bvar(4);

    // def Eq.{u} (α : Sort u) (x y : α) : Prop := ∀ (P : α → Prop), P x → P y
    let eq_name = env.arena.name_from_path("Eq");
    let eq_ty_y = env.arena.pi(n_y, BinderInfo::Default, b1, prop);
    let eq_ty_x = env.arena.pi(n_x, BinderInfo::Default, b0, eq_ty_y);
    let eq_ty = env.arena.pi(n_a, BinderInfo::Implicit, su, eq_ty_x);

    // Body under (α:#2) (x:#1) (y:#0): P : α → Prop, then under P:#0 (α:#3, x:#2, y:#1): P x → P y
    let p_ty = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, b2, prop);
    let px = env.arena.app(b0, b2);
    let py_shifted = env.arena.app(b1, b2); // under h : P x, P is #1, y is #2
    let px_to_py = env.arena.pi(n_h, BinderInfo::Default, px, py_shifted);
    let eq_body = env.arena.pi(n_p, BinderInfo::Default, p_ty, px_to_py);
    let eq_val_y = env.arena.lam(n_y, BinderInfo::Default, b1, eq_body);
    let eq_val_x = env.arena.lam(n_x, BinderInfo::Default, b0, eq_val_y);
    let eq_val = env.arena.lam(n_a, BinderInfo::Implicit, su, eq_val_x);
    env.add_decl(Declaration::Definition {
        name: eq_name,
        level_params: Box::new([u]),
        ty: eq_ty,
        val: eq_val,
        hint: ReducibilityHint::Regular(0),
    })
    .expect("Leibniz Eq must type-check in Prop");

    // theorem Eq.refl.{u} (α : Sort u) (x : α) : Eq.{u} α x x := fun P h => h
    let refl_name = env.arena.name_from_path("Eq.refl");
    let eq_u = env.arena.const_(eq_name, [lu]);
    let eq_a_x_x = env.arena.app_n(eq_u, &[b1, b0, b0]);
    let refl_ty_x = env.arena.pi(n_x, BinderInfo::Default, b0, eq_a_x_x);
    let refl_ty = env.arena.pi(n_a, BinderInfo::Implicit, su, refl_ty_x);

    // Under (α:#1) (x:#0): P : α → Prop (α is #1)
    let p_ty_r = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, b1, prop);
    let px_r = env.arena.app(b0, b1);
    let lam_h = env.arena.lam(n_h, BinderInfo::Default, px_r, b0);
    let lam_p = env.arena.lam(n_p, BinderInfo::Default, p_ty_r, lam_h);
    let lam_x = env.arena.lam(n_x, BinderInfo::Default, b0, lam_p);
    let refl_val = env.arena.lam(n_a, BinderInfo::Implicit, su, lam_x);
    env.add_decl(Declaration::Theorem {
        name: refl_name,
        level_params: Box::new([u]),
        ty: refl_ty,
        val: refl_val,
    })
    .expect("Eq.refl theorem must type-check");

    // Church numerals:
    // def CNat : Type 1 := ∀ (α : Type 0), (α → α) → α → α
    let l2 = env.arena.lvl_nat(2);
    let type1 = env.arena.sort(l2);
    let cnat_name = env.arena.name_from_path("CNat");
    let a_to_a = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, b0, b1);
    let a_to_a_shifted = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, b1, b2);
    let f_to_a_to_a = env.arena.pi(n_f, BinderInfo::Default, a_to_a, a_to_a_shifted);
    let cnat_val = env.arena.pi(n_a, BinderInfo::Default, type0, f_to_a_to_a);
    env.add_decl(Declaration::Definition {
        name: cnat_name,
        level_params: Box::new([]),
        ty: type1,
        val: cnat_val,
        hint: ReducibilityHint::Regular(0),
    })
    .expect("CNat must type-check");
    let cnat = env.arena.const_(cnat_name, []);

    // Helper to build Church numeral `k`: fun (α : Type 0) (f : α → α) (x : α) => f^k x
    let make_church = |arena: &mut Arena, k: u32| {
        let mut body = b0;
        for _ in 0..k {
            body = arena.app(b1, body);
        }
        let lx = arena.lam(n_x, BinderInfo::Default, b1, body);
        let lf = arena.lam(n_f, BinderInfo::Default, a_to_a, lx);
        arena.lam(n_a, BinderInfo::Default, type0, lf)
    };

    // def add : CNat → CNat → CNat := fun n m α f x => n α f (m α f x)
    let add_name = env.arena.name_from_path("add");
    let cnat_to_cnat = env.arena.pi(n_m, BinderInfo::Default, cnat, cnat);
    let add_ty = env.arena.pi(n_n, BinderInfo::Default, cnat, cnat_to_cnat);
    // Inside (n:#4) (m:#3) (α:#2) (f:#1) (x:#0): n α f (m α f x)
    let m_a_f_x = env.arena.app_n(b3, &[b2, b1, b0]);
    let n_a_f_m = env.arena.app_n(b4, &[b2, b1, m_a_f_x]);
    let add_body = env.arena.lam(n_x, BinderInfo::Default, b1, n_a_f_m);
    let add_body = env.arena.lam(n_f, BinderInfo::Default, a_to_a, add_body);
    let add_body = env.arena.lam(n_a, BinderInfo::Default, type0, add_body);
    let add_body = env.arena.lam(n_m, BinderInfo::Default, cnat, add_body);
    let add_val = env.arena.lam(n_n, BinderInfo::Default, cnat, add_body);
    env.add_decl(Declaration::Definition {
        name: add_name,
        level_params: Box::new([]),
        ty: add_ty,
        val: add_val,
        hint: ReducibilityHint::Regular(0),
    })
    .expect("Church add must type-check");

    // def mul : CNat → CNat → CNat := fun n m α f => n α (m α f)
    let mul_name = env.arena.name_from_path("mul");
    // Inside (n:#3) (m:#2) (α:#1) (f:#0): n α (m α f)
    let m_a_f = env.arena.app_n(b2, &[b1, b0]);
    let n_a_maf = env.arena.app_n(b3, &[b1, m_a_f]);
    let mul_body = env.arena.lam(n_f, BinderInfo::Default, a_to_a, n_a_maf);
    let mul_body = env.arena.lam(n_a, BinderInfo::Default, type0, mul_body);
    let mul_body = env.arena.lam(n_m, BinderInfo::Default, cnat, mul_body);
    let mul_val = env.arena.lam(n_n, BinderInfo::Default, cnat, mul_body);
    env.add_decl(Declaration::Definition {
        name: mul_name,
        level_params: Box::new([]),
        ty: add_ty,
        val: mul_val,
        hint: ReducibilityHint::Regular(0),
    })
    .expect("Church mul must type-check");

    // Prove theorem `mul_add_check : Eq.{2} CNat (add (mul 3 4) 2) 14 := Eq.refl.{2} CNat 14`
    let add_c = env.arena.const_(add_name, []);
    let mul_c = env.arena.const_(mul_name, []);
    let c2 = make_church(&mut env.arena, 2);
    let c3 = make_church(&mut env.arena, 3);
    let c4 = make_church(&mut env.arena, 4);
    let c14 = make_church(&mut env.arena, 14);
    let mul_3_4 = env.arena.app_n(mul_c, &[c3, c4]);
    let lhs = env.arena.app_n(add_c, &[mul_3_4, c2]);

    let eq_2 = env.arena.const_(eq_name, [l2]);
    let refl_2 = env.arena.const_(refl_name, [l2]);
    let thm_ty = env.arena.app_n(eq_2, &[cnat, lhs, c14]);
    let thm_val = env.arena.app_n(refl_2, &[cnat, c14]);
    let thm_name = env.arena.name_from_path("mul_add_check");
    env.add_decl(Declaration::Theorem {
        name: thm_name,
        level_params: Box::new([]),
        ty: thm_ty,
        val: thm_val,
    })
    .expect("Church arithmetic theorem add (mul 3 4) 2 = 14 must verify by refl");
}

#[test]
fn eta_conversion_proof_irrelevance_let_and_opaque() {
    let mut env = Environment::new();
    let prop = env.arena.prop();
    let l1 = env.arena.lvl_nat(1);
    let type0 = env.arena.sort(l1);

    // Axioms: A : Type 0, a1 a2 : A, f : A → A, P : Prop, p1 p2 : P
    let n_a = env.arena.name_from_path("A");
    let n_a1 = env.arena.name_from_path("a1");
    let n_a2 = env.arena.name_from_path("a2");
    let n_f = env.arena.name_from_path("f");
    let n_p = env.arena.name_from_path("P");
    let n_p1 = env.arena.name_from_path("p1");
    let n_p2 = env.arena.name_from_path("p2");

    env.add_decl(Declaration::Axiom { name: n_a, level_params: Box::new([]), ty: type0 }).unwrap();
    let ca = env.arena.const_(n_a, []);
    env.add_decl(Declaration::Axiom { name: n_a1, level_params: Box::new([]), ty: ca }).unwrap();
    env.add_decl(Declaration::Axiom { name: n_a2, level_params: Box::new([]), ty: ca }).unwrap();
    let a_to_a = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, ca, ca);
    env.add_decl(Declaration::Axiom { name: n_f, level_params: Box::new([]), ty: a_to_a }).unwrap();
    env.add_decl(Declaration::Axiom { name: n_p, level_params: Box::new([]), ty: prop }).unwrap();
    let cp = env.arena.const_(n_p, []);
    env.add_decl(Declaration::Axiom { name: n_p1, level_params: Box::new([]), ty: cp }).unwrap();
    env.add_decl(Declaration::Axiom { name: n_p2, level_params: Box::new([]), ty: cp }).unwrap();

    // Opaque definition must NOT unfold in is_def_eq.
    let n_op = env.arena.name_from_path("secret_a");
    let ca1 = env.arena.const_(n_a1, []);
    let ca2 = env.arena.const_(n_a2, []);
    env.add_decl(Declaration::Opaque {
        name: n_op,
        level_params: Box::new([]),
        ty: ca,
        val: ca1,
    })
    .unwrap();
    let cop = env.arena.const_(n_op, []);

    let cf = env.arena.const_(n_f, []);
    let b0 = env.arena.bvar(0);
    let fx = env.arena.app(cf, b0);
    let eta_f = env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, ca, fx);
    let cp1 = env.arena.const_(n_p1, []);
    let cp2 = env.arena.const_(n_p2, []);
    let let_expr = env.arena.let_(Arena::ANONYMOUS, ca, ca1, b0);

    let frozen = env.freeze();
    let mut scratch = Arena::child(Arc::clone(&frozen.arena));
    let mut tc = TypeChecker::new(&frozen.decls, &mut scratch);

    // Proof irrelevance in Prop: p1 ≡ p2, while in Type 0: a1 ≠ a2
    assert!(tc.is_def_eq(cp1, cp2).unwrap(), "proofs in Prop must be def-eq");
    assert!(!tc.is_def_eq(ca1, ca2).unwrap(), "distinct axioms in Type 0 must not be def-eq");

    // Eta conversion for functions: (fun x => f x) ≡ f and f ≡ (fun x => f x)
    assert!(tc.is_def_eq(eta_f, cf).unwrap());
    assert!(tc.is_def_eq(cf, eta_f).unwrap());

    // Zeta reduction: (let x : A := a1 in x) ≡ a1
    assert!(tc.is_def_eq(let_expr, ca1).unwrap());

    // Opaque stays opaque
    assert!(!tc.is_def_eq(cop, ca1).unwrap());
}

#[test]
fn rejects_ill_typed_terms_and_universe_violations() {
    let mut env = Environment::new();
    let l1 = env.arena.lvl_nat(1);
    let type0 = env.arena.sort(l1);
    let prop = env.arena.prop();

    // 1. Type 0 : Type 0 must fail (predicative universe hierarchy: Type 0 : Type 1).
    let bad_u = env.arena.name_from_path("type_in_type");
    let err = env
        .add_decl(Declaration::Definition {
            name: bad_u,
            level_params: Box::new([]),
            ty: type0,
            val: type0,
            hint: ReducibilityHint::Regular(0),
        })
        .unwrap_err();
    assert!(matches!(err, KernelError::TypeMismatch { .. }));

    // 2. Theorem living in Type 0 (not Prop) must fail.
    let bad_thm = env.arena.name_from_path("thm_in_type");
    let err = env
        .add_decl(Declaration::Theorem {
            name: bad_thm,
            level_params: Box::new([]),
            ty: type0,
            val: prop,
        })
        .unwrap_err();
    assert!(matches!(err, KernelError::TheoremNotInProp { .. }));

    // 3. Unbound universe parameter must fail.
    let u = env.arena.name_from_path("u");
    let lu = env.arena.lvl_param(u);
    let su = env.arena.sort(lu);
    let bad_lvl = env.arena.name_from_path("unbound_lvl");
    let err = env
        .add_decl(Declaration::Axiom {
            name: bad_lvl,
            level_params: Box::new([]),
            ty: su,
        })
        .unwrap_err();
    assert_eq!(err, KernelError::UnboundLevelParam(u));

    // 4. Unbound de Bruijn variable must fail.
    let b0 = env.arena.bvar(0);
    let bad_bvar = env.arena.name_from_path("unbound_bvar");
    let err = env
        .add_decl(Declaration::Axiom {
            name: bad_bvar,
            level_params: Box::new([]),
            ty: b0,
        })
        .unwrap_err();
    assert_eq!(err, KernelError::UnboundBVar(0));
}

#[test]
fn parallel_batch_checking_with_thread_local_scratch_arenas() {
    let mut env = Environment::new();
    let prop = env.arena.prop();
    let n_p = env.arena.name_from_path("P");
    let b0 = env.arena.bvar(0);
    let b1 = env.arena.bvar(1);
    let p_to_p = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, b0, b1);
    let id_prop_ty = env.arena.pi(n_p, BinderInfo::Default, prop, p_to_p);
    let lam_h = env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, b0, b0);
    let id_prop_val = env.arena.lam(n_p, BinderInfo::Default, prop, lam_h);

    let mut batch = Vec::new();
    for i in 0..64u64 {
        let name = env.arena.name_num(Arena::ANONYMOUS, i + 1);
        batch.push(Declaration::Theorem {
            name,
            level_params: Box::new([]),
            ty: id_prop_ty,
            val: id_prop_val,
        });
    }
    let frozen = env.freeze();
    let res = frozen.check_batch_parallel(&batch, 4);
    assert_eq!(res.len(), 64);
    assert!(res.iter().all(|r| r.is_ok()));
}

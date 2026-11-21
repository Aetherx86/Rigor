//! Phase 1 micro-benchmarks: hash-consing throughput, heavy Church numeral reduction,
//! and single-thread vs lock-free parallel theorem checking.

use std::time::Instant;

use rigor_kernel::{Arena, BinderInfo, Declaration, Environment, ReducibilityHint};

fn main() {
    println!("Rigor Phase 1 Micro-Benchmarks");
    println!("==============================");

    bench_arena_hash_consing();
    bench_church_reduction();
    bench_parallel_theorems();
}

fn bench_arena_hash_consing() {
    let mut arena = Arena::new();
    let n = 100_000u32;
    let l1 = arena.lvl_nat(1);
    let type0 = arena.sort(l1);
    let t0 = Instant::now();
    let mut cur = type0;
    for i in 0..n {
        let nm = arena.name_num(Arena::ANONYMOUS, i as u64);
        cur = arena.pi(nm, BinderInfo::Default, type0, cur);
    }
    // Re-intern a shared DAG of 100k hits to measure cache hit rate
    let b0 = arena.bvar(0);
    let mut hits = 0u32;
    for _ in 0..n {
        let x = arena.app(b0, b0);
        if x.0 > 0 {
            hits += 1;
        }
    }
    let elapsed = t0.elapsed();
    let total_ops = (n as f64) * 2.0;
    println!(
        "[1] Arena interning ({} unique + {} hits): {:.2} ms ({:.0} ops/sec)",
        n,
        hits,
        elapsed.as_secs_f64() * 1000.0,
        total_ops / elapsed.as_secs_f64()
    );
}

fn bench_church_reduction() {
    let mut env = Environment::new();
    let prop = env.arena.prop();
    let l1 = env.arena.lvl_nat(1);
    let l2 = env.arena.lvl_nat(2);
    let type0 = env.arena.sort(l1);
    let type1 = env.arena.sort(l2);
    let u = env.arena.name_from_path("u");
    let lu = env.arena.lvl_param(u);
    let su = env.arena.sort(lu);

    let b0 = env.arena.bvar(0);
    let b1 = env.arena.bvar(1);
    let b2 = env.arena.bvar(2);
    let b3 = env.arena.bvar(3);
    let b4 = env.arena.bvar(4);

    // Eq & Eq.refl
    let eq_name = env.arena.name_from_path("Eq");
    let eq_ty = {
        let y = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, b1, prop);
        let x = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, b0, y);
        env.arena.pi(Arena::ANONYMOUS, BinderInfo::Implicit, su, x)
    };
    let eq_val = {
        let p_ty = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, b2, prop);
        let px = env.arena.app(b0, b2);
        let py = env.arena.app(b1, b2);
        let body = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, px, py);
        let body = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, p_ty, body);
        let ly = env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, b1, body);
        let lx = env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, b0, ly);
        env.arena.lam(Arena::ANONYMOUS, BinderInfo::Implicit, su, lx)
    };
    env.add_decl(Declaration::Definition {
        name: eq_name,
        level_params: Box::new([u]),
        ty: eq_ty,
        val: eq_val,
        hint: ReducibilityHint::Regular(0),
    })
    .unwrap();

    let refl_name = env.arena.name_from_path("Eq.refl");
    let eq_u = env.arena.const_(eq_name, [lu]);
    let eq_axx = env.arena.app_n(eq_u, &[b1, b0, b0]);
    let refl_ty = {
        let x = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, b0, eq_axx);
        env.arena.pi(Arena::ANONYMOUS, BinderInfo::Implicit, su, x)
    };
    let refl_val = {
        let p_ty = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, b1, prop);
        let px = env.arena.app(b0, b1);
        let lh = env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, px, b0);
        let lp = env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, p_ty, lh);
        let lx = env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, b0, lp);
        env.arena.lam(Arena::ANONYMOUS, BinderInfo::Implicit, su, lx)
    };
    env.add_decl(Declaration::Theorem {
        name: refl_name,
        level_params: Box::new([u]),
        ty: refl_ty,
        val: refl_val,
    })
    .unwrap();

    let cnat_name = env.arena.name_from_path("CNat");
    let a_to_a = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, b0, b1);
    let a_to_a_s = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, b1, b2);
    let f_to = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, a_to_a, a_to_a_s);
    let cnat_val = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, type0, f_to);
    env.add_decl(Declaration::Definition {
        name: cnat_name,
        level_params: Box::new([]),
        ty: type1,
        val: cnat_val,
        hint: ReducibilityHint::Regular(0),
    })
    .unwrap();
    let cnat = env.arena.const_(cnat_name, []);
    let bin_ty = {
        let m = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, cnat, cnat);
        env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, cnat, m)
    };

    let add_name = env.arena.name_from_path("add");
    let add_val = {
        let mafx = env.arena.app_n(b3, &[b2, b1, b0]);
        let body = env.arena.app_n(b4, &[b2, b1, mafx]);
        let l = env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, b1, body);
        let l = env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, a_to_a, l);
        let l = env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, type0, l);
        let l = env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, cnat, l);
        env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, cnat, l)
    };
    env.add_decl(Declaration::Definition {
        name: add_name,
        level_params: Box::new([]),
        ty: bin_ty,
        val: add_val,
        hint: ReducibilityHint::Regular(0),
    })
    .unwrap();

    let mul_name = env.arena.name_from_path("mul");
    let mul_val = {
        let maf = env.arena.app_n(b2, &[b1, b0]);
        let body = env.arena.app_n(b3, &[b1, maf]);
        let l = env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, a_to_a, body);
        let l = env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, type0, l);
        let l = env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, cnat, l);
        env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, cnat, l)
    };
    env.add_decl(Declaration::Definition {
        name: mul_name,
        level_params: Box::new([]),
        ty: bin_ty,
        val: mul_val,
        hint: ReducibilityHint::Regular(0),
    })
    .unwrap();

    let church = |arena: &mut Arena, k: u32| {
        let mut body = b0;
        for _ in 0..k {
            body = arena.app(b1, body);
        }
        let lx = arena.lam(Arena::ANONYMOUS, BinderInfo::Default, b1, body);
        let lf = arena.lam(Arena::ANONYMOUS, BinderInfo::Default, a_to_a, lx);
        arena.lam(Arena::ANONYMOUS, BinderInfo::Default, type0, lf)
    };

    let c20 = church(&mut env.arena, 20);
    let c25 = church(&mut env.arena, 25);
    let c500 = church(&mut env.arena, 500);
    let mul_c = env.arena.const_(mul_name, []);
    let lhs = env.arena.app_n(mul_c, &[c20, c25]);
    let eq_2 = env.arena.const_(eq_name, [l2]);
    let refl_2 = env.arena.const_(refl_name, [l2]);
    let thm_ty = env.arena.app_n(eq_2, &[cnat, lhs, c500]);
    let thm_val = env.arena.app_n(refl_2, &[cnat, c500]);
    let thm_name = env.arena.name_from_path("church_20x25");

    let t0 = Instant::now();
    env.add_decl(Declaration::Theorem {
        name: thm_name,
        level_params: Box::new([]),
        ty: thm_ty,
        val: thm_val,
    })
    .expect("20 * 25 = 500 must verify");
    let elapsed = t0.elapsed();
    println!(
        "[2] Church numeral reduction (mul 20 25 == 500 by refl): {:.3} ms (arena nodes: {})",
        elapsed.as_secs_f64() * 1000.0,
        env.arena.expr_len()
    );
}

fn bench_parallel_theorems() {
    let mut env = Environment::new();
    let prop = env.arena.prop();
    let b0 = env.arena.bvar(0);
    let b1 = env.arena.bvar(1);
    let n_p = env.arena.name_from_path("P");
    let p_to_p = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, b0, b1);
    let base_ty = env.arena.pi(n_p, BinderInfo::Default, prop, p_to_p);
    let lh = env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, b0, b0);
    let base_val = env.arena.lam(n_p, BinderInfo::Default, prop, lh);

    // Build 2,000 independent non-trivial let-nested theorems
    let count = 2_000usize;
    let mut decls = Vec::with_capacity(count);
    for i in 0..count {
        let mut body = base_val;
        for _ in 0..8 {
            body = env.arena.let_(Arena::ANONYMOUS, base_ty, body, b0);
        }
        let name = env.arena.name_num(Arena::ANONYMOUS, i as u64 + 1);
        decls.push(Declaration::Theorem {
            name,
            level_params: Box::new([]),
            ty: base_ty,
            val: body,
        });
    }

    let frozen = env.freeze();
    let t1 = Instant::now();
    let r1 = frozen.check_batch_parallel(&decls, 1);
    let d1 = t1.elapsed();
    assert!(r1.iter().all(|r| r.is_ok()));

    let threads = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(4);
    let tp = Instant::now();
    let rp = frozen.check_batch_parallel(&decls, threads);
    let dp = tp.elapsed();
    assert!(rp.iter().all(|r| r.is_ok()));

    println!(
        "[3] Theorem batch ({} decls): 1 thread = {:.2} ms ({:.0} decls/s) | {} threads = {:.2} ms ({:.0} decls/s, {:.2}x)",
        count,
        d1.as_secs_f64() * 1000.0,
        count as f64 / d1.as_secs_f64(),
        threads,
        dp.as_secs_f64() * 1000.0,
        count as f64 / dp.as_secs_f64(),
        d1.as_secs_f64() / dp.as_secs_f64()
    );
}

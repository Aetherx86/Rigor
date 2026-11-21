//! Phase 1 micro-benchmarks: hash-consing throughput, heavy Church numeral reduction,
//! and single-thread vs lock-free parallel theorem checking.

use std::time::Instant;

use rigor_kernel::{
    Arena, BinderInfo, Declaration, Environment, InductiveSpec, InductiveTypeSpec, ReducibilityHint,
};

fn main() {
    println!("Rigor Phase 1-3 Micro-Benchmarks");
    println!("================================");

    bench_arena_hash_consing();
    bench_church_reduction();
    bench_nat_iota_reduction();
    bench_parallel_theorems();
    bench_lean4export_stream();
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

fn bench_nat_iota_reduction() {
    let mut env = Environment::new();
    let l1 = env.arena.lvl_nat(1);
    let type0 = env.arena.sort(l1);
    let prop = env.arena.prop();
    let nat_n = env.arena.name_from_path("Nat");
    let z_n = env.arena.name_from_path("Nat.zero");
    let s_n = env.arena.name_from_path("Nat.succ");
    let nat = env.arena.const_(nat_n, []);
    let s_ty = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, nat, nat);
    env.add_inductive(InductiveSpec {
        level_params: Box::new([]),
        num_params: 0,
        types: vec![InductiveTypeSpec { name: nat_n, ty: type0, ctors: vec![(z_n, nat), (s_n, s_ty)] }],
    })
    .unwrap();

    let u = env.arena.name_from_path("u");
    let lu = env.arena.lvl_param(u);
    let su = env.arena.sort(lu);
    let eq_n = env.arena.name_from_path("Eq");
    let refl_n = env.arena.name_from_path("Eq.refl");
    let b0 = env.arena.bvar(0);
    let b1 = env.arena.bvar(1);
    let b3 = env.arena.bvar(3);
    let eq_ty = {
        let tb = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, b1, prop);
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
        types: vec![InductiveTypeSpec { name: eq_n, ty: eq_ty, ctors: vec![(refl_n, refl_ty)] }],
    })
    .unwrap();

    let zero = env.arena.const_(z_n, []);
    let succ = env.arena.const_(s_n, []);
    let rec1 = env.arena.const_path("Nat.rec", [l1]);
    let bin_ty = {
        let i = env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, nat, nat);
        env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, nat, i)
    };
    let motive = env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, nat, nat);

    let add_n = env.arena.name_from_path("Nat.add");
    let add_val = {
        let sb0 = env.arena.app(succ, b0);
        let st = env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, nat, sb0);
        let st = env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, nat, st);
        let rc = env.arena.app_n(rec1, &[motive, b1, st, b0]);
        let lb = env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, nat, rc);
        env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, nat, lb)
    };
    env.add_decl(Declaration::Definition {
        name: add_n,
        level_params: Box::new([]),
        ty: bin_ty,
        val: add_val,
        hint: ReducibilityHint::Regular(0),
    })
    .unwrap();
    let add_c = env.arena.const_(add_n, []);

    let mul_n = env.arena.name_from_path("Nat.mul");
    let mul_val = {
        let a_ih = env.arena.app_n(add_c, &[b0, b3]);
        let st = env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, nat, a_ih);
        let st = env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, nat, st);
        let rc = env.arena.app_n(rec1, &[motive, zero, st, b0]);
        let lb = env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, nat, rc);
        env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, nat, lb)
    };
    env.add_decl(Declaration::Definition {
        name: mul_n,
        level_params: Box::new([]),
        ty: bin_ty,
        val: mul_val,
        hint: ReducibilityHint::Regular(0),
    })
    .unwrap();
    let mul_c = env.arena.const_(mul_n, []);

    let mk_nat = |arena: &mut Arena, k: u32| {
        let mut x = zero;
        for _ in 0..k {
            x = arena.app(succ, x);
        }
        x
    };
    let n20 = mk_nat(&mut env.arena, 20);
    let n25 = mk_nat(&mut env.arena, 25);
    let n500 = mk_nat(&mut env.arena, 500);
    let lhs = env.arena.app_n(mul_c, &[n20, n25]);
    let eq1 = env.arena.const_(eq_n, [l1]);
    let refl1 = env.arena.const_(refl_n, [l1]);
    let thm_ty = env.arena.app_n(eq1, &[nat, lhs, n500]);
    let thm_val = env.arena.app_n(refl1, &[nat, n500]);
    let thm_n = env.arena.name_from_path("nat_rec_20x25");

    let t0 = Instant::now();
    env.add_decl(Declaration::Theorem {
        name: thm_n,
        level_params: Box::new([]),
        ty: thm_ty,
        val: thm_val,
    })
    .expect("Nat.mul 20 25 == 500 via Nat.rec must verify");
    let elapsed = t0.elapsed();
    println!(
        "[2b] Inductive Nat.rec iota reduction (mul 20 25 == 500 by refl): {:.3} ms (arena nodes: {})",
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

fn bench_lean4export_stream() {
    use std::fmt::Write as _;

    // Generate a 5,000-declaration lean4export stream exercising #NS, #NI, #US, #ES, #EV,
    // #EC, #EA, #EL, #EP, #EZ, #ELN, #IND, #DEF, #THM.
    let n_decls = 5_000usize;
    let mut stream = String::with_capacity(n_decls * 96);
    stream.push_str(
        "0.1.4\n\
         1 #NS 0 Nat\n\
         2 #NS 1 zero\n\
         3 #NS 1 succ\n\
         4 #NS 0 Eq\n\
         5 #NS 4 refl\n\
         6 #NS 0 u\n\
         7 #NS 0 Bench\n\
         1 #US 0\n\
         2 #UP 6\n\
         0 #ES 0\n\
         1 #ES 1\n\
         2 #ES 2\n\
         3 #EV 0\n\
         4 #EV 1\n\
         5 #EC 1\n\
         6 #EP #BD 0 5 5\n\
         #IND 0 1 1 2 2 5 3 6\n\
         7 #EP #BD 0 4 0\n\
         8 #EP #BD 0 3 7\n\
         9 #EP #BI 0 2 8\n\
         10 #EC 4 2\n\
         11 #EA 10 4\n\
         12 #EA 11 3\n\
         13 #EA 12 3\n\
         14 #EP #BD 0 3 13\n\
         15 #EP #BI 0 2 14\n\
         #IND 2 4 9 1 5 15 6\n\
         16 #EC 4 1\n\
         17 #EC 5 1\n\
         18 #EA 16 5\n\
         19 #EA 17 5\n",
    );

    let mut next_name = 8usize;
    let mut next_expr = 20usize;
    for i in 0..n_decls {
        let nm_def = next_name;
        let nm_thm = next_name + 1;
        next_name += 2;
        let lit = next_expr;
        let let_e = next_expr + 1;
        let def_c = next_expr + 2;
        let eq1 = next_expr + 3;
        let eq2 = next_expr + 4;
        let rf = next_expr + 5;
        next_expr += 6;
        let _ = writeln!(stream, "{nm_def} #NI 7 {}", i * 2);
        let _ = writeln!(stream, "{nm_thm} #NI 7 {}", i * 2 + 1);
        let _ = writeln!(stream, "{lit} #ELN {}", i % 32);
        let _ = writeln!(stream, "{let_e} #EZ 0 5 {lit} 3");
        let _ = writeln!(stream, "#DEF {nm_def} 5 {let_e} R 1");
        let _ = writeln!(stream, "{def_c} #EC {nm_def}");
        let _ = writeln!(stream, "{eq1} #EA 18 {def_c}");
        let _ = writeln!(stream, "{eq2} #EA {eq1} {lit}");
        let _ = writeln!(stream, "{rf} #EA 19 {lit}");
        let _ = writeln!(stream, "#THM {nm_thm} {eq2} {rf}");
    }

    let bytes = stream.len();
    let t0 = Instant::now();
    let (env, stats) = rigor_parser::parse_str(&stream).expect("lean4export bench stream must verify");
    let elapsed = t0.elapsed();
    let mb = bytes as f64 / (1024.0 * 1024.0);
    println!(
        "[4] Streaming lean4export parse+check ({} decls, {} lines, {:.2} MiB): {:.2} ms ({:.0} decls/s, {:.1} MiB/s, env={} decls)",
        stats.total_decls(),
        stats.lines,
        mb,
        elapsed.as_secs_f64() * 1000.0,
        stats.total_decls() as f64 / elapsed.as_secs_f64(),
        mb / elapsed.as_secs_f64(),
        env.len()
    );
}

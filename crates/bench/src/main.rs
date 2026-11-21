//! Rigor Phase 4 Benchmark Harness & Computational Stress Suite.
//!
//! Modes:
//!   rigor-bench                                      Run full benchmark & stress suite
//!   rigor-bench --check <file.export>                Stream-parse and verify a lean4export file
//!   rigor-bench --generate-export <path> <n_decls>   Emit a valid lean4export benchmark artifact
//!   rigor-bench --stress-only [iters]                Loop heavy kernel reduction for CPU profiling

use std::env;
use std::fs::File;
use std::io::{BufWriter, Write};
use std::time::Instant;

use rigor_kernel::{
    Arena, BinderInfo, Declaration, Environment, ExprId, InductiveSpec, InductiveTypeSpec,
    ReducibilityHint,
};

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() >= 2 {
        match args[1].as_str() {
            "--check" => {
                let path = args.get(2).expect("usage: rigor-bench --check <file.export>");
                run_check_file(path);
                return;
            }
            "--generate-export" => {
                let path = args.get(2).expect("usage: rigor-bench --generate-export <path> <n_decls>");
                let n: usize = args
                    .get(3)
                    .and_then(|s| s.parse().ok())
                    .expect("expected integer <n_decls>");
                generate_export_file(path, n);
                return;
            }
            "--stress-only" => {
                let iters: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(20);
                for _ in 0..iters {
                    let _ = bench_ackermann(false);
                    let _ = bench_primality_reflection(false);
                }
                return;
            }
            _ => {}
        }
    }

    println!("Rigor Phase 4 Benchmark & Stress Suite");
    println!("======================================");
    bench_arena_hash_consing();
    bench_church_reduction();
    bench_nat_iota_reduction();
    bench_ackermann(true);
    bench_primality_reflection(true);
    bench_parallel_theorems();
    bench_lean4export_tier("Init-scale", 5_000);
    bench_lean4export_tier("Std-scale", 25_000);
    bench_lean4export_tier("Mathlib-subset-scale", 100_000);
}

fn run_check_file(path: &str) {
    let meta = std::fs::metadata(path).expect("failed to stat export file");
    let bytes = meta.len() as f64;
    let t0 = Instant::now();
    let mut env = Environment::new();
    let stats = rigor_parser::parse_file(path, &mut env).expect("kernel rejected export file");
    let elapsed = t0.elapsed();
    let secs = elapsed.as_secs_f64();
    let mib = bytes / (1024.0 * 1024.0);
    println!(
        "CHECK_OK file={} decls={} env_decls={} lines={} mib={:.2} time_ms={:.2} decls_per_sec={:.0} mib_per_sec={:.1} arena_exprs={}",
        path,
        stats.total_decls(),
        env.len(),
        stats.lines,
        mib,
        secs * 1000.0,
        stats.total_decls() as f64 / secs,
        mib / secs,
        env.arena.expr_len()
    );
}

fn generate_export_file(path: &str, n_decls: usize) {
    let file = File::create(path).expect("failed to create export file");
    let mut w = BufWriter::with_capacity(128 * 1024, file);
    write_export_stream(&mut w, n_decls).expect("failed writing export stream");
    w.flush().expect("failed flushing export file");
    let bytes = std::fs::metadata(path).map(|m| m.len()).unwrap_or(0);
    println!(
        "GENERATED file={} target_decls={} bytes={} ({:.2} MiB)",
        path,
        n_decls,
        bytes,
        bytes as f64 / (1024.0 * 1024.0)
    );
}

fn write_export_stream<W: Write>(w: &mut W, n_decls: usize) -> std::io::Result<()> {
    // Prelude: Nat, Bool, Eq, Prod, Quot, Nat.add
    w.write_all(
        b"0.1.4\n\
          1 #NS 0 Nat\n\
          2 #NS 1 zero\n\
          3 #NS 1 succ\n\
          4 #NS 1 rec\n\
          5 #NS 0 Eq\n\
          6 #NS 5 refl\n\
          7 #NS 0 u\n\
          8 #NS 0 Bool\n\
          9 #NS 8 false\n\
          10 #NS 8 true\n\
          11 #NS 0 Prod\n\
          12 #NS 11 mk\n\
          13 #NS 0 Bench\n\
          14 #NS 1 add\n\
          1 #US 0\n\
          2 #UP 7\n\
          0 #ES 0\n\
          1 #ES 1\n\
          2 #ES 2\n\
          3 #EV 0\n\
          4 #EV 1\n\
          5 #EV 2\n\
          6 #EV 3\n\
          7 #EC 1\n\
          8 #EP #BD 0 7 7\n\
          #IND 0 1 1 2 2 7 3 8\n\
          9 #EC 8\n\
          #IND 0 8 1 2 9 9 10 9\n\
          10 #EP #BD 0 4 0\n\
          11 #EP #BD 0 3 10\n\
          12 #EP #BI 0 2 11\n\
          13 #EC 5 2\n\
          14 #EA 13 4\n\
          15 #EA 14 3\n\
          16 #EA 15 3\n\
          17 #EP #BD 0 3 16\n\
          18 #EP #BI 0 2 17\n\
          #IND 2 5 12 1 6 18 7\n\
          #QUOT\n\
          19 #EP #BD 0 1 1\n\
          20 #EP #BD 0 1 19\n\
          21 #EC 11\n\
          22 #EA 21 6\n\
          23 #EA 22 5\n\
          24 #EP #BD 0 4 23\n\
          25 #EP #BD 0 4 24\n\
          26 #EP #BD 0 1 25\n\
          27 #EP #BD 0 1 26\n\
          #IND 2 11 20 1 12 27\n\
          28 #EC 4 1\n\
          29 #EC 3\n\
          30 #EL #BD 0 7 7\n\
          31 #EA 29 3\n\
          32 #EL #BD 0 7 31\n\
          33 #EL #BD 0 7 32\n\
          34 #EA 28 30\n\
          35 #EA 34 4\n\
          36 #EA 35 33\n\
          37 #EA 36 3\n\
          38 #EL #BD 0 7 37\n\
          39 #EL #BD 0 7 38\n\
          40 #EP #BD 0 7 8\n\
          #DEF 14 40 39 R 1\n\
          41 #EC 5 1\n\
          42 #EC 6 1\n\
          43 #EA 41 7\n\
          44 #EA 42 7\n\
          45 #EC 14\n\
          46 #EC 12\n\
          47 #EC 10\n",
    )?;

    // Each iteration emits 2 declarations (a #DEF and a #THM verifying it via delta/iota/proj/let).
    let pairs = n_decls.saturating_sub(6) / 2;
    let mut next_name = 15usize;
    let mut next_expr = 48usize;
    for i in 0..pairs {
        let nm_def = next_name;
        let nm_thm = next_name + 1;
        next_name += 2;
        if i % 4 == 0 {
            // Arithmetic computation theorem: Nat.add a b = (a+b) via Nat.rec + #ELN
            let a = (i % 7) as u64;
            let b = ((i / 7) % 5) as u64;
            let s = a + b;
            let ea = next_expr;
            let eb = next_expr + 1;
            let es = next_expr + 2;
            let add_a = next_expr + 3;
            let add_ab = next_expr + 4;
            let def_c = next_expr + 5;
            let eq1 = next_expr + 6;
            let eq2 = next_expr + 7;
            let rf = next_expr + 8;
            next_expr += 9;
            writeln!(w, "{nm_def} #NI 13 {}", i * 2)?;
            writeln!(w, "{nm_thm} #NI 13 {}", i * 2 + 1)?;
            writeln!(w, "{ea} #ELN {a}")?;
            writeln!(w, "{eb} #ELN {b}")?;
            writeln!(w, "{es} #ELN {s}")?;
            writeln!(w, "{add_a} #EA 45 {ea}")?;
            writeln!(w, "{add_ab} #EA {add_a} {eb}")?;
            writeln!(w, "#DEF {nm_def} 7 {add_ab} R 2")?;
            writeln!(w, "{def_c} #EC {nm_def}")?;
            writeln!(w, "{eq1} #EA 43 {def_c}")?;
            writeln!(w, "{eq2} #EA {eq1} {es}")?;
            writeln!(w, "{rf} #EA 44 {es}")?;
            writeln!(w, "#THM {nm_thm} {eq2} {rf}")?;
        } else if i % 4 == 1 {
            // Structure projection (#EJ) theorem: (Prod.mk Nat Bool k true).0 = k
            let k = (i % 64) as u64;
            let ek = next_expr;
            let p1 = next_expr + 1;
            let p2 = next_expr + 2;
            let p3 = next_expr + 3;
            let p4 = next_expr + 4;
            let prj = next_expr + 5;
            let def_c = next_expr + 6;
            let eq1 = next_expr + 7;
            let eq2 = next_expr + 8;
            let rf = next_expr + 9;
            next_expr += 10;
            writeln!(w, "{nm_def} #NI 13 {}", i * 2)?;
            writeln!(w, "{nm_thm} #NI 13 {}", i * 2 + 1)?;
            writeln!(w, "{ek} #ELN {k}")?;
            writeln!(w, "{p1} #EA 46 7")?;
            writeln!(w, "{p2} #EA {p1} 9")?;
            writeln!(w, "{p3} #EA {p2} {ek}")?;
            writeln!(w, "{p4} #EA {p3} 47")?;
            writeln!(w, "{prj} #EJ 11 0 {p4}")?;
            writeln!(w, "#DEF {nm_def} 7 {prj} R 1")?;
            writeln!(w, "{def_c} #EC {nm_def}")?;
            writeln!(w, "{eq1} #EA 43 {def_c}")?;
            writeln!(w, "{eq2} #EA {eq1} {ek}")?;
            writeln!(w, "{rf} #EA 44 {ek}")?;
            writeln!(w, "#THM {nm_thm} {eq2} {rf}")?;
        } else {
            // Let-binding (#EZ) + delta theorem
            let k = (i % 64) as u64;
            let lit = next_expr;
            let let_e = next_expr + 1;
            let def_c = next_expr + 2;
            let eq1 = next_expr + 3;
            let eq2 = next_expr + 4;
            let rf = next_expr + 5;
            next_expr += 6;
            writeln!(w, "{nm_def} #NI 13 {}", i * 2)?;
            writeln!(w, "{nm_thm} #NI 13 {}", i * 2 + 1)?;
            writeln!(w, "{lit} #ELN {k}")?;
            writeln!(w, "{let_e} #EZ 0 7 {lit} 3")?;
            writeln!(w, "#DEF {nm_def} 7 {let_e} R 1")?;
            writeln!(w, "{def_c} #EC {nm_def}")?;
            writeln!(w, "{eq1} #EA 43 {def_c}")?;
            writeln!(w, "{eq2} #EA {eq1} {lit}")?;
            writeln!(w, "{rf} #EA 44 {lit}")?;
            writeln!(w, "#THM {nm_thm} {eq2} {rf}")?;
        }
    }
    Ok(())
}

fn bench_lean4export_tier(label: &str, n_decls: usize) {
    let mut buf = Vec::with_capacity(n_decls * 128);
    write_export_stream(&mut buf, n_decls).unwrap();
    let bytes = buf.len() as f64;
    let t0 = Instant::now();
    let mut env = Environment::new();
    let stats = rigor_parser::parse_and_check(buf.as_slice(), &mut env)
        .expect("lean4export benchmark stream must verify");
    let elapsed = t0.elapsed();
    let secs = elapsed.as_secs_f64();
    let mib = bytes / (1024.0 * 1024.0);
    println!(
        "[export] {:<20} ({:>6} decls, {:>6} lines, {:>5.2} MiB): {:>7.2} ms ({:>7.0} decls/s, {:>5.1} MiB/s)",
        label,
        stats.total_decls(),
        stats.lines,
        mib,
        secs * 1000.0,
        stats.total_decls() as f64 / secs,
        mib / secs
    );
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

/// Shared prelude with `Nat`, `Bool`, `Eq` for computational stress tests.
struct NatBoolEq {
    env: Environment,
    nat: ExprId,
    zero: ExprId,
    succ: ExprId,
    nat_rec1: ExprId,
    bool_ty: ExprId,
    b_false: ExprId,
    b_true: ExprId,
    bool_rec1: ExprId,
    eq1: ExprId,
    refl1: ExprId,
}

fn setup_nat_bool_eq() -> NatBoolEq {
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
        types: vec![InductiveTypeSpec {
            name: nat_n,
            ty: type0,
            ctors: vec![(z_n, nat), (s_n, s_ty)],
        }],
    })
    .unwrap();

    let bool_n = env.arena.name_from_path("Bool");
    let bf_n = env.arena.name_from_path("Bool.false");
    let bt_n = env.arena.name_from_path("Bool.true");
    let bool_ty = env.arena.const_(bool_n, []);
    env.add_inductive(InductiveSpec {
        level_params: Box::new([]),
        num_params: 0,
        types: vec![InductiveTypeSpec {
            name: bool_n,
            ty: type0,
            ctors: vec![(bf_n, bool_ty), (bt_n, bool_ty)],
        }],
    })
    .unwrap();

    let u = env.arena.name_from_path("u");
    let lu = env.arena.lvl_param(u);
    let su = env.arena.sort(lu);
    let eq_n = env.arena.name_from_path("Eq");
    let refl_n = env.arena.name_from_path("Eq.refl");
    let b0 = env.arena.bvar(0);
    let b1 = env.arena.bvar(1);
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
        types: vec![InductiveTypeSpec {
            name: eq_n,
            ty: eq_ty,
            ctors: vec![(refl_n, refl_ty)],
        }],
    })
    .unwrap();

    let zero = env.arena.const_(z_n, []);
    let succ = env.arena.const_(s_n, []);
    let nat_rec1 = env.arena.const_path("Nat.rec", [l1]);
    let b_false = env.arena.const_(bf_n, []);
    let b_true = env.arena.const_(bt_n, []);
    let bool_rec1 = env.arena.const_path("Bool.rec", [l1]);
    let eq1 = env.arena.const_(eq_n, [l1]);
    let refl1 = env.arena.const_(refl_n, [l1]);

    NatBoolEq {
        env,
        nat,
        zero,
        succ,
        nat_rec1,
        bool_ty,
        b_false,
        b_true,
        bool_rec1,
        eq1,
        refl1,
    }
}

fn mk_peano(arena: &mut Arena, zero: ExprId, succ: ExprId, k: u32) -> ExprId {
    let mut x = zero;
    for _ in 0..k {
        x = arena.app(succ, x);
    }
    x
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
    let (b0, b1, b2, b3) = (
        env.arena.bvar(0),
        env.arena.bvar(1),
        env.arena.bvar(2),
        env.arena.bvar(3),
    );

    let eq_n = env.arena.name_from_path("Eq");
    let refl_n = env.arena.name_from_path("Eq.refl");
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
        types: vec![InductiveTypeSpec {
            name: eq_n,
            ty: eq_ty,
            ctors: vec![(refl_n, refl_ty)],
        }],
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

    let c25 = church(&mut env.arena, 25);
    let c40 = church(&mut env.arena, 40);
    let c1000 = church(&mut env.arena, 1000);
    let mul_c = env.arena.const_(mul_name, []);
    let lhs = env.arena.app_n(mul_c, &[c25, c40]);
    let eq_2 = env.arena.const_(eq_n, [l2]);
    let refl_2 = env.arena.const_(refl_n, [l2]);
    let thm_ty = env.arena.app_n(eq_2, &[cnat, lhs, c1000]);
    let thm_val = env.arena.app_n(refl_2, &[cnat, c1000]);
    let thm_name = env.arena.name_from_path("church_25x40");

    let t0 = Instant::now();
    env.add_decl(Declaration::Theorem {
        name: thm_name,
        level_params: Box::new([]),
        ty: thm_ty,
        val: thm_val,
    })
    .expect("Church 25 * 40 = 1000 must verify");
    let elapsed = t0.elapsed();
    println!(
        "[2] Stress A — Church mul 25*40 == 1000 by refl: {:.3} ms (arena nodes: {})",
        elapsed.as_secs_f64() * 1000.0,
        env.arena.expr_len()
    );
}

fn bench_nat_iota_reduction() {
    let mut s = setup_nat_bool_eq();
    let (b0, b1, b3) = (s.env.arena.bvar(0), s.env.arena.bvar(1), s.env.arena.bvar(3));
    let bin_ty = {
        let i = s.env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, s.nat, s.nat);
        s.env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, s.nat, i)
    };
    let motive = s.env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, s.nat, s.nat);

    let add_n = s.env.arena.name_from_path("Nat.add");
    let add_val = {
        let sb0 = s.env.arena.app(s.succ, b0);
        let st = s.env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, s.nat, sb0);
        let st = s.env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, s.nat, st);
        let rc = s.env.arena.app_n(s.nat_rec1, &[motive, b1, st, b0]);
        let lb = s.env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, s.nat, rc);
        s.env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, s.nat, lb)
    };
    s.env
        .add_decl(Declaration::Definition {
            name: add_n,
            level_params: Box::new([]),
            ty: bin_ty,
            val: add_val,
            hint: ReducibilityHint::Regular(0),
        })
        .unwrap();
    let add_c = s.env.arena.const_(add_n, []);

    let mul_n = s.env.arena.name_from_path("Nat.mul");
    let mul_val = {
        let a_ih = s.env.arena.app_n(add_c, &[b0, b3]);
        let st = s.env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, s.nat, a_ih);
        let st = s.env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, s.nat, st);
        let rc = s.env.arena.app_n(s.nat_rec1, &[motive, s.zero, st, b0]);
        let lb = s.env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, s.nat, rc);
        s.env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, s.nat, lb)
    };
    s.env
        .add_decl(Declaration::Definition {
            name: mul_n,
            level_params: Box::new([]),
            ty: bin_ty,
            val: mul_val,
            hint: ReducibilityHint::Regular(0),
        })
        .unwrap();
    let mul_c = s.env.arena.const_(mul_n, []);

    let n30 = mk_peano(&mut s.env.arena, s.zero, s.succ, 30);
    let n40 = mk_peano(&mut s.env.arena, s.zero, s.succ, 40);
    let n1200 = mk_peano(&mut s.env.arena, s.zero, s.succ, 1200);
    let lhs = s.env.arena.app_n(mul_c, &[n30, n40]);
    let thm_ty = s.env.arena.app_n(s.eq1, &[s.nat, lhs, n1200]);
    let thm_val = s.env.arena.app_n(s.refl1, &[s.nat, n1200]);
    let thm_n = s.env.arena.name_from_path("nat_rec_30x40");

    let t0 = Instant::now();
    s.env
        .add_decl(Declaration::Theorem {
            name: thm_n,
            level_params: Box::new([]),
            ty: thm_ty,
            val: thm_val,
        })
        .expect("Nat.mul 30 40 == 1200 via Nat.rec must verify");
    let elapsed = t0.elapsed();
    println!(
        "[3] Stress B — Nat.rec iota mul 30*40 == 1200 by refl: {:.3} ms (arena nodes: {})",
        elapsed.as_secs_f64() * 1000.0,
        s.env.arena.expr_len()
    );
}

/// Higher-order structurally recursive Ackermann function via nested `Nat.rec`:
///   iter f 0 = f 1
///   iter f (n+1) = f (iter f n)
///   ack 0 = Nat.succ
///   ack (m+1) = iter (ack m)
/// Verifies `ack 3 5 == 253` by `Eq.refl`.
fn bench_ackermann(print: bool) -> f64 {
    let mut s = setup_nat_bool_eq();
    let (b0, b1, b3) = (s.env.arena.bvar(0), s.env.arena.bvar(1), s.env.arena.bvar(3));
    let nat_to_nat = s.env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, s.nat, s.nat);
    let motive_nat = s.env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, s.nat, s.nat);
    let one = s.env.arena.app(s.succ, s.zero);

    // iter : (Nat -> Nat) -> Nat -> Nat
    let iter_n = s.env.arena.name_from_path("iter");
    let iter_ty = s.env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, nat_to_nat, nat_to_nat);
    let iter_val = {
        // Under (f:#1) (n:#0): Nat.rec (λ _, Nat) (f 1) (λ _ ih, f ih) n
        let f1 = s.env.arena.app(b1, one);
        let f_ih = s.env.arena.app(b3, b0);
        let step = s.env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, s.nat, f_ih);
        let step = s.env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, s.nat, step);
        let rc = s.env.arena.app_n(s.nat_rec1, &[motive_nat, f1, step, b0]);
        let ln = s.env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, s.nat, rc);
        s.env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, nat_to_nat, ln)
    };
    s.env
        .add_decl(Declaration::Definition {
            name: iter_n,
            level_params: Box::new([]),
            ty: iter_ty,
            val: iter_val,
            hint: ReducibilityHint::Regular(0),
        })
        .unwrap();
    let iter_c = s.env.arena.const_(iter_n, []);

    // ack : Nat -> Nat -> Nat
    let ack_n = s.env.arena.name_from_path("ack");
    let ack_ty = s.env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, s.nat, nat_to_nat);
    let motive_fn = s.env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, s.nat, nat_to_nat);
    let ack_val = {
        let iter_ih = s.env.arena.app(iter_c, b0);
        let step = s.env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, nat_to_nat, iter_ih);
        let step = s.env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, s.nat, step);
        let rc = s.env.arena.app_n(s.nat_rec1, &[motive_fn, s.succ, step, b0]);
        s.env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, s.nat, rc)
    };
    s.env
        .add_decl(Declaration::Definition {
            name: ack_n,
            level_params: Box::new([]),
            ty: ack_ty,
            val: ack_val,
            hint: ReducibilityHint::Regular(0),
        })
        .unwrap();
    let ack_c = s.env.arena.const_(ack_n, []);

    let n3 = s.env.arena.lit_nat(3);
    let n5 = s.env.arena.lit_nat(5);
    let n253 = s.env.arena.lit_nat(253);
    let lhs = s.env.arena.app_n(ack_c, &[n3, n5]);
    let thm_ty = s.env.arena.app_n(s.eq1, &[s.nat, lhs, n253]);
    let thm_val = s.env.arena.app_n(s.refl1, &[s.nat, n253]);
    let thm_n = s.env.arena.name_from_path("ack_3_5_eq_253");

    let t0 = Instant::now();
    s.env
        .add_decl(Declaration::Theorem {
            name: thm_n,
            level_params: Box::new([]),
            ty: thm_ty,
            val: thm_val,
        })
        .expect("ack 3 5 == 253 must verify");
    let ms = t0.elapsed().as_secs_f64() * 1000.0;
    if print {
        println!(
            "[4] Stress C — Ackermann ack(3, 5) == 253 by refl: {:.3} ms (arena nodes: {})",
            ms,
            s.env.arena.expr_len()
        );
    }
    ms
}

/// Pure-CIC kernel primality reflection: defines `pred`, `sub`, `isZero`, `not`, `and`,
/// `ble`, `lt`, `remStep`, `divides`, `noDivBelow`, `isPrime` via `Nat.rec`/`Bool.rec`,
/// and verifies `isPrime 53 = true`, `isPrime 51 = false`, and `isPrime 97 = true` by `Eq.refl`.
fn bench_primality_reflection(print: bool) -> f64 {
    let mut s = setup_nat_bool_eq();
    let (b0, b1, _b2, b3, b4) = (
        s.env.arena.bvar(0),
        s.env.arena.bvar(1),
        s.env.arena.bvar(2),
        s.env.arena.bvar(3),
        s.env.arena.bvar(4),
    );
    let n2n = s.env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, s.nat, s.nat);
    let nn2n = s.env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, s.nat, n2n);
    let n2b = s.env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, s.nat, s.bool_ty);
    let nn2b = s.env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, s.nat, n2b);
    let b2b = s.env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, s.bool_ty, s.bool_ty);
    let bb2b = s.env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, s.bool_ty, b2b);
    let mot_nat = s.env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, s.nat, s.nat);
    let mot_bool = s.env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, s.nat, s.bool_ty);
    let mot_b_nat = s.env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, s.bool_ty, s.nat);
    let mot_b_bool = s.env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, s.bool_ty, s.bool_ty);

    let add_def = |env: &mut Environment, name: &str, ty: ExprId, val: ExprId| -> ExprId {
        let nm = env.arena.name_from_path(name);
        env.add_decl(Declaration::Definition {
            name: nm,
            level_params: Box::new([]),
            ty,
            val,
            hint: ReducibilityHint::Regular(0),
        })
        .unwrap_or_else(|e| panic!("def {name} failed: {e}"));
        env.arena.const_(nm, [])
    };

    // pred n = Nat.rec _ 0 (λ k _, k) n
    let pred_val = {
        let st = s.env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, s.nat, b1);
        let st = s.env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, s.nat, st);
        let rc = s.env.arena.app_n(s.nat_rec1, &[mot_nat, s.zero, st, b0]);
        s.env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, s.nat, rc)
    };
    let pred_c = add_def(&mut s.env, "Nat.pred", n2n, pred_val);

    // sub a b = Nat.rec _ a (λ _ ih, pred ih) b
    let sub_val = {
        let p_ih = s.env.arena.app(pred_c, b0);
        let st = s.env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, s.nat, p_ih);
        let st = s.env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, s.nat, st);
        let rc = s.env.arena.app_n(s.nat_rec1, &[mot_nat, b1, st, b0]);
        let lb = s.env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, s.nat, rc);
        s.env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, s.nat, lb)
    };
    let sub_c = add_def(&mut s.env, "Nat.sub", nn2n, sub_val);

    // isZero n = Nat.rec _ true (λ _ _, false) n
    let is_zero_val = {
        let st = s.env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, s.bool_ty, s.b_false);
        let st = s.env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, s.nat, st);
        let rc = s.env.arena.app_n(s.nat_rec1, &[mot_bool, s.b_true, st, b0]);
        s.env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, s.nat, rc)
    };
    let is_zero_c = add_def(&mut s.env, "Nat.isZero", n2b, is_zero_val);

    // bnot x = Bool.rec _ true false x
    let not_val = {
        let rc = s.env.arena.app_n(s.bool_rec1, &[mot_b_bool, s.b_true, s.b_false, b0]);
        s.env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, s.bool_ty, rc)
    };
    let not_c = add_def(&mut s.env, "Bool.not", b2b, not_val);

    // band x y = Bool.rec _ false y x
    let and_val = {
        let rc = s.env.arena.app_n(s.bool_rec1, &[mot_b_bool, s.b_false, b0, b1]);
        let ly = s.env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, s.bool_ty, rc);
        s.env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, s.bool_ty, ly)
    };
    let and_c = add_def(&mut s.env, "Bool.and", bb2b, and_val);

    // ble a b = isZero (sub a b)
    let ble_val = {
        let sub_ab = s.env.arena.app_n(sub_c, &[b1, b0]);
        let iz = s.env.arena.app(is_zero_c, sub_ab);
        let lb = s.env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, s.nat, iz);
        s.env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, s.nat, lb)
    };
    let ble_c = add_def(&mut s.env, "Nat.ble", nn2b, ble_val);

    // lt a b = ble (succ a) b
    let lt_val = {
        let sa = s.env.arena.app(s.succ, b1);
        let bl = s.env.arena.app_n(ble_c, &[sa, b0]);
        let lb = s.env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, s.nat, bl);
        s.env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, s.nat, lb)
    };
    let lt_c = add_def(&mut s.env, "Nat.lt", nn2b, lt_val);

    // remStep : Nat -> Nat -> Nat -> Nat  (d, fuel, r)
    // remStep d 0 = λ r, r
    // remStep d (succ _) = λ r, Bool.rec _ (ih (sub r d)) r (lt r d)
    // (Bool.rec order: false-branch first, true-branch second!)
    let nnn2n = s.env.arena.pi(Arena::ANONYMOUS, BinderInfo::Default, s.nat, nn2n);
    let mot_n2n = s.env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, s.nat, n2n);
    let rem_step_val = {
        let id_nat = s.env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, s.nat, b0);
        // Under (d:#4) (fuel:#3) (_:#2) (ih:#1) (r:#0):
        let r_lt_d = s.env.arena.app_n(lt_c, &[b0, b4]);
        let r_sub_d = s.env.arena.app_n(sub_c, &[b0, b4]);
        let ih_next = s.env.arena.app(b1, r_sub_d);
        let br = s.env.arena.app_n(s.bool_rec1, &[mot_b_nat, ih_next, b0, r_lt_d]);
        let lr = s.env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, s.nat, br);
        let lih = s.env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, n2n, lr);
        let lk = s.env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, s.nat, lih);
        let rc = s.env.arena.app_n(s.nat_rec1, &[mot_n2n, id_nat, lk, b0]);
        let lf = s.env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, s.nat, rc);
        s.env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, s.nat, lf)
    };
    let rem_step_c = add_def(&mut s.env, "Nat.remStep", nnn2n, rem_step_val);

    // divides d n = isZero (remStep d n n)
    let divides_val = {
        let r = s.env.arena.app_n(rem_step_c, &[b1, b0, b0]);
        let iz = s.env.arena.app(is_zero_c, r);
        let ln = s.env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, s.nat, iz);
        s.env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, s.nat, ln)
    };
    let divides_c = add_def(&mut s.env, "Nat.divides", nn2b, divides_val);

    // noDivBelow n limit:
    //   0 => true
    //   succ k => Bool.rec _ (and (not (divides (succ k) n)) ih) true (isZero k)
    let no_div_val = {
        // Under (n:#3) (limit:#2) (k:#1) (ih:#0):
        let iz_k = s.env.arena.app(is_zero_c, b1);
        let sk = s.env.arena.app(s.succ, b1);
        let div = s.env.arena.app_n(divides_c, &[sk, b3]);
        let ndiv = s.env.arena.app(not_c, div);
        let both = s.env.arena.app_n(and_c, &[ndiv, b0]);
        let br = s.env.arena.app_n(s.bool_rec1, &[mot_b_bool, both, s.b_true, iz_k]);
        let lih = s.env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, s.bool_ty, br);
        let lk = s.env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, s.nat, lih);
        let rc = s.env.arena.app_n(s.nat_rec1, &[mot_bool, s.b_true, lk, b0]);
        let ll = s.env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, s.nat, rc);
        s.env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, s.nat, ll)
    };
    let no_div_c = add_def(&mut s.env, "Nat.noDivBelow", nn2b, no_div_val);

    // isPrime n = and (ble 2 n) (noDivBelow n (pred n))
    let two = s.env.arena.lit_nat(2);
    let is_prime_val = {
        let ge2 = s.env.arena.app_n(ble_c, &[two, b0]);
        let pn = s.env.arena.app(pred_c, b0);
        let nd = s.env.arena.app_n(no_div_c, &[b0, pn]);
        let res = s.env.arena.app_n(and_c, &[ge2, nd]);
        s.env.arena.lam(Arena::ANONYMOUS, BinderInfo::Default, s.nat, res)
    };
    let is_prime_c = add_def(&mut s.env, "Nat.isPrime", n2b, is_prime_val);

    let t0 = Instant::now();
    for (num, expected_prime) in [(51u64, false), (53, true), (97, true)] {
        let lit = s.env.arena.lit_nat(num);
        let exp = if expected_prime { s.b_true } else { s.b_false };
        let lhs = s.env.arena.app(is_prime_c, lit);
        let ty = s.env.arena.app_n(s.eq1, &[s.bool_ty, lhs, exp]);
        let val = s.env.arena.app_n(s.refl1, &[s.bool_ty, exp]);
        let nm = s.env.arena.name_from_path(&format!("prime_check_{num}"));
        s.env
            .add_decl(Declaration::Theorem {
                name: nm,
                level_params: Box::new([]),
                ty,
                val,
            })
            .unwrap_or_else(|e| panic!("isPrime {num} = {expected_prime} failed: {e}"));
    }
    let ms = t0.elapsed().as_secs_f64() * 1000.0;
    if print {
        println!(
            "[5] Stress D — Primality reflection (51=F, 53=T, 97=T by refl): {:.3} ms (arena nodes: {})",
            ms,
            s.env.arena.expr_len()
        );
    }
    ms
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

    let count = 10_000usize;
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
        "[6] Parallel theorem batch ({} decls): 1T = {:.2} ms ({:.0} decls/s) | {}T = {:.2} ms ({:.0} decls/s, {:.2}x)",
        count,
        d1.as_secs_f64() * 1000.0,
        count as f64 / d1.as_secs_f64(),
        threads,
        dp.as_secs_f64() * 1000.0,
        count as f64 / dp.as_secs_f64(),
        d1.as_secs_f64() / dp.as_secs_f64()
    );
}

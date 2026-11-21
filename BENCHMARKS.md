# Rigor Benchmarks & Optimization Report

This document records reproducible performance, Peak RSS memory, and CPU profiling results for **Rigor** across Phases 1–4, including before/after optimization metrics and instructions for head-to-head comparison against Lean 4's `lean4checker`.

## Test Environment

- **Hardware:** Apple M4 (10 CPU cores, 16 GiB RAM, macOS)
- **Toolchain:** Rust `rustc` / `cargo` (`--release`), `/usr/bin/time -l` (OS-level maximum resident set size), `/usr/bin/sample` (CPU call-stack profiler)
- **Kernel TCB Footprint:** `crates/kernel/src/*.rs` = **2,484 SLOC** (`#![forbid(unsafe_code)]`, zero third-party crates)
- **Correctness Gate:** 19/19 unit, inductive, `lean4export`, regression, and soundness torture tests passing with 0 warnings.

---

## 1. Before / After Optimization Results

### 1.1 Computational Reduction Stress Suite (`cargo run --release -p rigor-bench`)

| Workload | Before (Baseline) | After (Optimized) | Speedup | Arena Nodes (Before -> After) |
|---|---:|---:|---:|---:|
| Arena interning (100k unique + 100k hits) | 16.99 ms (`11.77M ops/s`) | **5.33 ms** (`37.50M ops/s`) | **3.19x** | — |
| Stress A: Church `mul 25 * 40 == 1000` (`Eq.refl`) | 1.823 ms | **0.390 ms** | **4.67x** | 9,345 -> **6,329** (`-32.3%`) |
| Stress B: Inductive `Nat.rec` `mul 30 * 40 == 1200` (`Eq.refl`) | 3.764 ms | **0.427 ms** | **8.81x** | 6,992 -> **5,503** (`-21.3%`) |
| Stress C: Higher-order `Nat.rec` Ackermann `ack(3, 5) == 253` | 2.051 ms | **0.285 ms** | **7.20x** | 4,085 -> **2,766** (`-32.3%`) |
| Stress D: Pure-CIC Primality reflection (`51=F, 53=T, 97=T`) | 38.395 ms | **10.036 ms** | **3.83x** | 132,684 -> **85,676** (`-35.4%`) |
| Parallel theorem batch (10,000 decls, 10 threads vs 1 thread) | 3.46 ms (`2.89M decls/s`) | **3.35 ms** (`2.98M decls/s`, 3.20x over 1T) | **1.03x** | thread-local scratch arenas |

### 1.2 Streaming `lean4export` File Throughput & Peak RSS (`./crates/bench/run_head_to_head.sh`)

Measured end-to-end from disk (64 KiB `BufReader` + parser + full CIC kernel type-checking) using `/usr/bin/time -l`:

| Artifact | Scale | Before Wall (Decls/s) | After Wall (Decls/s) | Speedup | Before Peak RSS | After Peak RSS | RSS Delta |
|---|---|---:|---:|---:|---:|---:|---:|
| `init_scale_5k.export` | 5,000 decls / 29,412 lines / 0.49 MiB | 10.65 ms (`469k/s`) | **6.20 ms** (`806k/s`) | **1.72x** | 5.66 MB | **5.23 MB** | **-7.6%** |
| `std_scale_25k.export` | 25,000 decls / 146,912 lines / 2.62 MiB | 54.27 ms (`461k/s`) | **29.45 ms** (`849k/s`) | **1.84x** | 16.23 MB | **13.30 MB** | **-18.1%** |
| `mathlib_subset_100k.export` | 100,000 decls / 587,537 lines / 11.29 MiB | 222.98 ms (`448k/s`) | **113.26 ms** (`883k/s`) | **1.97x** | 61.02 MB | **46.56 MB** | **-23.7%** |

In-memory streaming (`BufRead` slice, zero disk latency) reached **918,795 decls/s** (**103.7 MiB/s**) on the 100k-declaration stream.

---

## 2. Profiling Analysis & Root-Cause Optimizations

### Baseline Profile (`/usr/bin/sample` on `--stress-only`)

The baseline call-stack profile identified four dominant bottlenecks accounting for >80% of CPU time:

1. **Polymorphic `ExprData` Hash-Consing & Cloning (~37% of samples):**
   `Arena::lookup_expr` (153 samples), `ExprData::clone` (120), `Arena::intern_expr` (89), `ExprData::eq` (62), `FxHasher::hash_one(ExprData)` (49). Every `App(f, a)` and `BVar(i)` was boxed into the polymorphic `expr_map: FxHashMap<ExprData, ExprId>`, hashing enum tags and cloning 40-byte entries on insert.
2. **Per-Call Substitution HashMap Churn (~30% of samples):**
   `HashMap<(ExprId, u32), ExprId>::insert` (133), `reserve_rehash` (94), `malloc`/`free` (288), `map_children<instantiate_rev>` (84). Every small `instantiate1` call allocated and freed a brand-new `FxHashMap`.
3. **Repeated Universe Instantiation & Metadata Clones (~11% of samples):**
   `map_children<instantiate_level_params>` (99), `RecursorInfo::clone` (13), `delta_info` (10), `lookup_name` / `name_from_path` (16). Every `Nat.rec.{1}` / `Bool.rec.{1}` iota step re-traversed `rule.rhs` to instantiate `u_1 -> 1`, cloned `RecursorInfo`, and re-hashed `"Nat.zero"` / `"Nat.succ"`.
4. **Spine Re-Interning Between WHNF Steps (revealed in Round 1 profile as 38% of remaining time):**
   `whnf_core` popped arguments from a spine, then rebuilt every `App` node via `arena.app(...)`, only for `reduce_iota_or_proj` and `unfold_head_delta` to tear down the exact same `App` spine on the next loop iteration.

### Optimizations Implemented

1. **Specialized `app_map` & `bvar_cache` in `Arena` (`crates/kernel/src/arena.rs`):**
   - Split `App(ExprId, ExprId)` into a dedicated 8-byte-key `app_map: FxHashMap<(ExprId, ExprId), ExprId>` (eliminating `ExprData` cloning and cutting `mathlib_subset_100k.export` Peak RSS from 61.02 MB to 46.56 MB).
   - Added an O(1) `[u32; 32]` direct lookup cache for `BVar(0..32)`, routing `intern_expr` through the same canonical paths to preserve global hash-consing uniqueness across parent/child arenas.
2. **Unified Spine Abstract Machine (`crates/kernel/src/reduce.rs`):**
   - Replaced the separate `whnf_core` + `reduce_iota_or_proj` + `unfold_head_delta` loop with a single `whnf_spine_with` machine that retains arguments on `spine` across beta, zeta, local `FVar`, `Proj`, `Quot.lift`, `Recursor` iota/K-like, and delta steps, rebuilding `App` nodes only once at WHNF termination.
   - Eliminated `RecursorInfo` / `InductiveInfo` / `ConstructorInfo` / `ExprData` clones by borrowing `&'a` references directly from `self.decls`.
   - Cached 1-level-param instantiations (`inst_lvl1_cache`) and `Nat.zero` / `Nat.succ` expressions on `TypeChecker`.
   - Deferred `is_proof` in `is_def_eq_core` until after fast structural and same-head constructor checks (while still firing before delta unfolding of theorem/proof terms).
3. **Zero-Clone Traversal & Lazy Memoization (`crates/kernel/src/expr.rs`):**
   - Extracted `Copy` fields directly instead of calling `ExprData::clone()`.
   - Delayed `FxHashMap` allocation in `map_children` until traversal exceeds `LAZY_CACHE_THRESHOLD = 12` nodes, giving zero-allocation substitution on small terms while keeping worst-case $O(|V|)$ DAG memoization on deep shared terms.

### Post-Optimization Profile (`/usr/bin/sample` on `--stress-only 250`)

After optimization, `ExprData::clone`, `RecursorInfo::clone`, `name_from_path`, and redundant `instantiate_level_params` vanished from the top hotspots. Remaining time is concentrated cleanly in core work: `map_children<instantiate_rev>` (339), `Arena::app` (313), and `whnf_spine_with` (250).

---

## 3. Running Head-to-Head Against Lean 4's `lean4checker`

`lean4checker` and `lean4export` were not installed on the test host during Phase 4. The automated harness in `crates/bench/run_head_to_head.sh` auto-detects `lean4checker` on `PATH` and benchmarks both checkers on identical `.export` artifacts with OS-level Peak RSS reporting.

### Reproduce Synthetic Scale Benchmarks + Peak RSS

```sh
cargo test --workspace
cargo run --release -p rigor-bench
./crates/bench/run_head_to_head.sh /tmp/rigor_bench
```

### Run Head-to-Head on Real Lean 4 `Init`, `Std`, and `Mathlib` Exports

Once `elan`, `lean4export`, and `lean4checker` are installed:

```sh
# 1. Export Lean 4 modules with lean4export
lean4export Init > /tmp/Init.export
lean4export Std > /tmp/Std.export
lean4export Mathlib.Data.Nat.Prime.Basic > /tmp/Mathlib_Prime.export

# 2. Run Rigor vs lean4checker side-by-side (Wall Time, Decls/sec, Peak RSS)
./crates/bench/run_head_to_head.sh /tmp/h2h_out /tmp/Init.export /tmp/Std.export /tmp/Mathlib_Prime.export
```

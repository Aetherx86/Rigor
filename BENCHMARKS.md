# Rigor Benchmarks & Optimization Report

## 0. Full Lean 4 `Init` and `Std` libraries vs `leanchecker --fresh` (2026-11-22)

Measured on the same Apple M4 (10 cores) with `/usr/bin/time -l` on an idle machine against Lean 4
v4.36.0-rc1 exports from `lake env lean4export`:

- **`Init`**: 58,546 declarations (59,978 environment entries), 6,495,289 NDJSON lines, 331.7 MiB.
- **`Std`**: 96,626 declarations (99,305 environment entries), 10,123,003 NDJSON lines, 532.0 MiB.

| Library | Checker | Wall time | Peak RSS |
| :--- | :--- | ---: | ---: |
| `Init` | `lake env leanchecker --fresh Init` | 28.67 s | 547 MB |
| `Init` | Rigor, parallel (`rigor-bench --check`, 10 threads) | 8.54 s | 479 MB |
| `Init` | Rigor, sequential (`RIGOR_SEQUENTIAL=1`) | 25.06 s | 404 MB |
| `Std` | `lake env leanchecker --fresh Std` | 44.18 s | 928 MB |
| `Std` | Rigor, parallel (`rigor-bench --check`, 10 threads) | 11.68 s | 695 MB |
| `Std` | Rigor, sequential (`RIGOR_SEQUENTIAL=1`) | 44.88 s | 567 MB |

Rigor's wall time includes parsing the 332 MiB (`Init`) / 532 MiB (`Std`) NDJSON export; `leanchecker`
reads compiled `.olean` files. Both accept the full libraries. Soundness evidence beyond acceptance:
`tools/mutation/` (1,440 mutants across `Init.Prelude`, `Init.Core`, and full `Init`; every
meaning-changing mutant rejected, see `tools/mutation/REPORT.md`).

The single-module figures in the sections below were measured earlier, before full-library support, and
are not representative of whole-library performance.

This document records reproducible performance, Peak RSS memory, and CPU profiling results for **Rigor** across Phases 1–4, including before/after optimization metrics and instructions for head-to-head comparison against Lean 4's `lean4checker`.

## Test Environment

- **Hardware:** Apple M4 (10 CPU cores, 16 GiB RAM, macOS)
- **Toolchain:** Rust `rustc` / `cargo` (`--release`), `/usr/bin/time -l` (OS-level maximum resident set size), `/usr/bin/sample` (CPU call-stack profiler)
- **Kernel TCB Footprint:** `crates/kernel/src/*.rs` = **3,300 SLOC** excluding tests, comments and blank lines (`#![forbid(unsafe_code)]`, zero third-party crates); above the 2,500 target since arbitrary-precision `Nat`, parallel checking, compact arena, and full `Std` reduction parity were added (`tools/tcb/PLAN.md` targets < 2,500 SLOC)
- **Correctness Gate:** 26/26 unit, inductive, `lean4export`, regression, and soundness torture tests passing with 0 warnings; all of Lean 4 `Init` and `Std` accepted; mutation harness in `tools/mutation/`.

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

## 3. Head-to-Head vs Lean 4's Official `leanchecker --fresh` (Real Lean 4 `Init` Modules)

Exported directly from Lean 4 `v4.36.0-rc1` using `leanprover/lean4export` v3.1.0 (NDJSON) and verified end-to-end by **Rigor** vs Lean 4's built-in `leanchecker --fresh` on the exact same modules (Wall Time and OS-level Peak RSS measured via `/usr/bin/time -l` on Apple M4):

| Real Lean 4 Module (`v4.36.0-rc1`) | Export Size / Env Decls | Rigor Wall (Throughput) | `leanchecker --fresh` Wall | Speedup | Rigor Peak RSS | `leanchecker` Peak RSS | Memory Reduction |
|---|---:|---:|---:|---:|---:|---:|---:|
| `Init.Prelude` | 3.64 MiB / 2,121 decls | **92.86 ms** (`19.8k/s`) | 660.0 ms | **7.11x** | **19.55 MB** | 61.58 MB | **3.15x less (-68.3%)** |
| `Init.Core` | 6.15 MiB / 3,913 decls | **101.03 ms** (`34.4k/s`) | 500.0 ms | **4.95x** | **24.48 MB** | 67.34 MB | **2.75x less (-63.6%)** |
| `Init.Data.Nat.Basic` | 7.66 MiB / 4,718 decls | **132.29 ms** (`32.4k/s`) | 550.0 ms | **4.16x** | **26.61 MB** | 70.27 MB | **2.64x less (-62.1%)** |
| `Init.Data.List.Basic` | 9.38 MiB / 5,314 decls | **168.83 ms** (`28.7k/s`) | 620.0 ms | **3.67x** | **32.50 MB** | 72.33 MB | **2.23x less (-55.1%)** |

Key architectural enablers for real Lean 4 `Init` compatibility and 2.2x–3.1x lower Peak RSS:
- **Zero-dependency streaming NDJSON (`lean4export` v3.1.0) + classic text parser** (`crates/parser/src/{lib.rs,ndjson.rs}`).
- **Sound nested inductive elimination** (`expand_nested_inductives` in `crates/kernel/src/inductive.rs`, verifying `Lean.Syntax` nested in `Array`/`List` via mutual expansion and full positivity/universe checking).
- **WHNF structure eta (`to_ctor_when_structure`) & `u128` `Nat` literal primitives** (`reduce_nat` in `crates/kernel/src/reduce.rs`, matching Lean 4's kernel semantics for `2^64` and `Char` bounds).
- **Per-declaration scratch arena reclamation** (`Arena::truncate_to` in `crates/kernel/src/arena.rs`, reclaiming temporary WHNF/def-eq expressions after every `add_decl`, cutting `Init.Data.List.Basic` Peak RSS from 120.31 MB to 32.50 MB).

### Reproducing All Benchmarks

```sh
cargo test --workspace
cargo run --release -p rigor-bench
./crates/bench/run_head_to_head.sh /tmp/rigor_bench
```

To benchmark against any exported Lean 4 module (text or NDJSON):

```sh
lake env lean4export Init.Data.List.Basic > /tmp/Init.Data.List.Basic.ndjson
/usr/bin/time -l ./target/release/rigor-bench --check /tmp/Init.Data.List.Basic.ndjson
/usr/bin/time -l lake env leanchecker --fresh Init.Data.List.Basic
```

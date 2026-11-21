# Rigor — Worklog (architecture + phase status for seamless handoffs)

Read this file first before modifying code. Update after every milestone.

## Project overview
Rigor is a high-performance, mathematically sound dependent type theory proof kernel (Calculus of Inductive Constructions, Lean 4 `lean4export`-compatible) written in safe Rust (`#![forbid(unsafe_code)]` in `crates/kernel`), engineered to outperform `lean4checker` on type-checking throughput, peak RSS memory, and kernel reduction.

- Project root: `~/Rigor`
- Owner: `Aetherx86 <omakasekim@naver.com>`
- Repo conventions: no emoji, no AI mentions, no Co-Authored-By trailers in commits or docs.
- TCB budget: `crates/kernel` strictly isolated, zero external dependencies, `#![forbid(unsafe_code)]`, target < 2,500 LOC.

## Toolchain status
- `cargo` / `rustc`: Homebrew keg-only rustup (`/opt/homebrew/opt/rustup/bin`).
- `gh`: installed (`/opt/homebrew/bin/gh`).
- `lean` / `lake`: not currently installed (needed in Phase 3/4 for real `lean4export` artifacts and `lean4checker` head-to-head benchmarks).

## Phase plan & status
- **Phase 1: Core Calculus & Arena Engine** (done)
  - Workspace (`crates/kernel`, `crates/parser`, `crates/bench`) at `~/Rigor`.
  - Zero-dep `crates/kernel` (`#![forbid(unsafe_code)]`, 2,177 total lines incl. comments/whitespace; inline FxHasher; two-tier parent/scratch flat DAG arenas for `NameId`, `LevelId`, `ExprId` as `u32`, $O(1)$ structural equality, precomputed `loose_bvar_range` / `HAS_FVAR` / `HAS_LEVEL_PARAM` metadata).
  - Predicative universe level algebra (`Zero`, `Succ`, `Max`, `IMax`, `Param`) with eager canonicalization and complete case-splitting `level_leq` / `level_eq`.
  - Spine-based WHNF reducer + definitional equality (beta, delta with height priority, zeta, proof irrelevance in `Prop`, function eta, DAG caches).
  - Bidirectional CIC type checker + `Environment` / `FrozenEnv` with lock-free parallel checking (`std::thread::scope` + `Arena::child`).
  - Verified (`cargo test --workspace`): 7/7 Phase 1 test suites pass (0 warnings).
  - Phase 1 release benchmarks (`cargo run --release -p rigor-bench`):
    * Arena interning (100k unique + 100k hits): 17.56 ms (11.39M ops/sec)
    * Church numeral reduction (`mul 20 25 == 500` by `Eq.refl`): 1.029 ms (4,838 arena nodes)
    * Theorem batch (2,000 decls): 4.98 ms / 401k decls/s (1 thread) -> 2.64 ms / 757k decls/s (10 threads, 1.88x)
- **Phase 2: Inductive Types & Soundness Torture Suite** (next)
  - Inductive types, constructors, recursors, iota-reduction, structure projections (`Proj`).
  - Strict positivity checker & universe level constraint validator (including Prop large-elimination / Subsingleton rules).
  - `tests/soundness/` negative torture suite (Girard/Type:Type, non-positive inductives, invalid Prop->Type large eliminations, proof-irrelevance violations, ill-typed recursors).
  - Keep `crates/kernel` strictly < 2,500 LOC total (compact repetitive `expr.rs` traversal helpers before/while adding `inductive.rs`).
- **Phase 3: `lean4export` Compatibility** (pending)
- **Phase 4: Head-to-Head Benchmarking & Optimization** (pending)

## Progress log
- 2026-11-22 01:30 KST: initialized `~/Rigor` workspace and started Phase 1 implementation.
- 2026-11-22 01:39 KST: completed Phase 1 (7/7 tests green, 0 warnings, benchmarks recorded); creating public GitHub repo `Aetherx86/Rigor`.

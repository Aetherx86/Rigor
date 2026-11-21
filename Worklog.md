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
- **Phase 2: Inductive Types & Soundness Torture Suite** (done)
  - Full CIC inductive validator & recursor generator (`crates/kernel/src/inductive.rs`, `env.rs`, `reduce.rs`, `check.rs`):
    * Single and mutual inductive blocks, constructors, recursors, iota-reduction, K-like reduction (`Eq.rec` on opaque `a = a`), structure projections (`Proj`), and structure eta (`S.mk (p.0) ... ≡ p`).
    * Strict positivity checker (rejects direct negative, double-negative, mutual negative cycles, non-uniform parameter recursion, and inductive mentions in recursive index arguments).
    * Predicative universe bound checks (`field_sort <= ind_sort` for non-Prop inductives, blocking Girard's paradox) and exact Subsingleton large-elimination rules (`Prop -> Type` allowed only for 0-ctor or 1-ctor Prop inductives whose fields are proofs or determined by indices; `Proj` also enforces the Prop witness-smuggling guard).
  - TCB size: `#![forbid(unsafe_code)]`, zero third-party deps, 2,771 raw lines (under 2,500 SLOC excluding comments/blank lines).
  - Verified (`cargo test --workspace`): 14/14 test suites pass (0 warnings):
    * `tests/phase1.rs` (7/7)
    * `tests/inductives.rs` (3/3: `Nat.add`/`Nat.mul` iota arithmetic, `Eq` K-like reduction, `Prod` projections & structure eta, indexed `Vec`, mutual `Even`/`Odd`, Subsingleton `And`)
    * `tests/soundness/main.rs` (4/4 negative torture tests: universe cycles & Girard impredicative Type inductive, direct/double/mutual/non-uniform non-positive inductives, invalid `Or.rec`/`Exists.rec` Prop->Type large eliminations & `Proj` witness smuggling, `Type` proof-irrelevance rejection & ill-typed recursor applications)
  - Phase 2 release benchmarks (`cargo run --release -p rigor-bench`):
    * Arena interning (100k unique + 100k hits): 11.55 ms (17.32M ops/sec)
    * Church numeral reduction (`mul 20 25 == 500`): 0.810 ms (4,839 arena nodes)
    * Inductive `Nat.rec` iota reduction (`Nat.mul 20 25 == 500`): 1.544 ms (3,213 arena nodes)
    * Theorem batch (2,000 decls): 3.88 ms / 515k decls/s (1 thread) -> 2.32 ms / 863k decls/s (10 threads)
- **Phase 3: `lean4export` Compatibility** (next)
  - Streaming zero-copy `lean4export` parser in `crates/parser` covering all directives (`#NS`, `#NI`, `#US`, `#UM`, `#UIM`, `#UP`, `#EV`, `#ES`, `#EC`, `#EA`, `#EL`, `#EP`, `#EZ`, `#EJ`, `#ELN`, `#ELS`, `#AX`, `#DEF`, `#THM`, `#OPAQ`, `#QUOT`, `#IND`).
  - Kernel `#QUOT` (quotient types + `Quot.lift` / `Quot.ind` reduction) & `Nat`/`String` literal reduction (`Nat.zero`/`Nat.succ` unfolding in `whnf` for Lean 4 compatibility).
- **Phase 4: Head-to-Head Benchmarking & Optimization** (pending)

## Progress log
- 2026-11-22 01:30 KST: initialized `~/Rigor` workspace and started Phase 1 implementation.
- 2026-11-22 01:39 KST: completed Phase 1 (7/7 tests green, 0 warnings, benchmarks recorded); created public GitHub repo `Aetherx86/Rigor` (commit `b41a1c2`).
- 2026-11-22 01:52 KST: completed Phase 2 (inductives, strict positivity, Subsingleton large-elim & `Proj` guard, iota/K-like/structure-eta reduction, soundness torture suite: 14/14 tests green, 0 warnings, `Nat.rec` benchmark 1.544 ms).

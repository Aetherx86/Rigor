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
- `elan` / `lean` / `lake` / `leanchecker`: installed via Homebrew `elan-init` (`leanprover/lean4:v4.36.0-rc1`); `leanprover/lean4export` built at `/tmp/lean4-tools/lean4export`.

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
- **Phase 3: `lean4export` Compatibility** (done)
  - Streaming zero-copy-token `lean4export` parser in `crates/parser` (`#![forbid(unsafe_code)]`, zero external deps) covering all 22 directives (`#NS`, `#NI`, `#US`, `#UM`, `#UIM`, `#UP`, `#EV`, `#ES`, `#EC`, `#EA`, `#EL` with `#BD`/`#BI`/`#BS`/`#BC`, `#EP`, `#EZ`, `#EJ`, `#ELN`, `#ELS`, `#AX`, `#DEF` with `O`/`A`/`R`, `#THM`, `#OPAQ`, `#QUOT`, `#IND`), plus mutual `#INDM` and `lean4export` v3 `#IND`/`#CTOR`/`#REC` (always kernel-validated rather than trusting exported recursor rules).
  - Kernel `#QUOT` (`Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind` — self-checked by `TypeChecker::check_decl` with atomic rollback on invalid `Eq` — plus `Quot.lift`/`Quot.mk` reduction) and `Nat` literal (`#ELN`) step-expansion in `reduce_iota_or_proj` and `is_def_eq`.
  - Verified (`cargo test --workspace`): 18/18 test suites pass (0 warnings), including `crates/parser/tests/lean4export.rs` (4/4: full `Init`/`Std`-style prelude exercising all 22 directives + `Quot.lift` computation + `Nat.add 2 3 = 5` via `#ELN` + `#EJ` `Prod` projection + `#ELS` UTF-8 strings; v3 `#IND`/`#CTOR`/`#REC`; mutual `#INDM`; and 6 negative soundness/syntax rejections with zero false positives).
  - Note: real Lean 4 `Init`/`Std` `.export` artifacts require `lean`/`elan` + `lean4export` installed locally (not present on this host yet).
  - Phase 3 release benchmark (`cargo run --release -p rigor-bench`):
    * Streaming `lean4export` parse + kernel verify (10,002 decls, 50,032 lines, 0.86 MiB): 12.85 ms (778k decls/s, 67.1 MiB/s).
- **Phase 4: Head-to-Head Benchmarking & Optimization** (done)
  - Automated benchmark harness & stress suite (`crates/bench/src/main.rs`, `crates/bench/run_head_to_head.sh`):
    * CLI modes: `--check <file.export>`, `--generate-export <path> <n>`, `--stress-only [iters]`, and default full suite.
    * Computational stress tests: Church `mul 25*40 == 1000`, inductive `Nat.rec` `mul 30*40 == 1200`, higher-order `Nat.rec` Ackermann `ack(3, 5) == 253`, and pure-CIC primality reflection (`isPrime 51 = false`, `53 = true`, `97 = true` by `Eq.refl`).
    * Head-to-head script capturing Wall Time, Decls/sec, and OS-level Peak RSS (`/usr/bin/time -l` on macOS, `-v` on Linux), auto-detecting `lean4checker` on `PATH` when installed.
  - Profile-guided kernel optimizations (`/usr/bin/sample` before/after):
    * Dedicated `app_map` (`(ExprId, ExprId) -> ExprId`) and `[u32; 32]` `bvar_cache` in `Arena`.
    * Unified spine abstract machine (`whnf_spine_with`) avoiding intermediate `App` re-interning across beta/zeta/proj/quot/iota/delta.
    * Zero-clone `&'a` decl borrows, cached 1-param level instantiation (`inst_lvl1_cache`), cached `Nat.zero`/`Nat.succ`, deferred `is_proof`, and lazy `FxHashMap` allocation in `expr.rs` `map_children`.
  - Regression test added in `crates/kernel/tests/inductives.rs` covering over-applied `Nat.rec`, over-applied `Quot.lift`, and `Lam` proof irrelevance (`19/19` tests green, `0` warnings).
  - Real Lean 4 v4.36.0-rc1 `Init` verification & head-to-head vs `leanchecker --fresh`:
    * Added zero-dependency streaming NDJSON (`lean4export` v3.1.0) parser (`crates/parser/src/ndjson.rs`), sound nested inductive elimination (`crates/kernel/src/inductive.rs`), WHNF structure eta (`to_ctor_when_structure`), `u128` `Nat` literal `reduce_nat`, and per-declaration scratch arena reclamation (`Arena::truncate_to`).
    * Verified 100% of real `Init.Prelude` (2,121 decls: 92.86 ms / 19.55 MB RSS vs `leanchecker` 660 ms / 61.58 MB — 7.11x faster, 3.15x less RAM), `Init.Core` (3,913 decls: 101.03 ms / 24.48 MB vs 500 ms / 67.34 MB — 4.95x faster, 2.75x less RAM), `Init.Data.Nat.Basic` (4,718 decls: 132.29 ms / 26.61 MB vs 550 ms / 70.27 MB — 4.16x faster, 2.64x less RAM), and `Init.Data.List.Basic` (5,314 decls: 168.83 ms / 32.50 MB vs 620 ms / 72.33 MB — 3.67x faster, 2.23x less RAM).
  - TCB size audit: `crates/kernel/src/*.rs` strictly < 2,500 SLOC (`#![forbid(unsafe_code)]`, zero external deps).

- **Phase 5: Full `Init` verification** (in progress, 2026-11-22)
  - Target: all of Lean 4 v4.36.0-rc1 `Init` (`lake env lean4export Init` run in `/tmp/lean4-tools/lean4export`
    -> `/tmp/rigor_real/Init.ndjson`, 6,495,289 lines, 332 MiB). Check with
    `RIGOR_TRACE=1000 ./target/release/rigor-bench --check /tmp/rigor_real/Init.ndjson` (stderr reports every
    declaration slower than 1000 ms and progress every 100k lines; run it with `timeout` and watch the stderr).
  - Fixed so far (each was found by the full-`Init` run):
    1. SOUNDNESS: large elimination from a 1-constructor Prop inductive was allowed when a non-proof field only
       occurred *inside* a result index (`P (f n)`), which proves False (extract different `n` from
       proof-irrelevant-equal proofs). Now the field must *be* an index, as in Lean (`Int.NonNeg.rec` has no
       universe parameter in Lean). Regression test `rejects_large_elimination_when_a_field_only_occurs_inside_an_index`.
    2. String literals expand to `String.ofList [Char.ofNat ..]` for recursors, projections and def-eq
       (`String.toByteArray_empty`).
    3. `Nat` literals are arbitrary precision (`crates/kernel/src/nat.rs`, dependency-free, unit tested) and all of
       Lean's accelerated ops are evaluated (add sub mul div mod gcd beq ble pow land lor xor shiftLeft shiftRight
       log2; pow/shift capped at 2^24 bits). u128 overflow used to fall back to unary unfolding.
    4. Def-eq failure cache (`def_neq_cache`); `reduce_nat` skips terms with free variables (as Lean); proof
       irrelevance is checked before structural comparison (Lean's order).
    5. `--check` runs on a 4 GiB-stack thread.
  - Result now: the run passes the first ~2.26M of 6.5M lines (~35%) and then hangs on `BitVec.reverse_replicate`
    (line 2,264,328; `zero => rfl` case). Diagnosis: whnf unfolds `Nat.add/mul/pow/sub` structurally (via
    `Nat.brecOn`, `*.match_1`, `*._f`) and counts a literal down from 2^32 one step at a time. Lean avoids this
    path; most likely its lazy-delta ordering (unfold the side with the greater height first, compare arguments
    of same-head applications before unfolding, `is_def_eq_offset` for succ/literal) or its `whnf` cache.
    NEXT: dump the exact def-eq pair at the top of that check (instrument `is_def_eq` depth <= 3 behind an env
    var), compare with Lean's `lazy_delta_reduction` in src/kernel/type_checker.cpp, fix, then continue the run.
  - Init.Prelude (95 ms, 19.8 MB RSS) and Init.Core (96 ms, 24.7 MB RSS) still verify fully after these changes.
  - TCB: kernel is now 2,815 SLOC (nat.rs adds 253), over the 2,500 target; trimming is open work.

## Progress log
- 2026-11-22 01:30 KST: initialized `~/Rigor` workspace and started Phase 1 implementation.
- 2026-11-22 01:39 KST: completed Phase 1 (7/7 tests green, 0 warnings, benchmarks recorded); created public GitHub repo `Aetherx86/Rigor` (commit `b41a1c2`).
- 2026-11-22 01:52 KST: completed Phase 2 (inductives, strict positivity, Subsingleton large-elim & `Proj` guard, iota/K-like/structure-eta reduction, soundness torture suite: 14/14 tests green, 0 warnings, `Nat.rec` benchmark 1.544 ms, commit `f879983`).
- 2026-11-22 02:04 KST: completed Phase 3 (streaming `lean4export` parser for all 22 directives + v3 `#IND`/`#CTOR`/`#REC` + `#INDM`, kernel `#QUOT` + `#ELN` reduction, 18/18 tests green, 0 warnings, 778k decls/s streaming parse+verify, TCB < 2,500 SLOC, commit `2e473b1`).
- 2026-11-22 02:19 KST: completed Phase 4 (head-to-head benchmark harness + Peak RSS script, Ackermann & primality reflection stress tests, `/usr/bin/sample` profile-guided spine-machine & arena optimizations up to 8.81x faster / -23.7% RSS, 19/19 tests green, TCB 2,484 SLOC, `BENCHMARKS.md`, commit `cb2ddff`).
- 2026-11-22 04:07 KST: verified real Lean 4 v4.36.0 `Init.Prelude`, `Init.Core`, `Init.Data.Nat.Basic`, `Init.Data.List.Basic` via NDJSON `lean4export`, nested inductives, `to_ctor_when_structure`, `u128` `reduce_nat`, and `Arena::truncate_to` — beating `leanchecker --fresh` by 3.67x-7.11x wall time and 2.23x-3.15x lower Peak RSS while keeping TCB < 2,500 SLOC.
- 2026-11-22 04:50 KST: Phase 5 started (full Init). Fixed unsound nested-index large elimination, string literal expansion, bignum Nat + all accelerated ops, failure cache, fvar guard in reduce_nat, proof-irrelevance order, big-stack checker. Blocked at BitVec.reverse_replicate (see Phase 5 NEXT).

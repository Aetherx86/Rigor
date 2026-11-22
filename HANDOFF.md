# Rigor hand-off (coordination file for the agents working on this repo)

Read this file and Worklog.md before doing anything. Update the "Log" section at the end of every step.

## Goal
Make Rigor better than Lean's own checker (`leanchecker --fresh`) on the full Lean 4 v4.36.0-rc1 `Init`
library, on BOTH wall time and peak memory, without weakening soundness.

Reference numbers on this Mac (Apple M4, 10 cores):
- leanchecker --fresh Init: 28.5 s wall, 550 MB peak RSS (measured with /usr/bin/time -l).
- Rigor today (parallel, all cores): 4.9-6.7 s wall, ~712 MB peak RSS. Sequential (RIGOR_SEQUENTIAL=1):
  27.7 s, 502 MB. Single worker thread: 566 MB. Each extra worker thread adds ~15 MB.
- Target: parallel wall time < 10 s AND peak RSS < 550 MB.

## How to build and measure (always use these exact commands)
    export PATH="/opt/homebrew/opt/rustup/bin:$PATH"
    cd ~/rigor
    cargo test -q --workspace                     # must stay all green (23+ tests), 0 warnings
    cargo build --release -q -p rigor-bench
    /usr/bin/time -l ./target/release/rigor-bench --check ~/rigor-data/exports/Init.ndjson
    # must print CHECK_OK decls=58546 ...; read "real" and "maximum resident set size" from stderr
    RIGOR_SEQUENTIAL=1 /usr/bin/time -l ./target/release/rigor-bench --check ~/rigor-data/exports/Init.ndjson
Small fast sanity inputs: ~/rigor-data/exports/Init.Prelude.ndjson, ~/rigor-data/exports/Init.Core.ndjson.
Never run two full Init checks at the same time (timings become meaningless).

## Rules
- Soundness first: never remove or weaken a check to make something pass. Every kernel change needs the
  full test suite green and a full Init CHECK_OK in both parallel and sequential mode.
- crates/kernel must stay `#![forbid(unsafe_code)]` with zero external dependencies.
- Commits: author Aetherx86 <omakasekim@naver.com> (already configured in this repo), plain technical
  messages, no emoji, no mention of AI or assistants, no Co-Authored-By lines. Only the coordinating
  session commits and pushes; workers do not run git commit or git push.
- File ownership while a task is in progress is listed per task below. Do not edit files owned by
  another task.

## Tasks
A. [owner: gem] Shrink `ExprData` from 24 to 16 bytes to cut arena memory (~6.3M expressions in Init).
   - `ExprData::Const(NameId, Box<[LevelId]>)` -> intern level lists in the Arena (new `LevelListId(u32)`,
     hash-consed like names/levels, with parent/child lookup like the other tables) and store
     `Const(NameId, LevelListId)`. Provide an accessor returning `&[LevelId]` so call sites stay simple.
   - `ExprData::Lit(Literal)` (Literal holds a boxed Nat or a boxed str) -> intern literals in an Arena
     table and store `Lit(LitId)`.
   - Truncation (`Arena::truncate_to`) and child arenas (`Arena::child`) must handle the new tables.
   - Add a unit test asserting `core::mem::size_of::<ExprData>() <= 16`.
   - Files owned: crates/kernel/src/* and crates/parser/src/* (call-site updates), crates/bench/src/*.
B. [owner: agy-mut] Mutation-testing harness in ~/rigor/tools/mutation/ only (see that directory).
C. [owner: coordinator] Verification of A and B, Worklog.md, BENCHMARKS.md, commits.
D. [next, unassigned] Per-thread scratch memory: profile which TypeChecker caches dominate for the
   heaviest declarations and bound them.
E. [owner: agy-mut] Read-only TCB SLOC reduction analysis in ~/rigor/tools/tcb/PLAN.md (target < 2,500 SLOC from 3,155 SLOC; no edits to crates/).

## Continuity rule (owner's instruction, 2026-11-22)
The process must not stop. Every agent (Claude coordinator = A, Gemini/Antigravity workers = B) appends to
the Log below after EVERY meaningful step, and immediately when it notices it is close to a rate limit,
quota or context limit: what was done, what is half-done (files, commands), and the exact next step. A fresh
agent must be able to continue from this file alone.

## Data locations (persistent; /tmp is wiped on reboot)
- lean4export build: ~/rigor-data/lean4export (`lake env .lake/build/bin/lean4export <Module>` from there)
- Exports: ~/rigor-data/exports/{Init,Std,Init.Prelude,Init.Core}.ndjson (regenerate if missing)
- Rigor binary: ~/rigor/target/release/rigor-bench
- ChronosVault moved to ~/ChronosVault (was ~/Documents/ChronosVault; ~/Documents is often blocked by macOS
  privacy settings for these processes).

## Recovery (rate limits, quota, stalls)
- The coordinator (Claude session in herdr pane w2:p1) re-checks every hour (:23) and also resumes after its
  own usage limit resets. Workers: gem in w2:p3 (Task A), agy-mut in w2:p2 (Task B), both `agy` (Antigravity
  CLI, Gemini) started with --dangerously-skip-permissions.
- If a worker hits a rate limit, quota, context limit or stalls: stop it (ctrl+c, exit), start a fresh one in
  the same pane: `herdr agent start <name> --kind agy --pane <pane> -- --dangerously-skip-permissions`,
  accept the folder-trust prompt for ~/Rigor, then prompt: "Read ~/rigor/HANDOFF.md and continue your task
  (<task letter>) from the Log." Workers must therefore append to the Log after every meaningful step.
- A worker that resumes must first inspect `git status` / `git diff` to see partial work before continuing.

## Log
- 2026-11-22 06:30 KST: parallel deferred checking landed (check_deferred, parse_file_parallel), id-only
  hash-consing table (expr_table) replaced expr_map/app_map. Uncommitted at this point; coordinator will
  commit after verification. Task A assigned to gem, task B running in agy-mut.
- 2026-11-22 06:20 KST: Task B round 1 done (agy-mut): tools/mutation/mutate.py, 250 mutants of Init.Prelude, 249 rejected, 1 accepted = Lean.Name.str -> Lean.Name.mkStr (abbrev of the constructor, definitionally equal; correct). Reviewed by coordinator, committed. Task B round 2: larger modules and more mutants.
- 2026-11-22 06:16 KST: Task B round 2 done (agy-mut): added inductive_mutation and level_arity_mismatch (7 operators total); seed=2 ran 700 mutants on Init.Core (697 rejected, 3 accepted: Std.Trichotomous/Std.IdempotentOp/Std.Symm Prop->Type 0, all valid 1-ctor Prop-field structures whose only downstream uses remain well-typed via imax 1 0 = 0; harmless) and 350 mutants on Init.Prelude (350 rejected, 0 accepted); total 1050 mutants, 1047 rejected, 3 harmless accepted, 0 soundness bugs (see tools/mutation/REPORT.md).
- 2026-11-22 06:15 KST: Task A done (gem): shrank ExprData from 24 to 16 bytes (interned Const level lists via LevelListId and literals via LitId, dropped unused Let binder name, updated Arena::child, Arena::truncate_to, Arena::shrink_for_sharing, and all kernel call sites; added size_of::<ExprData>() <= 16 and child/truncate tests). cargo test -q --workspace: 25/25 passed, 0 warnings. Full Init CHECK_OK (58,546 decls, 6,311,599 arena_exprs): parallel 12.58 s real (12.31 s check; host shared with Task B), 442,548,224 B (422.0 MiB) peak RSS; sequential 31.34 s real (31.33 s check), 359,776,256 B (343.1 MiB) peak RSS.
- 2026-11-22 06:55 KST (coordinator): verified Task A: 25/25 tests, forbid(unsafe) intact. Quiet-machine full Init: parallel 7.78 s / 445 MB, sequential 23.89 s / 377 MB; leanchecker --fresh Init 28.67 s / 547 MB. GOAL MET (faster and smaller in both modes). Committed. Task B round 2 (agy-mut): 1,050 mutants, 3 accepted, all harmless Prop->Type 0 changes of single-proof-field structures (verified reasoning).
- 2026-11-22 06:41 KST: Task E done (agy-mut, read-only): analysed crates/kernel/src/*.rs (3,155 SLOC) and wrote ~/rigor/tools/tcb/PLAN.md identifying 753 SLOC of core low-risk savings (773 SLOC with optional Lam/Pi binder-field drop; projected 2,402 SLOC, < 2,500 target) across dead/test-only code, non-TCB moves (FrozenEnv, Nat::from_dec, format_name), and deduplication (inductive.rs -145, arena.rs Table<T> -120, nat.rs -99, reduce.rs -90, DAG visitor -65).
- 2026-11-22 06:40 KST (A): machine rebooted at 06:35, /tmp wiped (exports and /tmp/lean4-tools gone; the Std check was killed at line 10M of 10.1M with no rejection so far). Rebuilding lean4export in ~/rigor-data. NEXT: regenerate exports to ~/rigor-data/exports, re-run Std check; gem: review ~/ChronosVault (3 new commits 1ba83cb..45c39c7 by another tool); agy-mut: Task E (TCB reduction plan, read-only) was interrupted, redo.
- 2026-11-22 06:45 KST (A): lean4export rebuilt in ~/rigor-data; exports regenerated in ~/rigor-data/exports (Init 6,495,289 lines, Std 10,123,003). Std check restarted (log ~/rigor-data/std_trace.log, result ~/rigor-data/std_check.log). gem: ChronosVault review; agy-mut: Task E.
- 2026-11-22 06:42 KST (gem): ChronosVault review (~/ChronosVault, commits 1ba83cb, 8e75bce, 45c39c7) done. Working tree clean; no files changed. All 7 checks PASS: test:core (23/23), build:wasm, typecheck, eslint src, build, npm test (27/27), test:browser (17/17, 0 console errors). Security checks clean (no share/key/entropy/mnemonic logging, Share 3B client-sealed with heir passphrase, Testnet4-only enforced, no emoji/AI mentions/secrets). Noted concerns: proactive rotation overwrites local Share 1 before server rotateVault succeeds and leaves existing Share 3B stale until heir is re-registered; GET /api/vault/activity exposes cosine similarities unauthenticated; offline verifier HTML reads iterations without bounds check.
- 2026-11-22 06:44 KST (gem, coordinator): Step 4 done — recorded ChronosVault review outcome in ~/ChronosVault/Worklog.md, committed (a50785c) and pushed to origin/main. Checking running Std check (PID 8125, ~5 min elapsed, 261% CPU, 3.16 GB RSS).

## TAKEOVER (A is out of usage, 2026-11-22 07:00 KST): gem becomes coordinator
gem: after finishing your current ChronosVault review, act as coordinator (the role A had). Do these in order,
appending to this Log after each step:
1. Std result: read ~/rigor-data/std_trace.log and ~/rigor-data/std_check.log. If CHECK_OK: record decls,
   wall time and peak RSS here and in Worklog.md, then run leanchecker for comparison:
   `cd ~/rigor-data/lean4export && /usr/bin/time -l lake env leanchecker --fresh Std` (PATH needs
   /opt/homebrew/bin and ~/.elan/bin). If Rigor rejected something: identify the declaration with the line
   number (python3: scan the NDJSON for {"in":...} names up to that line), find the missing kernel rule by
   comparing with Lean's src/kernel/type_checker.cpp (fetch: gh api
   "repos/leanprover/lean4/contents/src/kernel/type_checker.cpp?ref=v4.36.0-rc1" -H
   "Accept: application/vnd.github.raw"), fix it in crates/kernel with a regression test, then re-run
   `cargo test -q --workspace` and both the Init and Std checks.
2. agy-mut's Task E plan (~/rigor/tools/tcb/PLAN.md): implement the low-risk items one at a time; after
   each: cargo test -q --workspace (all green, 0 warnings), full Init check parallel and sequential
   (CHECK_OK, record time/RSS), then commit.
3. Commits: only verified work, author Aetherx86 <omakasekim@naver.com> (repo config already set), plain
   technical message, no emoji, no AI/assistant mentions, no Co-Authored-By line; then `git push origin HEAD`.
4. ChronosVault (~/ChronosVault): commit your verified fixes there the same way if you made any; record the
   review outcome in ~/ChronosVault/Worklog.md.
Never weaken a kernel check to make something pass. Keep the continuity rule above.

## CYCLE (owner's instruction): perpetual hand-back between Claude and Gemini until everything is done
- Agents: Claude coordinator = `claude-lead` (herdr pane w2:p1); Gemini coordinator/worker = `gem` (w2:p3);
  Gemini worker = `agy-mut` (w2:p2).
- Whoever holds the coordinator role works through the TAKEOVER list and the Log's NEXT items. When it has
  finished its current batch, OR is close to a usage/rate/context limit, it MUST:
  1. append to the Log: what was done, what is half-done (files, commands), and the exact next step;
  2. hand the role to the other side WITHOUT waiting:
     - gem -> Claude:  `herdr agent prompt claude-lead "Your turn: read the Log and TAKEOVER/CYCLE sections in ~/rigor/HANDOFF.md and continue as coordinator."`
     - Claude -> gem:  `herdr agent prompt gem "Your turn: read the Log and TAKEOVER/CYCLE sections in ~/rigor/HANDOFF.md and continue as coordinator."`
  3. If the hand-off prompt fails because the other agent is busy, wait (`herdr agent wait <name> --timeout 600000`) and retry;
     if the other agent is rate-limited or gone, keep working yourself and log it.
- Stop the cycle only when every item in TAKEOVER and every NEXT in the Log is done and verified; then write
  "ALL DONE" with a final summary at the end of the Log.
- 2026-11-22 09:05 KST (A): Std check hung near its end (passed line 10M of 10.1M, killed by timeout, exit 143); gem is debugging it (a Nat.rec countdown loop; editing crates/kernel/src/reduce.rs, uncommitted). agy-mut finished Task E (tools/tcb/PLAN.md: 753 SLOC of low-risk savings, 3,155 -> 2,402) and was restarted with --dangerously-skip-permissions; next for agy-mut: Task B round 3 (Init.ndjson mutants, tools only). PLAN.md implementation waits until gem has finished in reduce.rs.

- 2026-11-22 11:28 KST (agy-mut): Task B round 3 in progress: upgraded ~/rigor/tools/mutation/mutate.py for 6.5M-line Init.ndjson (mmap-backed LazyExprStore, O(log N) candidate selection, streaming binary mutant emission, and sound two-stage `--truncate` mode that truncates right after the mutated decl + direct dependents and automatically re-verifies any Stage-1 accept against the full un-truncated file); smoke-tested on Init.Prelude (21 mutants in 0.77s). Next: running Round 3 on ~/rigor-data/exports/Init.ndjson (seed=3, per-op=20, 140 mutants total), then reviewing every accepted mutant and appending Round 3 to ~/rigor/tools/mutation/REPORT.md.
- 2026-11-22 10:45 KST (A, coordinator turn): Std investigation.
  * The Std hang is in `_private.Std.Time.Time.Unit.Basic.0.Std.Time.Nanosecond.Offset.ofHours._proof_1`
    (Std.ndjson line 2,035,582; source Std/Time/Time/Unit/Basic.lean:84, `by decide +kernel` over Rat with
    3600000000000). A cut file ending at that declaration is ~/rigor-data/exports/std_head.ndjson (sequential
    check hangs at its last line; use `RIGOR_SEQUENTIAL=1 timeout 120 ...`).
  * leanchecker --fresh Std (measured by gem): 44.18 s, 927.5 MB peak RSS.
  * First cause found and fixed (committed): K-like recursors (Eq.rec) reduced the major premise before trying
    `to_cnstr_when_K`, so the proof `Nat.eq_of_beq_eq_true` was unfolded over 13-digit numbers. Now the K
    replacement is tried on the unreduced major first, as in Lean's inductive_reduce_rec. Tests 25/25, Init OK.
  * Still hangs after that: now `Nat.sub` is unfolded structurally via `Nat.brecOn` (counting down) inside
    Rat/Int comparisons (`Rat.mk'`, `Int.instLTInt`, `Int.instLEInt` appear just before). Lean avoids this.
    Lean source with the relevant code: ~/rigor-data/lean-src/type_checker.cpp. Leads:
    (1) Lean's `is_def_eq_core` reflection fast path (line ~1134): if `t` has no fvars (or eager mode) and `s`
        is `Bool.true`, `whnf(t)` and compare; Rigor has no such path.
    (2) `eagerReduce` mode (lines 169-180, 1056): an app argument `eagerReduce _ _` turns on eager mode in which
        reduce_nat and the reflection path also apply to terms WITH free variables.
    (3) Lean's whnf calls reduce_nat with NO free-variable guard (lines 725-735); the guard is only in
        lazy_delta_reduction (1056). Rigor's `has_opaque_fvar` guard sits inside whnf's try_reduce_nat; consider
        matching Lean exactly (guard only in def-eq lazy delta, plus eager mode).
    (4) Lean's lazy_delta_reduction tries reduce_nat on both sides before unfolding (1056-1062).
    Plan: implement (1)-(4) to match Lean, add regression tests, re-run std_head, then full Std and Init.
  * gem's earlier debug instrumentation (countdown detector) is in `git stash` ("gem debug instrumentation").
  * Task E plan (agy-mut) is in tools/tcb/PLAN.md: 753 SLOC of low-risk savings (3,155 -> 2,402). Implement
    after Std passes, one item at a time with tests + full Init check.
  NEXT (gem, coordinator): leads (1)-(4) above until std_head and full Std pass; record Std time/RSS vs
  leanchecker 44.18 s / 927.5 MB; then Task E; hand back to claude-lead per CYCLE when done or near a limit.
- 2026-11-22 11:43 KST (agy-mut): Task B round 3 done on full ~/rigor-data/exports/Init.ndjson (6,495,289 lines, seed=3, 20 per operator, 7 operators = 140 mutants total; `--truncate` averaged 3,542,856 / 6,495,289 lines = 54.5% with automatic full-file Stage-2 re-verification for Stage-1 accepts; 820.46 s elapsed). Totals: 140 generated, 139 rejected (99.3%), 1 accepted (harmless), 0 soundness bugs. Per-operator: `thm_value_swap` 20/20, `const_swap` 20/20, `arg_swap` 20/20, `level_change` 20/20, `def_body_rfl_break` 19/20 (3 rejected at later dependent decl), `inductive_mutation` 20/20 (6 rejected at later dependent decl, including #108 caught by Stage-2 full recheck), `level_arity_mismatch` 20/20. Sole accepted mutant: #89 (`def_body_rfl_break`, `HSMul.hSMul` line 554307, `outParam -> semiOutParam`), harmless because both are `@[reducible] def ... (α : Sort u) : Sort u := α` in `Init/Prelude.lean:749,772` (identical `type`/`value`/`hints` in NDJSON, definitionally equal). Appended Round 3 section + review to ~/rigor/tools/mutation/REPORT.md; JSON saved to ~/rigor/tools/mutation/results_round3_init.json. No crates edited, no cargo run, no commit.
- 2026-11-22 11:49 KST (agy-mut): Task D done (read-only analysis; no edits to crates/, no cargo, no commit): profiled per-declaration memory structures in crates/kernel/src/{check.rs,reduce.rs,env.rs,arena.rs,expr.rs}, profiled top-20 heaviest declarations in ~/rigor-data/exports/Init.ndjson, and compared with Lean 4 v4.36.0-rc1 (~/rigor-data/lean-src/type_checker.cpp, type_checker.h, environment.cpp, alloc.h). Wrote ~/rigor/tools/tcb/MEMORY.md. Key findings: (1) child Arena is the biggest per-worker consumer (~40 B/expr) and single-binder instantiate1 in check.rs:192-234 causes 5x-24x temporary ExprData blowup on deep telescopes (e.g. 24 leading Lams over a 16k-node DAG -> ~384k temp exprs = ~15 MB); (2) whnf_cache (reduce.rs:45-52) caches already-WHNF Sort/Pi/Lam/Lit/FVar/Const unlike Lean (type_checker.cpp:703-718), and def_neq_cache caches globally unlike Lean's narrow m_failure (type_checker.cpp:1000-1006); (3) Lean has no numeric entry caps on type_checker::state caches (only 128 MB Nat limit), relying instead on trivial-case filtering, batched telescopes, narrow m_failure, and ref-counted exprs + mimalloc; (4) check_deferred allocates fresh Arena::child + TypeChecker 57,937 times in module-clustered order. Combined plan estimates ~45-65 MB reduction on 10-thread Init (445 MB -> ~380-400 MB).
- 2026-11-22 15:10 KST (A, coordinator turn): committed gem's Std fix after verification (26/26 tests, Init
  CHECK_OK; no debug output): Lean's eagerReduce mode, Bool.true reflection fast path, is_def_eq_offset,
  cheap projections (whnf_core cheap_proj, try_unfold_proj_app), congruence before unfolding. With it the
  sequential Std check passes ~9.84M of 10.12M lines. gem's chained benchmark had hung in the PARALLEL Std
  run (1 h 40 min) and was stopped by A.
  NEXT BLOCKER: `_private.Std.Time.Format.0.Std.Time.PlainTime.format._sparseCasesOn_1` (Std.ndjson line
  9,836,899, a `def` with hint abbrev, levelParams 1; generated sparse casesOn for a match in
  Std/Time/Format.lean). The sequential check stays on this declaration for 30+ minutes. Make a cut file with
  `head -n 9836899 Std.ndjson > std_head2.ndjson` (or start from the existing std_head.ndjson idea), find what
  is being unfolded (temporary eprintln of delta names, removed before commit), compare with Lean.
  Timing note: an Init parallel run reported time_ms=12443 but 553 s wall with 76 s user, so the machine
  was likely asleep; re-measure Init/Std timings on an awake, idle machine before recording them.
  NEXT (gem): fix this blocker, then full Std parallel + sequential and leanchecker comparison (44.18 s /
  927.5 MB), then Task E (tools/tcb/PLAN.md) and the MEMORY.md plan. Always run long checks with `timeout`.
- 2026-11-22 16:40 KST (gem, coordinator turn): Fixed the `_private.Std.Time.Format.0.Std.Time.PlainTime.format._sparseCasesOn_1` blocker!
  * Root cause: `try_reduce_nat` still had an `has_opaque_fvar` guard even when `allow_delta == true` (`whnf`). In `_sparseCasesOn_1`, `Std.Time.Modifier.ctorIdx (Std.Time.Modifier.G x)` syntactically mentions opaque fvar `x` but reduces to a constant `Nat` literal; the guard prevented `Nat.mod` from reducing in `whnf`, causing `Nat.mod` to unfold into `Nat.modCore` repeated subtraction.
  * Fix (`crates/kernel/src/reduce.rs`): apply the `has_opaque_fvar` guard in `try_reduce_nat` ONLY when `!allow_delta && !self.eager_reduce` (matching Lean 4's `whnf` vs `lazy_delta_reduction`), plus regression test in `crates/kernel/tests/inductives.rs`.
  * Verified: `cargo test -q --workspace` 26/26 passed, 0 warnings. Idle-machine results (`/usr/bin/time -l`, sequential runs, no contention):
    - Full `Init` (58,546 decls / 59,978 env_decls, 6,495,289 lines, 331.7 MiB):
      * parallel: **8.54 s** wall, **478,887,936 B (478.9 MB / 456.7 MiB)** peak RSS (vs `leanchecker --fresh Init` 28.67 s / 547 MB)
      * sequential: **25.06 s** wall, **404,422,656 B (404.4 MB / 385.7 MiB)** peak RSS
    - Full `Std` (96,626 decls / 99,305 env_decls, 10,123,003 lines, 532.0 MiB):
      * parallel: **11.68 s** wall, **694,927,360 B (694.9 MB / 662.7 MiB)** peak RSS (**3.78x faster, 25.1% less RAM** vs `leanchecker --fresh Std` 44.18 s / 927.5 MB)
      * sequential: **44.88 s** wall, **566,657,024 B (566.7 MB / 540.4 MiB)** peak RSS
  * Updated `BENCHMARKS.md` and `Worklog.md`; committing & pushing now.
  * NEXT: Task E (`tools/tcb/PLAN.md`: reduce `crates/kernel/src/*.rs` from 3,300 SLOC to < 2,500 SLOC, Wave 1 -> Wave 2 -> Wave 3), then `tools/tcb/MEMORY.md` per-thread memory optimizations. Starting Wave 1 now.
- 2026-11-22 16:35 KST (agy-mut): Silica portal page upgrade done in ~/Documents/aetherx86.github.io/silica/{index.html,sim.js,test.mjs} (no edits to ~/rigor/crates, no commit/push). Ported Kotlin Rule (B/S + legacy S/B notation, rejects counts > 8 and reversed S/B letters), Rle (read/parse/write with MAX_COORDINATE=2^30, MAX_RUN_LENGTH=1,000,000, DEFAULT_MAX_CELLS=10,000,000, 70-char wrapping, header/comments/topology-suffix support), Patterns (GLIDER, GOSPER_GUN, ACORN, DIEHARD, PULSAR, R_PENTOMINO, BLINKER, BLOCK), and active-span Life engine supporting arbitrary B/S rules (including B0 fallback). Updated index.html with strict CSP (`script-src 'self'`, zero inline handlers/scripts), responsive mobile layout, rule input + presets, pattern presets, and RLE import/export panel. Verified: `node ~/Documents/aetherx86.github.io/silica/test.mjs` passed (`all silica checks passed`, 0.40s wall, including Diehard dies at gen 130 and Acorn reaches 633 cells at gen 5206 on 2600x2600) + static HTML/JS/CSP check (`HTML_JS_CSP_OK`, 21/21 IDs matched, 0 inline handlers/scripts).
- 2026-11-22 17:05 KST (A, hourly check): independently re-verified gem's 1e4332d from a clean worktree (no
  uncommitted Task E edits): Std CHECK_OK 96,626 decls, 11.86 s wall / 695.6 MB peak (leanchecker --fresh
  44.18 s / 927.5 MB); Init CHECK_OK 7.76 s / 478.5 MB (leanchecker 28.67 s / 547 MB). Milestone confirmed:
  Rigor checks both Init and Std. gem continues Task E (Wave 1) in the working tree.
- 2026-11-22 17:25 KST (A, took over: Gemini account quota exhausted for both gem and agy-mut, resets in
  ~146 h, around 2026-11-28 19:00 KST). Reviewed and committed gem's partial Task E Wave 1 (dead fields
  name/binder_info/is_reflexive/ctor_idx, unused FrozenEnv/check_batch_parallel, Display match, lvl_zero,
  Nat decimal parsing moved to the parser): no change to what the kernel accepts. Tests green; Init CHECK_OK
  7.59 s / 482 MB, Std CHECK_OK 10.99 s / 690 MB. Kernel non-blank non-comment lines 3,418 -> 3,322.
  A continues Task E alone; CYCLE hand-backs to gem are paused until the quota resets.
- 2026-11-22 18:10 KST (A): Task E progress, all verified (tests, full Init + Std CHECK_OK, 42-mutant
  round on inductive changes): f4f57b0 arena Table<T> (3,157 -> 3,077), 887a5e1 any_subexpr /
  replace_expr / inductive helpers (-> 2,962), 40e8bf2 reduce.rs helpers (-> 2,892). Count method:
  tools/tcb/PLAN.md baseline command. Remaining to < 2,500: ~393 (check.rs arms, env.rs add_quot,
  has_opaque_fvar/require_known_consts via any_subexpr, hash.rs, nat.rs compaction).
  Released v0.1.0 (55f0c43: README, LICENSE, CHANGELOG, web/ crate, CI). Portal: rigor/ live checker
  page + card (8e295d1). GitLab still on hold per user.
- 2026-11-22 18:40 KST (A): more Task E, all verified (tests, Init + Std CHECK_OK): 34ea9e5 env.rs
  (-> 2,847), 512f934 check.rs (-> 2,783). Mutation round 5 (seed 5, 42 mutants) after the check.rs change:
  42/42 rejected (total now 1,524 mutants over five rounds, none meaning-changing accepted). CI green on
  main and v0.1.0. NEXT (A, or gem after its quota resets ~2026-11-28): ~284 more lines to < 2,500:
  hash.rs (56), nat.rs (208), level.rs (137), inductive.rs recursor builders (major_ty built twice,
  motive/minor loops), reduce.rs K-rule block; then MEMORY.md plan. Keep each step verified.
- 2026-11-22 19:20 KST (A, hourly check; Gemini quota still out): ecd6b31 hash.rs + nat.rs compaction
  with a new 20,000-case randomized Nat test against u128 (-> 2,671); then structure()/major_type helpers
  (2,670). All verified: tests, Init 7.8 s / 477 MB, Std 11.0 s / 689 MB. ~171 lines left to < 2,500.
  Remaining duplication is small; what is left is mostly long match arms in reduce.rs (whnf_spine_with
  K/iota block) and inductive.rs nested-inductive discovery. Next: extract the K-rule and iota steps of
  whnf_spine_with into methods, flatten the nested-aux discovery in inductive.rs; mutation round after.
- 2026-11-22 18:56 KST (A, hourly check): Gemini quota still out (gem, agy-mut idle until ~2026-11-28). Rigor Task E paused at 2,670 lines while A works on the user's Osmium compressor request; resume from the 19:20 entry's NEXT.

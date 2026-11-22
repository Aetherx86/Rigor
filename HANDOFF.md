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

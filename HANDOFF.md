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
- 2026-11-22 06:40 KST (A): machine rebooted at 06:35, /tmp wiped (exports and /tmp/lean4-tools gone; the Std check was killed at line 10M of 10.1M with no rejection so far). Rebuilding lean4export in ~/rigor-data. NEXT: regenerate exports to ~/rigor-data/exports, re-run Std check; gem: review ~/ChronosVault (3 new commits 1ba83cb..45c39c7 by another tool); agy-mut: Task E (TCB reduction plan, read-only) was interrupted, redo.
- 2026-11-22 06:45 KST (A): lean4export rebuilt in ~/rigor-data; exports regenerated in ~/rigor-data/exports (Init 6,495,289 lines, Std 10,123,003). Std check restarted (log ~/rigor-data/std_trace.log, result ~/rigor-data/std_check.log). gem: ChronosVault review; agy-mut: Task E.

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

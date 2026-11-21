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
    /usr/bin/time -l ./target/release/rigor-bench --check /tmp/rigor_real/Init.ndjson
    # must print CHECK_OK decls=58546 ...; read "real" and "maximum resident set size" from stderr
    RIGOR_SEQUENTIAL=1 /usr/bin/time -l ./target/release/rigor-bench --check /tmp/rigor_real/Init.ndjson
Small fast sanity inputs: /tmp/rigor_real/Init.Prelude.ndjson, /tmp/rigor_real/Init.Core.ndjson.
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

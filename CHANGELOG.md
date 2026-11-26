# Changelog

## [0.3.0] - 2026-11-27

### Added
- Shortest dependency chain witness tracing (`shortest_dependency_path` in `crates/parser/src/audit.rs`): explains *why* a theorem transitively depends on an axiom or lemma (e.g., tracing the exact lemma chain introducing `sorryAx` or `Classical.choice`) in deterministic sorted order, strictly outside the TCB.
- Direct reverse-dependents query (`reverse_dependents`) and filtered declaration enumeration (`list_decls` with `DeclKind::from_str_name` and dotted prefix filtering).
- New `rigor-bench` CLI commands: `--why <file> <decl> <dep>`, `--rdeps <file> <decl>`, and `--list <file> [--kind K] [--prefix P]` (all supporting `--json`, `--sequential`, and `--threads`).
- New WebAssembly export `why(input, from_name, to_name)` in `web/src/lib.rs`.
- Strict `cargo clippy --workspace --all-targets -- -D warnings` step in `.github/workflows/ci.yml` and Korean documentation (`README.ko.md`).

## [0.2.0] - 2026-11-24

### Added
- Transitive axiom footprint auditing and declaration inspection (`crates/parser/src/audit.rs`):
  computes exact transitive axiom dependencies for any declaration (analogous to Lean's
  `#print axioms`) or across an entire verified environment via reverse-BFS, classifies standard
  axioms (`propext`, `Quot.sound`, `Classical.choice`) vs non-standard/trust-extending axioms
  (`sorryAx`, `Lean.ofReduceBool`, `Lean.trustCompiler`, custom axioms), and enforces
  `--forbid-sorry` and `--allow-axioms` verification policies.
- Bounded, cycle-safe pretty-printer (`crates/parser/src/pretty.rs`) for Lean names, universe
  levels, expressions (with binder-name resolution), and human-readable kernel error diagnostics.
- Extended `rigor-bench` CLI with `--audit <file> [--decl <name>]`, `--inspect <file> <decl>`,
  `--json`, `--sequential`, `--threads <N>`, `--forbid-sorry`, `--allow-axioms <list>`,
  `--version`, and clean non-panicking exit codes.
- New WebAssembly exports in `web/`: `audit(input, decl_name)` and `version()`, while preserving
  the existing `check(input)` signature and schema (now with human-readable error diagnostics).
- Configurable parser resource limits (`ParseLimits`) and `ParseError::LimitExceeded`.

### Changed
- Kernel memory and telescope optimization (`crates/kernel`): batched `Lam`/`Pi`/`Let` telescope
  opening and `infer_only` `App` spines via `instantiate_rev`, batched `Pi`/`Lam` definitional
  equality (`bindings_def_eq`), fast-return guards skipping trivial WHNF and leaf `infer_type`
  cache entries, parent arena intern-map shrinking in `Arena::shrink_for_sharing`, and
  coprime-stride parallel work dispatch in `Environment::check_deferred` with lock-free earliest
  error tracking. Peak RSS drops from 478 MB to 355 MB on parallel `Init` (-25.7%) and from
  696 MB to 547 MB on parallel `Std` (-21.4%).
- Added read-only `Environment::decls()` and `Environment::is_empty()` accessors without
  expanding the Trusted Computing Base beyond ~2,700 lines.

### Security & Hardening
- Hardened `crates/parser` against hostile and malformed `lean4export` inputs: strict JSON
  nesting depth limit, sparse-ID allocation bomb protection, `u32`/`usize` overflow checks,
  rejection of negative/floating-point values outside `mdata`, trailing-token rejection after JSON
  objects, UTF-8-safe JSON escape scanning, bounded `Vec::with_capacity` in text inductive
  directives, `Nat` literal digit limits, and mutual inductive consistency checks (`levelParams`,
  `numParams`, duplicate `cidx`, and orphan constructors).

### Verified
- Full workspace unit, soundness, telescope, parallel differential, audit, hostile-input, and CLI
  tests (37/37 tests), `cargo clippy --workspace --all-targets -- -D warnings`, and
  `wasm32-unknown-unknown` release build.
- Full Lean v4.36.0-rc1 `Init` (58,546 decls, parallel 355 MB / sequential 347 MB) and `Std`
  (96,626 decls, parallel 547 MB), plus full `Std` axiom audit (`--forbid-sorry --allow-axioms
  propext,Quot.sound,Classical.choice`: 68,728 theorems, 0 `sorryAx` dependents).
- Additional mutation round on `Init.Prelude` (28/28 mutants rejected across all 7 operators).

## [0.1.1] - 2026-11-23

### Changed
- The kernel is about 2,600 lines (from about 3,150): shared helpers replace duplicated code
  (one generic intern table, one subexpression walk, shared binder instantiation,
  compact Nat arithmetic with a randomized test against u128, and others). What the kernel
  accepts is unchanged: full Init and Std still verify, and mutation testing (now 1,608 mutants
  over eight rounds) rejects every meaning-changing mutant.

## [0.1.0] - 2026-11-22

First release.

### Features
- Kernel for Lean 4's type theory in safe Rust (`#![forbid(unsafe_code)]`, no dependencies):
  universes, mutual and nested inductive types with generated recursors, definitional equality
  following Lean's `type_checker.cpp` (lazy delta, K-like reduction, quotients, proof
  irrelevance, function and structure eta, unit-like types, big `Nat` literals, string literals,
  `Bool.true` reflection and `eagerReduce`).
- `lean4export` 3.x NDJSON and text-format parser.
- Parallel checking of independent declarations (`rigor-bench --check`), with `RIGOR_THREADS`,
  `RIGOR_SEQUENTIAL` and `RIGOR_TRACE`.
- Browser build in `web/` (the live demo on omakasekim.github.io/rigor).
- Mutation-testing harness in `tools/mutation/`.

### Verified
- Lean v4.36.0-rc1 `Init` (58,546 declarations) in 7.8 s / 478 MB and `Std` (96,626) in
  11.9 s / 696 MB, against `leanchecker --fresh` at 28.7 s / 547 MB and 44.2 s / 928 MB.
- 1,482 mutants over four rounds; every meaning-changing mutant rejected.

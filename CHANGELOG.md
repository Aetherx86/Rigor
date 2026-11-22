# Changelog

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
- Browser build in `web/` (the live demo on aetherx86.github.io/rigor).
- Mutation-testing harness in `tools/mutation/`.

### Verified
- Lean v4.36.0-rc1 `Init` (58,546 declarations) in 7.8 s / 478 MB and `Std` (96,626) in
  11.9 s / 696 MB, against `leanchecker --fresh` at 28.7 s / 547 MB and 44.2 s / 928 MB.
- 1,482 mutants over four rounds; every meaning-changing mutant rejected.

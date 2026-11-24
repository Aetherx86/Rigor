# Rigor

An independent proof checker for Lean 4, written in safe Rust. Rigor reads the `lean4export`
NDJSON export of a Lean library and re-checks every declaration with its own small kernel
(the Calculus of Inductive Constructions as Lean implements it). A proof is trusted only when
this second kernel agrees with Lean's.

Live demo: <https://aetherx86.github.io/rigor/> runs the same kernel, compiled to WebAssembly, on
Lean's `Init.Prelude` in the browser, and shows it rejecting a tampered proof.

## Results

Lean v4.36.0-rc1 exports on an Apple M4 MacBook Air (10 cores), peak memory from `/usr/bin/time -l`:

| Library | Declarations | `leanchecker --fresh` | Rigor, parallel | Rigor, one thread |
| :--- | ---: | ---: | ---: | ---: |
| `Init` | 58,546 | 28.7 s, 547 MB | 7.3–8.6 s, 355 MB | 25.1–29.1 s, 347 MB |
| `Std` | 96,626 | 44.2 s, 928 MB | 11.1–12.6 s, 547 MB | 44.9 s, 567 MB |

Rigor's times include parsing the NDJSON export (332 MiB for `Init`, 532 MiB for `Std`);
`leanchecker` reads compiled `.olean` files. Details and history: [BENCHMARKS.md](BENCHMARKS.md).

## What the kernel checks

- Universe levels with impredicative `Prop`, universe polymorphism and parameter checks.
- Inductive types, including mutual and nested ones: strict positivity, universe bounds,
  large-elimination rules (a field must be one of the result indices, as in Lean), and
  recursors that Rigor generates itself rather than reading from the export.
- Definitional equality: beta, delta (height-ordered, lazy), zeta, iota, K-like reduction,
  quotients, projections, proof irrelevance, eta for functions and structures, unit-like types,
  `Nat` literals with Lean's arithmetic extensions (big integers), string literals, the
  `Bool.true` reflection fast path and `eagerReduce`, following Lean's `type_checker.cpp`.

## Design

- `crates/kernel` is the trusted part: about 2,700 lines with `#![forbid(unsafe_code)]` and no
  third-party crates. Expressions are hash-consed into 16-byte nodes in an arena; batched binder
  telescopes and coprime-stride work dispatch let worker threads check independent declarations in
  parallel against a shared read-only arena with low peak memory.
- `crates/parser` reads `lean4export` 3.x NDJSON and the older text format with defensive parser
  limits (`ParseLimits`), admits declarations through the kernel, and provides post-verification
  transitive axiom auditing (`audit`) and bounded pretty-printing (`pretty`) outside the TCB.
- `crates/bench` is the command-line checker, axiom auditor, inspector, and benchmark suite
  (`rigor-bench`).
- `web/` builds the browser module (`wasm-bindgen`, single-threaded) exporting `check(input)`,
  `audit(input, decl_name)`, and `version()`.
- `tools/mutation/` corrupts exports on purpose and re-checks them. Over nine rounds and 1,636
  mutants (swapped proofs, universe changes, broken definitions, altered inductive types), every
  mutant that changes meaning was rejected; the few accepted ones are provably harmless and are
  explained in `tools/mutation/REPORT.md`.

## Usage

```sh
cargo test --workspace
cargo build --release -p rigor-bench

# Verify exports (parallel by default, or sequential / bounded thread count)
./target/release/rigor-bench --check Init.ndjson
./target/release/rigor-bench --check Init.ndjson --sequential
./target/release/rigor-bench --check Init.ndjson --threads 4 --json
RIGOR_TRACE=1000 ./target/release/rigor-bench --check Std.ndjson   # report declarations over 1 s

# Verify and audit transitive axiom footprints (equivalent to #print axioms)
./target/release/rigor-bench --audit Std.ndjson --forbid-sorry \
  --allow-axioms propext,Quot.sound,Classical.choice
./target/release/rigor-bench --audit Init.Prelude.ndjson --decl Eq.symm --json

# Verify and inspect a single declaration (kind, type, direct dependencies, axioms)
./target/release/rigor-bench --inspect Init.Prelude.ndjson Eq.symm
```

### Browser / WebAssembly build

```sh
cargo build --release --target wasm32-unknown-unknown --manifest-path web/Cargo.toml
```

WASM exports:
- `check(input: &str) -> String`: verifies an export and returns JSON with counts or a formatted error.
- `audit(input: &str, decl_name: &str) -> String`: verifies and audits the full environment (empty `decl_name`) or one declaration's transitive axiom footprint.
- `version() -> String`: returns the Rigor package version (`0.2.0`).

Exports come from [lean4export](https://github.com/leanprover/lean4export):
`lake env lean4export Init > Init.ndjson`.

## License

MIT, see [LICENSE](LICENSE).

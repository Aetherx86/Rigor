# Rigor

A mathematically sound, high-performance dependent type theory proof kernel (Calculus of Inductive Constructions, Lean 4 `lean4export`-compatible) written in pure, safe Rust.

## Design Principles

1. **Small Trusted Computing Base (De Bruijn Criterion):** The entire proof kernel lives in `crates/kernel` with `#![forbid(unsafe_code)]`, zero third-party dependencies, and a target budget under 2,500 lines of auditable Rust.
2. **Logical Soundness:** Predicative universe hierarchy (`Prop : Type 0 : Type 1 ...`) with impredicative `Prop` (`imax`), universe polymorphism, strict positivity checking, predicative inductive universe bounds, Subsingleton large-elimination guards (including on `Proj`), quotient primitives (`Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind`), and definitional equality (beta, delta, iota, K-like, zeta, quotient, `Nat` literals, proof irrelevance in `Prop`, function and structure eta).
3. **Performance Architecture:**
   - **Flat Hash-Consed DAG Arenas:** `Name`, `Level`, and `Expr` are interned in contiguous `u32`-indexed arenas with $O(1)$ structural equality and precomputed `loose_bvar_range` / flag metadata.
   - **Two-Tier Lock-Free Scratch Arenas:** Global declarations live in an immutable `Arc<Arena>`; worker threads type-check independent declarations in parallel using isolated thread-local scratch arenas with zero locking and $O(1)$ teardown.
   - **Spine-Based WHNF & DAG Memoization:** Arguments are accumulated on an explicit spine to perform batched multi-substitution, paired with height-ordered delta unfolding and per-check WHNF/DefEq/type caches.

## Workspace Layout

- `crates/kernel`: The Trusted Computing Base (`#![forbid(unsafe_code)]`, zero third-party deps, < 2,500 SLOC): arena, universe levels, expressions, environment, inductive validator, reducer/def-eq, bidirectional type checker.
- `crates/parser`: Streaming zero-copy-token `lean4export` format parser supporting all 22 directives (`#NS`, `#NI`, `#US`, `#UM`, `#UIM`, `#UP`, `#EV`, `#ES`, `#EC`, `#EA`, `#EL`, `#EP`, `#EZ`, `#EJ`, `#ELN`, `#ELS`, `#AX`, `#DEF`, `#THM`, `#OPAQ`, `#QUOT`, `#IND`), plus mutual `#INDM` and v3 `#IND`/`#CTOR`/`#REC`.
- `crates/bench`: Micro-benchmarks and head-to-head `lean4checker` harness.

## Build and Test

```sh
cargo test --workspace
cargo run --release -p rigor-bench
```

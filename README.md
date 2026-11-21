# Rigor

A mathematically sound, high-performance dependent type theory proof kernel (Calculus of Inductive Constructions, Lean 4 `lean4export`-compatible) written in pure, safe Rust.

## Design Principles

1. **Small Trusted Computing Base (De Bruijn Criterion):** The entire proof kernel lives in `crates/kernel` with `#![forbid(unsafe_code)]`, zero third-party dependencies, and a target budget under 2,500 lines of auditable Rust.
2. **Logical Soundness:** Predicative universe hierarchy (`Prop : Type 0 : Type 1 ...`) with impredicative `Prop` (`imax`), universe polymorphism, definitional equality (beta, delta, zeta, proof irrelevance in `Prop`, function eta), and (in Phase 2) strict positivity and structural recursors.
3. **Performance Architecture:**
   - **Flat Hash-Consed DAG Arenas:** `Name`, `Level`, and `Expr` are interned in contiguous `u32`-indexed arenas with $O(1)$ structural equality and precomputed `loose_bvar_range` / flag metadata.
   - **Two-Tier Lock-Free Scratch Arenas:** Global declarations live in an immutable `Arc<Arena>`; worker threads type-check independent declarations in parallel using isolated thread-local scratch arenas with zero locking and $O(1)$ teardown.
   - **Spine-Based WHNF & DAG Memoization:** Arguments are accumulated on an explicit spine to perform batched multi-substitution, paired with height-ordered delta unfolding and per-check WHNF/DefEq/type caches.

## Workspace Layout

- `crates/kernel`: The Trusted Computing Base (arena, universe levels, expressions, environment, reducer/def-eq, bidirectional type checker).
- `crates/parser`: Streaming `lean4export` format parser (Phase 3).
- `crates/bench`: Micro-benchmarks and head-to-head `lean4checker` harness (Phases 1 and 4).

## Build and Test

```sh
cargo test --workspace
cargo run --release -p rigor-bench
```

# Rigor Kernel TCB SLOC Reduction Plan

## Baseline Measurement

Measured with:

```sh
cd ~/rigor
for f in crates/kernel/src/*.rs; do awk '/#\[cfg\(test\)\]/{exit} {print}' "$f"; done | grep -vE '^\s*(//|$)' | wc -l
```

Current TCB size: **3,155 SLOC** (`#![forbid(unsafe_code)]`, zero third-party dependencies).
Target budget: **< 2,500 SLOC** (minimum reduction required: **656 SLOC**).

| File | Current SLOC | Planned Reduction | Projected SLOC |
|---|---:|---:|---:|
| `crates/kernel/src/inductive.rs` | 641 | -150 | 491 |
| `crates/kernel/src/reduce.rs` | 595 | -105 | 490 |
| `crates/kernel/src/arena.rs` | 517 | -164 | 353 |
| `crates/kernel/src/env.rs` | 382 | -118 | 264 |
| `crates/kernel/src/check.rs` | 316 | -30 | 286 |
| `crates/kernel/src/nat.rs` | 253 | -99 | 154 |
| `crates/kernel/src/expr.rs` | 185 | -35 | 150 |
| `crates/kernel/src/level.rs` | 139 | -1 | 138 |
| `crates/kernel/src/hash.rs` | 56 | -24 | 32 |
| `crates/kernel/src/error.rs` | 46 | -23 | 23 |
| `crates/kernel/src/lib.rs` | 25 | -4 | 21 |
| **Total** | **3,155** | **-753** | **2,402** |

(Totals below sum to **773 SLOC** including the optional `BinderInfo`/binder-name cleanup on `ExprData`; core low-risk items alone yield **753 SLOC**, reaching **2,402 SLOC** with 98 SLOC of headroom below 2,500.)

---

## 1. Dead, Unused, or Test-Only Code

Every item below was verified via `grep` across `crates/`.

### 1.1 Move `Nat::to_dec` into `#[cfg(test)]`
- **Location:** `crates/kernel/src/nat.rs:82-106`
- **Estimated SLOC saved:** 25
- **Risk:** Low. `grep` confirms `to_dec` is called only inside `nat.rs`'s unit test module (`lines 295, 305, 325, 336`). Moving it into `#[cfg(test)] mod tests` removes 25 SLOC from production TCB with zero API impact outside tests.

### 1.2 Remove unused `KernelError::Unsupported`, `Environment::deferred_len`, `Environment::is_empty`, `Arena::lvl_zero`
- **Location:** `crates/kernel/src/error.rs:24, 47`; `crates/kernel/src/env.rs:126, 314`; `crates/kernel/src/level.rs:10`
- **Estimated SLOC saved:** 5
- **Risk:** Low. Zero production callers anywhere in `crates/` (`lvl_zero` has 3 test-only call sites that can use `Arena::LEVEL_ZERO` directly).

### 1.3 Remove dead `LocalDecl` / `InductiveInfo` / `ConstructorInfo` fields
- **Location:** `crates/kernel/src/check.rs:11-19, 69-77`; `crates/kernel/src/env.rs:23, 29`; `crates/kernel/src/inductive.rs:193, 346, 405, 439, 525, 528-535`
- **Estimated SLOC saved:** 20
- **Risk:** Low. `LocalDecl::name` and `LocalDecl::binder_info` are already marked `#[allow(dead_code)]` and never read; removing them simplifies `push_local`/`push_existing_local` call sites across `check.rs`, `reduce.rs`, and `inductive.rs`. `InductiveInfo::is_reflexive` and `ConstructorInfo::ctor_idx` are written in `inductive.rs` and never read anywhere in `crates/`.

---

## 2. Benchmark-Only & Non-TCB Code to Move Out of `crates/kernel`

### 2.1 Move `FrozenEnv` and `check_batch_parallel` to `crates/bench`
- **Location:** `crates/kernel/src/env.rs:376-445`; `crates/kernel/src/lib.rs:22`
- **Estimated SLOC saved:** 65
- **Risk:** Low. `grep` confirms `FrozenEnv` and `check_batch_parallel` are only used by the synthetic micro-benchmark (`crates/bench/src/main.rs:938, 946`) and one unit test (`crates/kernel/tests/phase1.rs:505`). Real parallel verification uses `Environment::check_deferred`. Moving the batch harness into `crates/bench` (using `Arena::child` + `TypeChecker`, or testing `check_deferred` in `phase1.rs`) removes redundant thread-spawning code from the TCB without touching production checking.

### 2.2 Move `Nat::from_dec` to `crates/parser`
- **Location:** `crates/kernel/src/nat.rs:56-80`
- **Estimated SLOC saved:** 24 (net ~21 after adding a 3-line `Nat::from_limbs(Vec<u64>)` constructor)
- **Risk:** Low. `grep` confirms `from_dec` is called only by `crates/parser/src/lib.rs:402` and `crates/parser/src/ndjson.rs:413` (plus `nat.rs` unit tests). Decimal string parsing is an untrusted front-end concern; arbitrary-precision limb arithmetic (`add`, `sub`, `mul`, `divmod`, `gcd`, `pow`, `bitwise`, `shl`, `shr`, `log2`) remains inside the TCB.

### 2.3 Move `Arena::format_name` to `crates/parser`
- **Location:** `crates/kernel/src/arena.rs:222-230`
- **Estimated SLOC saved:** 9
- **Risk:** Low. `grep` confirms `format_name` is called only once, in `crates/parser/src/lib.rs:761`, solely to format an error message. `Arena::get_name` is already public, so `crates/parser` can format names itself.

### 2.4 Simplify `KernelError::Display`
- **Location:** `crates/kernel/src/error.rs:27-50`
- **Estimated SLOC saved:** 21
- **Risk:** Low. `KernelError` already derives `Debug` with descriptive variant and field names; replacing the 24-line hand-written `match` in `Display` with `write!(f, "{self:?}")` (or moving human-friendly formatting to `crates/parser`) preserves all diagnostic information (and `crates/parser` tests match on enum variants, not display text).

### 2.5 Optional (not counted in 753 core total): Extract `check_deferred` thread-pool scheduler
- **Location:** `crates/kernel/src/env.rs:339-374`
- **Estimated SLOC saved:** ~35
- **Risk:** Medium. Keep `set_deferred_checking` and `require_known_consts` inside the kernel so self-reference/forward-reference invariants remain enforced by the TCB, and expose a `check_one_deferred(&self, i)` or move only the worker-pool loop to a driver crate if further headroom is ever needed. Caution: splitting admission from checking across crates requires careful API design so callers cannot inspect an unchecked `Environment`.

---

## 3. Duplicated Logic to Merge

### 3.1 Deduplicate `inductive.rs` (`replace_expr`, telescope peeling, `wrap_binders`, recursor builders)
- **Location:** `crates/kernel/src/inductive.rs:52-105, 117-121, 138-195, 206-352, 369-422, 521-621`
- **Estimated SLOC saved:** 145
- **Risk:** Low-medium (touches inductive validator; verify against full soundness torture suite and full `Init.ndjson`).
  - Replace `replace_expr` (`lines 73-105`, 33 SLOC) with a 3-line wrapper around `pub(crate) fn expr::map_children` (**-30 SLOC**).
  - Merge `wrap_pis` (`52-58`) and `wrap_lams` (`60-66`) into one `wrap_binders(arena, binders, body, is_pi)` (**-6 SLOC**).
  - Factor the 5 repeated `whnf` + `Pi`-peeling / argument-instantiation loops (`144-161`, `207-225`, `268-289`, `371-401`, `412-422`) into two small helpers: `peel_pis(tc, expr, limit)` and `inst_pis(tc, expr, args)` (**-65 SLOC**).
  - Deduplicate `InductiveInfo` construction (`189-195`, `342-347`, `521-526`), `major_ty` construction (`548-555`, `584-591`), and `check_unique_params` (`117-121` duplicates `check.rs:342-349`) (**-44 SLOC**).

### 3.2 Replace 4 duplicated intern tables in `arena.rs` with a generic `Table<T>`
- **Location:** `crates/kernel/src/arena.rs:90-316, 522-558`
- **Estimated SLOC saved:** 120
- **Risk:** Low. `names`/`name_map`/`name_base`, `levels`/`level_map`/`level_base`, `level_lists`/`level_list_map`/`level_list_base`, and `lits`/`lit_map`/`lit_base` repeat identical `lookup`, `intern`, `get`, `len`, `shrink_to_fit`, and `truncate_to` logic four times. A private generic `Table<T>` monomorphizes to the same machine code with zero runtime overhead and cuts ~120 SLOC.

### 3.3 Deduplicate `reduce.rs` helpers (`inst_levels`, `try_reduce_nat`, `as_structure_type`, `expand_lit`, `Pi`/`Lam`)
- **Location:** `crates/kernel/src/reduce.rs:14-42, 165-177, 199-219, 365-436, 489-529, 590-628`
- **Estimated SLOC saved:** 90
- **Risk:** Low.
  - Unify `inst_levels_cached` / `inst_levels_list` (`14-42`) and the duplicated 1-param/multi-param level dispatch in `reduce.rs:165-177` and `check.rs:148-156` (**-28 SLOC**).
  - Remove the redundant two-pass `op: &'static str` string-to-string remapping table in `try_reduce_nat` (`373-435`) and reuse cached `nat_zero` instead of nested `NameData::Str` matching (`387-393`) (**-25 SLOC**).
  - Extract `as_structure_type(&mut self, e)` shared across `to_ctor_when_structure` (`199-219`), `try_unit_like` (`590-605`), and `try_struct_eta` (`607-628`) (**-20 SLOC**).
  - Merge duplicate `(Lit, _)` / `(_, Lit)` arms (`489-502`) via `expand_lit`, and share binder-opening between `Pi`/`Pi` and `Lam`/`Lam` (`503-529`) (**-17 SLOC**).

### 3.4 Unify 6 duplicated `ExprData` DAG traversals via `expr::visit_expr_dag`
- **Location:** `crates/kernel/src/expr.rs:135-202`; `crates/kernel/src/env.rs:129-152, 316-334`; `crates/kernel/src/reduce.rs:344-363`
- **Estimated SLOC saved:** 65
- **Risk:** Low. `mentions_rec`, `mentions_fvar_rec`, `check_lvl_rec`, `require_known_consts`, `has_opaque_fvar`, and `max_height_rec` all implement the same visited-set `ExprData` child walk. A single `visit_expr_dag` (with short-circuit + prune predicate so `has_fvar`/`has_level_param` O(1) skips are preserved) removes ~65 SLOC across `expr.rs`, `env.rs`, and `reduce.rs`.

### 3.5 Merge `Arena::app` into `intern_expr` and share `Arena::new` / `Arena::child` init
- **Location:** `crates/kernel/src/arena.rs:124-184, 386-400, 475-486`
- **Estimated SLOC saved:** 35
- **Risk:** Low. Since `app_map` was replaced by the unified `expr_table`, `Arena::app` (`475-486`) duplicates `intern_expr` (`392-399`) verbatim. Removing the duplicate body and factoring a common `Arena::with_bases` helper shared by `new` and `child` removes ~35 SLOC with no performance regression (`#[inline]` keeps the `App` fast path identical).

### 3.6 Merge duplicated arms in `check.rs` (`check_decl` and `Literal` typing)
- **Location:** `crates/kernel/src/check.rs:221-238, 318-337`
- **Estimated SLOC saved:** 20
- **Risk:** Low. `Definition | Opaque` and `Theorem` share identical value checking; `Literal::Nat` and `Literal::Str` share identical constant lookup.

---

## 4. Compact Formatting & Low-Risk Boilerplate Reductions

### 4.1 Compact `nat.rs` trivial methods (keeping full arbitrary-precision arithmetic trusted)
- **Location:** `crates/kernel/src/nat.rs:13-55, 186-282`
- **Estimated SLOC saved:** 50
- **Risk:** Low. Single-expression methods (`zero`, `from_u128`, `is_zero`, `div`, `rem`, `land`, `lor`, `xor`, `log2`, `PartialOrd`, `Ord`, short guards) currently expand across 3–5 lines each.

### 4.2 Compact `env.rs::add_quot` expression builder
- **Location:** `crates/kernel/src/env.rs:205-305`
- **Estimated SLOC saved:** 30
- **Risk:** Low. Local closures for `pi`/`app` remove 25 repetitive `self.arena.pi(Arena::ANONYMOUS, ...)` boilerplate lines while preserving exact de Bruijn indices and self-checking rollback.

### 4.3 Compact `hash.rs` `Hasher` forwarding methods
- **Location:** `crates/kernel/src/hash.rs:20-64`
- **Estimated SLOC saved:** 24
- **Risk:** Low. Same `FxHasher` algorithm and bit-for-bit identical hashes; removes vertical expansion on 1-line `write_*` / `finish` methods.

### 4.4 Optional: Drop unused `name` and `BinderInfo` from `ExprData::Lam` and `ExprData::Pi`
- **Location:** `crates/kernel/src/arena.rs:41-47, 62-63, 492-498`; `crates/kernel/src/check.rs:178-201`; `crates/kernel/src/reduce.rs:503-537, 572-586`; `crates/kernel/src/inductive.rs:29, 52-66`
- **Estimated SLOC saved:** ~25 (beyond 1.3 above)
- **Risk:** Low-medium. Neither binder `name` nor `BinderInfo` affects CIC typing or definitional equality (`ExprData::Let` already dropped `name` in Task A). Dropping them from `Lam`/`Pi` (while keeping ignored parameters on `Arena::lam`/`Arena::pi` for API compatibility) also improves hash-consing hit rate across alpha-equivalent binders.

---

## 5. Recommended Execution Order

1. **Wave 1 (Pure deletions & non-TCB moves, zero logic changes — ~169 SLOC):** Items 1.1, 1.2, 1.3, 2.1, 2.2, 2.3, 2.4 -> **~2,986 SLOC**.
2. **Wave 2 (Mechanical deduplication in `arena.rs`, `expr.rs`, `check.rs`, `reduce.rs` — ~330 SLOC):** Items 3.2, 3.3, 3.4, 3.5, 3.6 -> **~2,656 SLOC**.
3. **Wave 3 (`inductive.rs` deduplication + compact `nat.rs`/`add_quot`/`hash.rs` — ~254 SLOC):** Items 3.1, 4.1, 4.2, 4.3 -> **~2,402 SLOC** (under 2,500 SLOC target with ~98 SLOC margin).
4. **Verification Gate (after each wave):** `cargo test -q --workspace`, full `Init.ndjson` `CHECK_OK` in both parallel and sequential mode, plus re-running `tools/mutation/mutate.py` to confirm zero soundness regressions and no memory/speed regression.

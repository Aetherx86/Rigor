# Rigor Per-Thread Scratch Memory Analysis and Bounding Plan

## 1. Observed Memory Baseline

Measurements on Apple M4 (10 cores, macOS, `/usr/bin/time -l`) verifying full Lean 4 v4.36.0-rc1 `Init` (58,546 declarations, 6,495,289 NDJSON lines, 6,311,599 arena expressions):

| Configuration | Pre-Task A (`ExprData` 24 B) | Post-Task A (`ExprData` 16 B) | Delta vs Sequential |
|---|---:|---:|---:|
| Sequential (`RIGOR_SEQUENTIAL=1`) | 502 MB | 377 MB | baseline |
| Parallel, 1 worker (`RIGOR_THREADS=1`) | 566 MB | — | +64 MB (pre-Task A) |
| Parallel, 10 workers (default) | ~712 MB | 445 MB | +210 MB pre-A (~15 MB/worker); +68 MB post-A (~7 MB/worker) |
| `leanchecker --fresh Init` (reference) | 550 MB | 547 MB | — |

Why parallel `check_deferred` adds ~7–15 MB peak RSS per worker thread (and more on larger libraries such as `Std`):

1. **Simultaneous peak concurrency of heavy declarations** (`crates/kernel/src/env.rs:349-368`): in sequential mode (`add_decl`, `env.rs:176-188`), only one declaration's scratch expressions and `TypeChecker` caches exist at a time. In parallel mode, up to `n_threads` workers simultaneously hold a live `Arena::child` plus a live `TypeChecker` with unbounded caches. Worse, `next.fetch_add(1)` hands out indices in admission (module) order, and heavy `Init` proofs are tightly clustered by module (`Array.Extract` lines 363k–505k, `Iterators`/`String.ForwardSearcher` lines 1.86M–2.62M, `Vector.Extract` lines 4.44M–6.17M), so multiple workers hit 10k–27k-node proofs simultaneously.
2. **Per-declaration heap churn and macOS `libmalloc` magazine retention**: `check_deferred` (`env.rs:359-360`) constructs and drops a brand-new `Arena::child` (12 containers) and `TypeChecker` (7 containers) on every one of the 57,937 deferred declarations (~1.1M container alloc/free cycles). On macOS, per-CPU `libmalloc` magazines retain freed slabs near each thread's historical high-water mark rather than immediately returning every page to the OS.
3. **Per-thread demand-paged stacks**: each worker reserves a 1 GiB stack (`env.rs:353`), committing physical pages up to its maximum recursion depth (typically 0.5–2 MB per worker) that stay resident until thread exit.

---

## 2. Inventory of Per-Declaration Structures and Growth Profiles

Exact sizes assume 64-bit ARM64 (`ExprId`/`NameId`/`LevelId`/`LevelListId`/`LitId`/`FVarId` = 4 B; Rust `std::collections::HashMap`/`HashSet` uses `hashbrown` SwissTable: 1 control byte/bucket, power-of-2 table, max load 7/8, so effective bytes per live entry range from `1.14x` right before resize to `2.28x` right after doubling).

### 2.1 Child `Arena` Tables (`crates/kernel/src/arena.rs:89-184`)

| Field | Element / Bucket Size | Effective Cost | Growth Behavior for a Heavy Declaration |
|---|---:|---:|---|
| `exprs: Vec<ExprData>` | 16 B | 16–32 B/expr | **Primary consumer.** Strictly append-only for the entire `check_decl`; every intermediate `App`, `Pi`, `Lam`, `Let`, `Proj`, `Lit`, and `instantiate1` copy stays live until `check_decl` returns. |
| `expr_meta: Vec<ExprMeta>` | 8 B (`u32`+`u8`+3 B pad) | 8–16 B/expr | Mirrors `exprs` 1:1. |
| `expr_table: Vec<u32>` | 4 B/slot (75% max load, min 1024 slots = 4 KiB) | 5.3–10.7 B/expr | Open-addressed hash-consing table over child `exprs`. |
| `lits: Vec<Literal>` + `lit_map` | `Literal` = 32 B (`Nat` `Vec<u64>` + tag, or `Box<str>`) | ~70–130 B/lit + heap limbs | Usually empty; can grow during `Nat` arithmetic / `decide +kernel` / `omega` / `String` expansion (`reduce.rs:320-334, 451-519`). |
| `levels` / `level_meta` / `level_map` | 12 B + 1 B + map | ~30–60 B/level | Small (typically < 100 entries/decl). |
| `level_lists` / `level_list_map` | `Box<[LevelId]>` (16 B + heap) × 2 | ~60–100 B/list | Small (typically < 200 entries/decl). |
| `names` / `name_map` | `NameData` (24 B + heap `str`) × 2 | ~70–120 B/name | Normally 0 entries (names already exist in parent `Arena`). |

**Combined child-arena cost:** **~29.3–58.7 B/expr** (typical average **~40 B/expr**).

#### Root cause of child-arena explosion: single-binder telescope instantiation (`check.rs:192-234`, `reduce.rs:613-639`)

In `Init.ndjson`, the heaviest declarations have 10k–27.7k-node proof DAGs wrapped in deep `Lam`/`Let` telescopes:

| Heavy `Init.ndjson` Declaration | `Ty` DAG | `Val` DAG | `App`s | `Lam`s | `Let`s | Leading `Lam` Run |
|---|---:|---:|---:|---:|---:|---:|
| `...ForwardSliceSearcher.Invariants.isValidSearchFrom_toList` | 109 | 27,696 | 23,926 | 2,704 | 424 | 12 |
| `...Array.extract_append._proof_1_1` | 68 | 26,764 | 26,374 | 267 | 0 | 6 |
| `...Vector.extract_append._proof_1` | 94 | 26,954 | 26,568 | 266 | 0 | 5 |
| `...Vector.extract_extract._proof_1` | 80 | 26,504 | 26,158 | 226 | 0 | 6 |
| `...toList_filterMapWithPostcondition_filterMapWithPostcondition'` | 326 | 16,017 | 13,914 | 1,406 | 0 | **24** |
| `...Rxc.Iterator.instIteratorLoop.loopWf_eq._unary` | 663 | 12,210 | 10,890 | 913 | 0 | **18** |
| `Std.IterM.toList_filterMapM_map` | 240 | 9,828 | 8,876 | 702 | 1 | **19** |

Because `check.rs:192-234` peels **one binder at a time** and calls `instantiate1(self.arena, body, fv_expr)` on every binder (and `abstract_fvars(self.arena, body_ty, &[fv])` one `FVar` at a time on return), a leading telescope of `k` binders over an `M`-node body rewrites and interns the remaining body `k` times (`O(k * M)`):

- `toList_filterMapWithPostcondition...` (`k = 24`, `M = 16,017`): up to **~384,000 temporary `ExprData` nodes** (~15 MB in `scratch` alone) just from the leading telescope.
- `isValidSearchFrom_toList` (`k = 12`, `M = 27,696`, plus 2,704 inner `Lam`s and 424 `Let`s): **~300,000+ temporary `ExprData` nodes** (~12 MB in `scratch`).
- Similarly, `check.rs:163-191` (`App` in both full and `infer_only` mode) calls `instantiate1(self.arena, body, a)` once per argument instead of batching multi-argument spines in `infer_only` mode (`type_checker.cpp:188-205`).

### 2.2 `TypeChecker` Caches and Scratch State (`crates/kernel/src/check.rs:22-46`, `reduce.rs`)

| Field | Entry Layout (KV + ctrl) | Effective Bytes/Entry | Growth Risk & Specific Issues |
|---|---:|---:|---|
| `whnf_cache: FxHashMap<ExprId, ExprId>` | 8 + 1 = 9 B | 10.3–18.3 B | **High.** `reduce.rs:45-52` caches *every* call, including already-WHNF `Sort`, `Pi`, `Lam`, `Lit`, `BVar`, non-let `FVar`, and non-delta `Const` (tens of thousands of useless `(e, e)` entries per heavy decl). Also retains entries containing dead ephemeral `FVar`s after `pop_local()`. |
| `infer_cache: FxHashMap<ExprId, ExprId>` | 8 + 1 = 9 B | 10.3–18.3 B | **High.** Caches every checked node including trivial O(1) leaves (`Sort`, `FVar`, `Lit`) and every intermediate `ExprId` created by single-binder `instantiate1`. Dead after `infer_type(val)` finishes (useless in Phase 3 `is_def_eq(val_ty, ty)`). |
| `infer_only_cache: FxHashMap<ExprId, ExprId>` | 8 + 1 = 9 B | 10.3–18.3 B | **Medium.** Stores types of reduction/def-eq intermediate terms (`is_proof`, `try_fun_eta`, `try_struct_eta`, `try_unit_like`, K-like `Eq.rec`, WHNF struct eta). Unbounded; contains ephemeral-`FVar` entries. |
| `def_eq_cache: FxHashSet<(ExprId, ExprId)>` | 8 + 1 = 9 B | 10.3–18.3 B | **Medium–High.** Caches every equal pair globally (`reduce.rs:552, 585`), including ephemeral-`FVar` sub-comparisons from `Pi`/`Lam`/`try_fun_eta` that become unreachable once `pop_local()` runs. |
| `def_neq_cache: FxHashSet<(ExprId, ExprId)>` | 8 + 1 = 9 B | 10.3–18.3 B | **Medium–High.** Caches *every* failing `is_def_eq` call globally (`reduce.rs:553, 585`), much broader than Lean's `m_failure` (which only caches same-regular-def congruence failures). Accumulates dead ephemeral-`FVar` pairs and speculative eta/K-like probes. |
| `inst_lvl1_cache: FxHashMap<(ExprId, LevelId), ExprId>` | 12 + 1 = 13 B | 14.9–26.3 B | **Low.** Bounded by distinct `(1-param expr, level)` pairs touched in one declaration (typically < 2,000 entries = < 50 KB). |
| `locals: Vec<LocalDecl>` | 24 B/entry (`Option<ExprId>` = 8 B) | 768 B initial (`cap=32`) | **Negligible.** Bounded by binder nesting depth (< 200 entries = < 5 KB). |
| Transient `expr.rs::map_children` cache | `FxHashMap<(ExprId, u32), ExprId>` (13 B) | 14.9–26.3 B | **Medium (transient peak).** Allocated whenever substitution/abstraction exceeds `LAZY_CACHE_THRESHOLD = 12` (`expr.rs:8, 129`). On a 27k-node body, one live `instantiate1` call allocates ~0.5–0.8 MB transiently; nested recursive calls can stack. |
| Transient `reduce.rs::has_opaque_fvar` | `Vec<ExprId>` + `FxHashSet<ExprId>` | 5–10 B/visited node | **Low–Medium (transient churn).** Freshly allocated on every call when `has_fvar()` is set (`reduce.rs:432-433`). |

**Combined `TypeChecker` cache cost on a heavy declaration:** 50k–200k entries across the 5 main `ExprId` tables = **1.0–4.5 MB** (up to **~6 MB** immediately after power-of-2 rehashes), on top of **6–16 MB** in `scratch` (`Arena::child`), matching the observed ~7–15 MB per concurrent heavy worker.

### 2.3 Secondary Shared-Arena Opportunity (`arena.rs:522-539`)

`Arena::shrink_for_sharing()` calls `shrink_to_fit()` on all `Vec`s and repacks `expr_table`, but does **not** shrink `name_map`, `level_map`, `level_list_map`, or `lit_map`. In `Init`, `name_map` holds 299,085 `NameData -> NameId` entries (~24–40 B/slot); post-doubling slack in `name_map` alone can leave **4–12 MB** of unused capacity permanently resident in the shared parent `Arena`.

---

## 3. How Lean 4 Bounds and Manages Equivalent Caches

Inspected from `~/rigor-data/lean-src/type_checker.cpp` (v4.36.0-rc1), `src/kernel/type_checker.h`, `src/kernel/environment.cpp`, `src/kernel/expr_maps.h`, and `src/util/alloc.h`:

1. **No hard numeric entry caps on `type_checker::state` caches:**
   - All 6 caches (`m_infer_type[2]`, `m_whnf_core`, `m_whnf`, `m_success`, `m_failure`, `m_unfold`) live on `type_checker::state` (`type_checker.h:22-45`) as `lean::unordered_map`/`unordered_set` (`expr_maps.h:14`, `alloc.h:25-38`).
   - There are **zero** `.clear()`, `.erase()`, or size-cap checks on any of these 6 maps inside `type_checker.cpp`.
   - Instead, `type_checker` is created fresh per declaration (`environment.cpp:135, 166, 171, 180, 195, 213`) and destroyed at declaration exit (`~type_checker()` at `type_checker.cpp:1217-1220`).
   - The only explicit memory bound in `type_checker.cpp` is `g_nat_max_size` (`LEAN_NAT_MAX_SIZE`, default **128 MB**, lines `35-36, 298-303, 621-622, 636-640, 653, 677`), capping computed `Nat` numeral sizes (analogous to Rigor's `MAX_BITS = 1 << 24` = 2 MB in `nat.rs`).
2. **Four mechanisms that keep Lean's per-declaration memory low without explicit cache caps:**
   - **Skip trivial cases before cache lookup/insert (`type_checker.cpp:469-484, 543-545, 569-578, 703-718`):**
     - `whnf` (`704-718`) returns immediately without touching `m_whnf` for `BVar`, `Sort`, `MVar`, `Pi`, `Lit`, `MData`, and non-let `FVar`.
     - `whnf_core` (`469-484, 543-545`) skips `m_whnf_core` for `BVar`, `Sort`, `MVar`, `Pi`, `Const`, `Lambda`, `Lit`, `MData`, non-let `FVar`, and whenever `cheap_rec || cheap_proj`.
     - `unfold_definition_core` (`569-578`) caches in `m_unfold` only when `length(us) > 0`.
   - **Batched telescope instantiation and abstraction (`type_checker.cpp:125-166, 208-230, 748-775`, `infer_app` `infer_only` `188-205`):**
     - `infer_lambda`, `infer_pi`, `infer_let`, and `is_def_eq_binding` peel all consecutive binders into a stack `buffer<expr> fvars` and call `instantiate_rev` once (and `m_lctx.mk_pi` once), avoiding Rigor's `O(k * M)` intermediate expression blowup.
     - `infer_app(..., infer_only = true)` batches the full `App` spine with `instantiate_rev`.
   - **Narrow `m_failure` scope (`type_checker.cpp:995-1008`):**
     - `m_failure` is inserted and queried at only one site: the same-regular-definition congruence shortcut in `lazy_delta_reduction_step`. It does not record every failing `is_def_eq` call globally.
   - **Ref-counted expression lifetime + `mimalloc` (`alloc.h:15-21`):**
     - Temporary expressions not retained by a cache are freed immediately mid-declaration, and `lean::allocator` uses `mimalloc` (aggressive cross-thread slab return), whereas Rigor's child `Arena` retains every temporary expression until `check_decl` ends and uses system `libmalloc`.

---

## 4. Concrete Optimization Plan (Ranked by Impact and Risk)

All changes below are **100% soundness-preserving** (none weaken any CIC check; cache eviction/skipping and arena reuse can never cause an invalid declaration to be accepted).

### Item 1: Batch `Lam`/`Pi`/`Let` Telescopes and `infer_only` `App` Spines (`check.rs:163-234`, `reduce.rs:613-639`)

- **What:** Match Lean's `infer_lambda`, `infer_pi`, `infer_let`, `is_def_eq_binding`, and `infer_app(infer_only)` using Rigor's existing slice-based `instantiate_rev(arena, body, &fvars)` and `abstract_fvars(arena, body_ty, &fvars)` (`expr.rs:16, 30`).
  - Peel consecutive `Lam` / `Pi` / `Let` binders in a `while` loop, instantiating each binder's domain (and `Let` value) against the accumulated `fvars` slice, checking each domain before pushing the local, and calling `instantiate_rev(body, &fvars)` **once** at the end of the telescope.
  - On return from `Lam`, call `abstract_fvars(arena, body_ty, &fvars)` once and wrap the `Pi`s inside-out. On return from `Let`, call `abstract_fvars` once and `instantiate_rev(abs, &vals)` once.
  - In `infer_app` when `self.infer_only`, collect the `App` spine and instantiate in batches via `instantiate_rev` (matching `type_checker.cpp:188-205`).
- **Expected savings:** **-25 to -45 MB peak RSS on 10-thread `Init`** (cuts temporary child-arena expressions by **5x–20x** on binder-heavy `Iterators`/`String`/`Array`/`Vector` proofs, and proportionally shrinks `infer_cache` and `whnf_cache` because those redundant intermediate `ExprId`s are never created). Also **improves wall time** (~5–15% faster checking).
- **TCB impact:** ~+25 SLOC in `check.rs`/`reduce.rs` (or net neutral once `Lam`/`Pi` loops share structure).
- **Risk:** **Low–Medium.** Must preserve exact binder scoping: check each domain `d_i` (and `Let` value `v_i`) before pushing `fv_i` into `self.locals`, and pop `fvars.len()` locals on both `Ok` and `Err` paths (exact same invariant as Lean `type_checker.cpp:134, 222`). Verify with full unit/soundness suite + `Init` + `Std`.

### Item 2: Reuse One Child `Arena` + One `TypeChecker` Per Worker with High-Water Reset (`env.rs:350-366`, `arena.rs`, `check.rs`)

- **What:** Hoist `let mut scratch = Arena::child(Arc::clone(arena));` and `let mut tc = TypeChecker::new(decls, &mut scratch);` (or reusable `TypeCheckerState` caches) **outside** the per-declaration `loop` in `check_deferred`, and add `Arena::reset_child(&mut self, max_expr_cap: usize)` + `TypeChecker::reset(&mut self, max_cache_cap: usize)`:
  - Between declarations:
    - Clear `locals`, reset `next_fvar = 0`, clear `nat_zero`/`nat_succ` (actually `nat_zero`/`nat_succ` stay valid if they live in the parent arena! Only drop them if `id.0 >= expr_base`).
    - Clear all 6 caches (`whnf_cache`, `infer_cache`, `infer_only_cache`, `def_eq_cache`, `def_neq_cache`, `inst_lvl1_cache`). If any map's `capacity() > max_cache_cap` (e.g. `16_384` entries ≈ 150–300 KB), replace it with `FxHashMap::default()` (releasing the oversized backing buffer back to the allocator immediately rather than pinning a peak allocation on that worker).
    - Clear `scratch`: `exprs.clear()`, `expr_meta.clear()`, `bvar_cache.fill(u32::MAX)`, clear the 4 small intern tables; if `exprs.capacity() > max_expr_cap` (e.g. `16_384` exprs ≈ 650 KB) or `expr_table.len() > 32_768`, drop and replace with empty `Vec::new()` (so an outlier heavy declaration never permanently pins a 10+ MB buffer per worker); otherwise `expr_table.fill(u32::MAX)` and `expr_table_len = 0` (O(cap) `memset` on a small <=128 KiB buffer, zero `malloc`/`free`!).
  - Also fix `FrozenEnv::check_batch_parallel` (`env.rs:426-436`) to call `scratch.reset_child(...)` per declaration (currently it leaks every scratch expr across the entire chunk).
- **Expected savings:** **-10 to -20 MB peak RSS on 10-thread `Init`** by eliminating ~1.1M `malloc`/`free` cycles and per-thread `libmalloc` magazine bloat, while ensuring post-outlier buffers are released promptly. Also reduces allocator lock contention across 10 threads (~3–8% faster wall time).
- **TCB impact:** ~+25 SLOC in `arena.rs`/`check.rs`/`env.rs`.
- **Risk:** **Low.** Because `next_fvar` resets to 0 and all caches + child arena tables are cleared between declarations, every declaration sees an observationally identical fresh state (parent `Arc<Arena>` is immutable). Just verify `nat_zero`/`nat_succ` are cleared if they were interned in the child rather than parent (simplest: always clear them to `None` — 2 lines, zero bug surface).

### Item 3: Filter Trivial Entries Out of `whnf_cache` and `infer_cache`, Plus Bounded Cache Caps (`reduce.rs:45-52`, `check.rs:95-107`)

- **What:**
  1. **Match Lean's `whnf` fast-return guard (`type_checker.cpp:703-718`) before `whnf_cache` lookup/insert (`reduce.rs:45-52`):**
     - Return `e` immediately (without hashing or inserting into `whnf_cache`) for `ExprData::Sort(_) | Pi { .. } | Lam { .. } | Lit(_) | BVar(_)`, non-let `FVar(fv)` (`self.local_value(*fv).is_none()`), and non-delta `Const` (`!matches!(decl, Definition { hint: Abbrev | Regular(_), .. } | Theorem { .. })`).
     - Eliminates ~60–80% of `whnf_cache` entries (all trivial `(e, e)` pairs) with **faster** lookups (no hash probe for `Pi`/`Sort`/`Lit`!).
  2. **Skip trivial O(1) leaves in `infer_cache` / `infer_only_cache` (`check.rs:95-107`):**
     - Do not insert `ExprData::Sort(_) | ExprData::FVar(_) | ExprData::Lit(_)` (or non-level-polymorphic `Const`) into `infer_cache`/`infer_only_cache` — computing them directly is a single match/array lookup, cheaper than a hash table insert, and shrinks `infer_cache` by ~15–25%.
  3. **Add generous high-water caps on non-DAG-critical caches (`whnf_cache`, `infer_only_cache`, `def_eq_cache`, `def_neq_cache`, `inst_lvl1_cache`):**
     - Cap each at e.g. `65_536` entries (~1.0 MB max each, ~5 MB hard ceiling per worker across all 5 caches combined). When `len() >= CAP`, call `.clear()` (or for `def_neq_cache`, stop inserting once `len() >= 65_536` — stopping insertion avoids a sudden performance cliff on a deep failing comparison while hard-bounding memory at ~1.0 MB!).
     - **Do NOT aggressively clear `infer_cache` mid-`infer_type`:** on a heavily shared proof DAG, clearing `infer_cache` mid-traversal can degrade `O(|V|)` checking to exponential `O(2^d)`. Instead, bound `infer_cache` indirectly via Item 1 (batched telescopes) + trivial-leaf skipping + Item 4 (clearing before Phase 3).
- **Expected savings:** **-8 to -18 MB peak RSS on 10-thread `Init`** (and prevents pathological 50+ MB spikes on heavy `Std`/`decide +kernel` proofs). Slight wall-time speedup from avoiding hash probes on `Sort`/`Pi`/`Lit`/`FVar`.
- **TCB impact:** ~+15 SLOC in `reduce.rs`/`check.rs`.
- **Risk:** **Low.** Stopping `def_neq_cache` insertion above 65k entries (rather than clearing) prevents any exponential re-exploration regression while guaranteeing bounded RSS. Only risk is setting caps too low (e.g. `< 16k`), which could slow down `decide`/`grind` proofs; `65_536` is well above normal `Init` declarations (~99.9% never hit it).

### Item 4: Clear `infer_cache` (and Ephemeral Caches) Between Phase 2 and Phase 3 of `check_decl` (`check.rs:332-352`)

- **What:** In `check_decl` for `Definition`/`Opaque`/`Theorem`, after `let val_ty = self.infer_type(*val)?;` returns and before `self.is_def_eq(val_ty, ty)?`:
  - Call `self.infer_cache.clear()` (and drop backing storage if `capacity() > 16_384`).
  - Optionally clear `whnf_cache` / `def_eq_cache` / `def_neq_cache` if they grew large (`> 16_384` entries) before Phase 3.
- **Expected savings:** **Small on `Init` (~0–5 MB)** because for most heavy `Init` theorems (`Array.Extract`, `Vector.Extract`, `ForwardSliceSearcher`), `TyDAG` is 60–326 nodes while `ValDAG` is 10k–27.7k nodes — so peak RSS occurs *during* Phase 2 (`infer_type(val)`), not Phase 3. However, for theorems with both a large proof body *and* an expensive final `is_def_eq(val_ty, ty)` (e.g. large `decide +kernel` / `rfl` / `grind` certificates in `Std`), this prevents Phase 2's dead `infer_cache` from stacking on top of Phase 3's reduction caches (**-2 to -8 MB** on such declarations).
- **Note on Phase 1 -> Phase 2:** Clearing between `infer_sort(ty)` and `infer_type(val)` is **not worthwhile** (`ty` is < 500 nodes on almost all declarations, saving only a few KB while discarding useful type entries).
- **TCB impact:** 3–5 SLOC in `check.rs`.
- **Risk:** **Very Low.** Purely discards dead memo entries; `val_ty` and `ty` are already computed `ExprId`s.

### Item 5: De-Cluster `check_deferred` Work Dispatch + Shrink Shared `Arena` Maps (`env.rs:346-365`, `arena.rs:522-539`)

- **What:**
  1. **De-cluster heavy modules in `check_deferred` (`env.rs:355`):** instead of dispatching `pending[i]` sequentially (`0, 1, 2, ...`), permute dispatch with a fixed coprime stride (e.g. `orig_idx = (k * stride) % n` where `stride` is coprime to `n`, e.g. finding the first odd `stride >= 1009` with `gcd(stride, n) == 1`). Keep `first_err` keyed by `orig_idx` so error reporting stays deterministic (earliest failing declaration in admission order). This spreads the `Array.Extract`, `Iterators`, and `Vector.Extract` clusters across time instead of feeding 10 heavy proofs to 10 workers simultaneously.
  2. **Shrink intern maps in `Arena::shrink_for_sharing()` (`arena.rs:522-539`):** add `.shrink_to_fit()` on `name_map`, `level_map`, `level_list_map`, and `lit_map` before wrapping `Arena` in `Arc`.
- **Expected savings:**
  - De-clustering: **-10 to -25 MB** reduction in instantaneous multi-worker overlap spikes on `Init` (and even larger on `Std`, where `Std.Time` / `Std.Sat` / `Std.Internal` proofs cluster heavily).
  - Shrinking `name_map` et al.: **-4 to -12 MB** directly off the shared base RSS in parallel mode (zero runtime cost during checking).
- **TCB impact:** ~+10 SLOC total.
- **Risk:** **Very Low.** Pure scheduling order change (no effect on checked declarations; `first_err` still returns the minimum admission index; remove the `if j < i { break; }` shortcut since `orig_idx` is no longer monotonic, or break only after error when needed — in the passing case `first_err` is always `None`).

---

## 5. Summary of Expected Total Savings (10-Thread `Init` Parallel Check)

| Priority | Change | Target | Est. Peak RSS Reduction (10T `Init`) | Wall-Time Impact | Risk |
|---:|---|---|---:|---|---|
| **1** | Batched `Lam`/`Pi`/`Let` telescopes + `infer_only` `App` spine (`check.rs`, `reduce.rs`) | Child `Arena` + `infer_cache` | **-25 to -45 MB** | Faster (~5–15%) | Low–Med |
| **2** | Reuse 1 child `Arena` + `TypeChecker` per worker with high-water reset (`env.rs`, `arena.rs`, `check.rs`) | Allocator churn / `libmalloc` retention | **-10 to -20 MB** | Faster (~3–8%) | Low |
| **3** | Skip trivial `whnf_cache`/`infer_cache` inserts + 65k cap on non-`infer_cache` maps (`reduce.rs`, `check.rs`) | `TypeChecker` caches | **-8 to -18 MB** | Slightly faster | Low |
| **4** | De-cluster `check_deferred` dispatch + `shrink_to_fit` parent intern maps (`env.rs`, `arena.rs`) | Multi-worker overlap + shared base | **-14 to -35 MB** | Neutral | Very Low |
| **5** | Clear `infer_cache` between Phase 2 and Phase 3 of `check_decl` (`check.rs`) | Phase-3 heavy decls (`Std` / `decide`) | **0–5 MB** (`Init`), **-2–8 MB** (`Std`) | Neutral | Very Low |

Because Items 1–3 overlap partially on the same heavy declarations (fewer telescope-generated `ExprId`s also mean smaller caches and smaller peak `Arena::child` buffers), realistic **combined** savings on 10-thread `Init` are **~45–65 MB**, bringing 10-thread parallel peak RSS from **445 MB** down to roughly **~380–400 MB** (within ~10–25 MB of the 377 MB sequential baseline, and ~150 MB below `leanchecker`'s 547 MB), while keeping memory tightly bounded on `Std` and larger libraries.

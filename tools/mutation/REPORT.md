# Rigor Soundness Mutation-Testing Report

## Command

```sh
RIGOR_THREADS=4 python3 /Users/sushikim/rigor/tools/mutation/mutate.py --input /tmp/rigor_real/Init.Prelude.ndjson --checker /Users/sushikim/rigor/target/release/rigor-bench --seed 1 --per-op 50 --workers 2 --report /Users/sushikim/rigor/tools/mutation/REPORT.md
```

## Sanity Check (Unmutated Input)

- Result: PASS (`CHECK_OK file=/tmp/rigor_real/Init.Prelude.ndjson decls=1840 env_decls=2121 lines=65406 mib=3.64 time_ms=45.97 decls_per_sec=40029 mib_per_sec=79.1 arena_exprs=67536`)
- Total elapsed time: 5.47 s

## Summary by Mutation Operator

| Operator | Total | Rejected | Accepted | Rejection Rate |
|---|---:|---:|---:|---:|
| `thm_value_swap` | 50 | 50 | 0 | 100.0% |
| `const_swap` | 50 | 50 | 0 | 100.0% |
| `arg_swap` | 50 | 50 | 0 | 100.0% |
| `level_change` | 50 | 50 | 0 | 100.0% |
| `def_body_rfl_break` | 50 | 49 | 1 | 98.0% |
| **Total** | **250** | **249** | **1** | **99.6%** |

## Operator 5 (`def_body_rfl_break`) Rejection Breakdown

- Rejected mutants: 49
- Rejected at a later dependent declaration (mutated definition remained well-typed and broke a downstream proof/rfl check): 7
- Rejected at the mutated definition line itself: 42

## Accepted Mutants

The following mutants were accepted by Rigor and require manual review to determine whether each mutation was semantically harmless (for example, proof irrelevance, unreachable branch, or definitionally equal replacement) or a genuine soundness bug:

- Mutant #242 (`def_body_rfl_break`): target `Lean.Name.brecOn.go` (line 25169) -- in def Lean.Name.brecOn.go (rfl deps: Lean.Name.brecOn.eq), same-type const swap Lean.Name.str -> Lean.Name.mkStr | output: `CHECK_OK file=/var/folders/4k/zxttxcf53d3616s6mvcsv_xc0000gn/T/rigor_mut_giwz57fg/mutant_0242.ndjson decls=1840 env_decls=2121 lines=65423 mib=3.64 time_ms=44.82 decls_per_sec=41051 mib_per_sec=81.1 arena_exprs=67551`

## Review of accepted mutants

- Mutant #242 is semantically harmless: `Lean.Name.mkStr` is `abbrev mkStr (p : Name) (s : String) : Name :=
  Name.str p s` (Init/Prelude.lean), so replacing the constructor `Lean.Name.str` by `Lean.Name.mkStr` yields a
  definitionally equal term (delta then eta). Accepting it is correct; Lean's kernel accepts it as well.
- Conclusion: every mutant that changes meaning (249 of 250) was rejected; no soundness bug found.

---

## Round 2A: Init.Core.ndjson (seed=2, 100 per operator)

### Command

```sh
RIGOR_THREADS=4 python3 /Users/sushikim/rigor/tools/mutation/mutate.py --input /tmp/rigor_real/Init.Core.ndjson --checker /Users/sushikim/rigor/target/release/rigor-bench --seed 2 --per-op 100 --workers 2 --report /Users/sushikim/rigor/tools/mutation/REPORT.md
```

### Sanity Check (Unmutated Input)

- Result: PASS (`CHECK_OK file=/tmp/rigor_real/Init.Core.ndjson decls=3480 env_decls=3913 lines=111781 mib=6.15 time_ms=90.73 decls_per_sec=38354 mib_per_sec=67.8 arena_exprs=115583`)
- Total elapsed time: 30.62 s

### Summary by Mutation Operator

| Operator | Total | Rejected | Accepted | Rejection Rate |
|---|---:|---:|---:|---:|
| `thm_value_swap` | 100 | 100 | 0 | 100.0% |
| `const_swap` | 100 | 100 | 0 | 100.0% |
| `arg_swap` | 100 | 100 | 0 | 100.0% |
| `level_change` | 100 | 100 | 0 | 100.0% |
| `def_body_rfl_break` | 100 | 100 | 0 | 100.0% |
| `inductive_mutation` | 100 | 97 | 3 | 97.0% |
| `level_arity_mismatch` | 100 | 100 | 0 | 100.0% |
| **Total** | **700** | **697** | **3** | **99.6%** |

### Operator 5 (`def_body_rfl_break`) Rejection Breakdown

- Rejected mutants: 100
- Rejected at a later dependent declaration: 7
- Rejected at the mutated declaration itself: 93

### Operator 6 (`inductive_mutation`) Rejection Breakdown

- Rejected mutants: 97
- Rejected at a later dependent declaration: 16
- Rejected at the mutated declaration itself: 81

### Accepted Mutants

- Mutant #504 (`inductive_mutation`): target `Std.Trichotomous` (line 42610) -- in inductive Std.Trichotomous, changed sort Prop -> Type 0 | output: `CHECK_OK file=/var/folders/4k/zxttxcf53d3616s6mvcsv_xc0000gn/T/rigor_mut_eqdmttu9/mutant_0504.ndjson decls=3480 env_decls=3913 lines=111785 mib=6.15 time_ms=78.79 decls_per_sec=44168 mib_per_sec=78.1 arena_exprs=115592`
- Mutant #575 (`inductive_mutation`): target `Std.IdempotentOp` (line 77940) -- in inductive Std.IdempotentOp, changed sort Prop -> Type 0 | output: `CHECK_OK file=/var/folders/4k/zxttxcf53d3616s6mvcsv_xc0000gn/T/rigor_mut_eqdmttu9/mutant_0575.ndjson decls=3480 env_decls=3913 lines=111785 mib=6.15 time_ms=75.56 decls_per_sec=46054 mib_per_sec=81.4 arena_exprs=115592`
- Mutant #581 (`inductive_mutation`): target `Std.Symm` (line 54035) -- in inductive Std.Symm, changed sort Prop -> Type 0 | output: `CHECK_OK file=/var/folders/4k/zxttxcf53d3616s6mvcsv_xc0000gn/T/rigor_mut_eqdmttu9/mutant_0581.ndjson decls=3480 env_decls=3913 lines=111785 mib=6.15 time_ms=75.02 decls_per_sec=46388 mib_per_sec=82.0 arena_exprs=115591`

### Review of Accepted Mutants (Round 2A)

All three accepted mutants are **harmless (valid CIC environments, not soundness bugs)**:

- Mutant #504 (`Std.Trichotomous`, `~/.elan/toolchains/leanprover--lean4---v4.36.0-rc1/src/lean/Init/Core.lean:2469`): defined as `class Trichotomous (r : α → α → Prop) : Prop where trichotomous (a b : α) : ¬ r a b → ¬ r b a → a = b`. Lifting its sort from `Prop` to `Type 0` remains strictly predicative (its sole field has sort `Prop : Type 0 <= Type 0`). Because it is a 1-constructor `Prop` structure with only a `Prop` field, it already permitted large elimination, so `Std.Trichotomous.rec` keeps the same universe-parameter arity and type. Its only downstream references in `Init.Core.ndjson` are `Std.Trichotomous.casesOn`, `Std.Trichotomous.recOn`, and `thm Std.Trichotomous.trichotomous`; in `trichotomous`, `[self : Std.Trichotomous r]` is a domain binder and the codomain lives in `Prop`, so the theorem type remains in `Prop` by `imax 1 0 = 0`. No declaration in `Init.Core.ndjson` constrains `Std.Trichotomous r : Prop` or relies on proof irrelevance of its instances.
- Mutant #575 (`Std.IdempotentOp`, `~/.elan/toolchains/leanprover--lean4---v4.36.0-rc1/src/lean/Init/Core.lean:2371`): defined as `class IdempotentOp (op : α → α → α) : Prop where idempotent : (x : α) → op x x = x`. Identical reasoning: 1-constructor structure with a single `Prop` field; its only downstream references in `Init.Core.ndjson` are `casesOn`, `recOn`, and `thm Std.IdempotentOp.idempotent` (whose codomain is in `Prop`, so `imax 1 0 = 0` keeps the theorem in `Prop`).
- Mutant #581 (`Std.Symm`, `~/.elan/toolchains/leanprover--lean4---v4.36.0-rc1/src/lean/Init/Core.lean:2454`): defined as `class Symm (r : α → α → Prop) : Prop where symm : ∀ a b, r a b → r b a`. Identical reasoning: 1-constructor structure with a single `Prop` field; its only downstream references in `Init.Core.ndjson` are `casesOn`, `recOn`, and `thm Std.Symm.symm` (codomain in `Prop`, `imax 1 0 = 0`).
- Conclusion: across 1,050 Round 2 mutants (700 on `Init.Core.ndjson` + 350 on `Init.Prelude.ndjson`), 1,047 were rejected and all 3 accepted mutants produce valid type-checked environments; no soundness bug found.

---

## Round 2B: Init.Prelude.ndjson (seed=2, 50 per operator)

### Command

```sh
RIGOR_THREADS=4 python3 /Users/sushikim/rigor/tools/mutation/mutate.py --input /tmp/rigor_real/Init.Prelude.ndjson --checker /Users/sushikim/rigor/target/release/rigor-bench --seed 2 --per-op 50 --workers 2 --report /Users/sushikim/rigor/tools/mutation/REPORT.md
```

### Sanity Check (Unmutated Input)

- Result: PASS (`CHECK_OK file=/tmp/rigor_real/Init.Prelude.ndjson decls=1840 env_decls=2121 lines=65406 mib=3.64 time_ms=51.34 decls_per_sec=35837 mib_per_sec=70.8 arena_exprs=67536`)
- Total elapsed time: 7.72 s

### Summary by Mutation Operator

| Operator | Total | Rejected | Accepted | Rejection Rate |
|---|---:|---:|---:|---:|
| `thm_value_swap` | 50 | 50 | 0 | 100.0% |
| `const_swap` | 50 | 50 | 0 | 100.0% |
| `arg_swap` | 50 | 50 | 0 | 100.0% |
| `level_change` | 50 | 50 | 0 | 100.0% |
| `def_body_rfl_break` | 50 | 50 | 0 | 100.0% |
| `inductive_mutation` | 50 | 50 | 0 | 100.0% |
| `level_arity_mismatch` | 50 | 50 | 0 | 100.0% |
| **Total** | **350** | **350** | **0** | **100.0%** |

### Operator 5 (`def_body_rfl_break`) Rejection Breakdown

- Rejected mutants: 50
- Rejected at a later dependent declaration: 8
- Rejected at the mutated declaration itself: 42

### Operator 6 (`inductive_mutation`) Rejection Breakdown

- Rejected mutants: 50
- Rejected at a later dependent declaration: 5
- Rejected at the mutated declaration itself: 45

### Accepted Mutants

None. Every generated mutant was rejected by Rigor.

---

## Round 3: Init.ndjson (seed=3, 20 per operator)

### Command

```sh
RIGOR_THREADS=4 python3 /Users/sushikim/rigor/tools/mutation/mutate.py --input /Users/sushikim/rigor-data/exports/Init.ndjson --checker /tmp/rigor-bench-round3 --seed 3 --per-op 20 --workers 2 --truncate --report /Users/sushikim/rigor/tools/mutation/REPORT.md --append-report --section-title "Round 3: Init.ndjson (seed=3, 20 per operator)" --json-out /Users/sushikim/rigor/tools/mutation/results_round3_init.json
```

### Sanity Check (Unmutated Input)

- Result: PASS (`CHECK_OK file=/Users/sushikim/rigor-data/exports/Init.ndjson decls=58546 env_decls=59978 lines=6495289 mib=331.66 time_ms=29058.52 decls_per_sec=2015 mib_per_sec=11.4 arena_exprs=6311599`)
- Total elapsed time: 820.46 s
- Truncation mode: ON (avg 3,542,856 / 6,495,289 lines = 54.5% per mutant; 2 Stage-1 accept(s) re-verified against the full un-truncated file)

### Summary by Mutation Operator

| Operator | Total | Rejected | Accepted | Rejection Rate |
|---|---:|---:|---:|---:|
| `thm_value_swap` | 20 | 20 | 0 | 100.0% |
| `const_swap` | 20 | 20 | 0 | 100.0% |
| `arg_swap` | 20 | 20 | 0 | 100.0% |
| `level_change` | 20 | 20 | 0 | 100.0% |
| `def_body_rfl_break` | 20 | 19 | 1 | 95.0% |
| `inductive_mutation` | 20 | 20 | 0 | 100.0% |
| `level_arity_mismatch` | 20 | 20 | 0 | 100.0% |
| **Total** | **140** | **139** | **1** | **99.3%** |

### Operator 5 (`def_body_rfl_break`) Rejection Breakdown

- Rejected mutants: 19
- Rejected at a later dependent declaration: 3
- Rejected at the mutated declaration itself: 16

### Operator 6 (`inductive_mutation`) Rejection Breakdown

- Rejected mutants: 20
- Rejected at a later dependent declaration: 6
- Rejected at the mutated declaration itself: 14

### Accepted Mutants

- Mutant #89 (`def_body_rfl_break`): target `HSMul.hSMul` (line 554307) -- in def HSMul.hSMul (rfl deps: _private.Init.Grind.Ring.IntSolver.0.Lean.Grind.CommRing.eq_norm_unsat_expr._proof_1_6 (via Lean.Grind.CommRing.Poly.denote) (via Lean.Grind.CommRing.Poly.denote._f), Lean.Grind.CommRing.Poly.denote_insertC (via Lean.Grind.CommRing.Poly.denote) (via Lean.Grind.CommRing.Poly.denote._f)), same-type const swap outParam -> semiOutParam | output: `CHECK_OK file=/var/folders/4k/zxttxcf53d3616s6mvcsv_xc0000gn/T/rigor_mut_7pm4l_8v/mutant_0089.ndjson decls=58546 env_decls=59978 lines=6495294 mib=331.66 time_ms=25259.84 decls_per_sec=2318 mib_per_sec=13.1 arena_exprs=6311604`

### Review of Accepted Mutants (Round 3)

Note: `/tmp/rigor-bench-round3` in the command above was an unmodified snapshot of `/Users/sushikim/rigor/target/release/rigor-bench` used to isolate the run from concurrent rebuilds.

The single accepted mutant is **harmless (definitionally equal term, not a soundness bug)**:

- Mutant #89 (`HSMul.hSMul`, `~/.elan/toolchains/leanprover--lean4---v4.36.0-rc1/src/lean/Init/Prelude.lean:1560`): `HSMul` is declared as `class HSMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where hSMul : α → β → γ`, so the binder type of `γ` inside the projection definition `HSMul.hSMul` mentions `outParam (Type w)`. The mutation swapped `outParam` for `semiOutParam`. In Lean 4 v4.36.0-rc1 (`Init/Prelude.lean`), both are identity functions on types used solely as elaborator/typeclass-synthesis metadata gadgets:
  - `~/.elan/toolchains/leanprover--lean4---v4.36.0-rc1/src/lean/Init/Prelude.lean:749`: `@[reducible] def outParam (α : Sort u) : Sort u := α`
  - `~/.elan/toolchains/leanprover--lean4---v4.36.0-rc1/src/lean/Init/Prelude.lean:772`: `@[reducible] def semiOutParam (α : Sort u) : Sort u := α`
  In `Init.ndjson` (lines 635 and 162480), both declarations even share the exact same exported `type` (`ie=495`), `value` (`ie=496`), `levelParams` (`[2]`), and `hints` (`{"regular": 1}`). Thus `outParam (Type w)` and `semiOutParam (Type w)` are definitionally equal (both delta-beta reduce to `Type w`), so replacing `outParam` with `semiOutParam` yields a definitionally equal body for `HSMul.hSMul`. Accepting it is correct; Lean's kernel accepts it as well.
- Stage-2 truncation check note: 2 of 140 mutants passed Stage 1 (truncated prefix) and were automatically re-verified against the full 6,495,289-line `Init.ndjson`; Mutant #108 (`inductive_mutation` on `Lean.Grind.CommRing.Poly.NonnegCoeffs.below`, `Prop -> Type 0`) was caught on the full file at `Lean.Grind.CommRing.Poly.NonnegCoeffs.below.casesOn` (`universe parameter count mismatch`), leaving only Mutant #89 accepted.
- Conclusion: across 140 Round 3 mutants on full `Init.ndjson` (20 per operator, seed 3), 139 were rejected and the sole accepted mutant (#89) is a definitionally equal elaborator-marker swap (`outParam -> semiOutParam`); no soundness bug found.

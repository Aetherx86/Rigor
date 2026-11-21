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

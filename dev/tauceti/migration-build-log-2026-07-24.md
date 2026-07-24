# Tau Ceti extraction — build & audit log (2026-07-24)

All commands run at Davis–Kahan `fc38eb4`+campaign, Tau Ceti branch
`approximation-numbers` @ `450317c1` (from `origin/main` `92c79e5e`).

## Davis–Kahan workspace

| Command | Result |
| --- | --- |
| `lake build ForTauCeti` (full staging library) | **PASS** — Build completed successfully (3038 jobs), warning-clean |
| `lake build ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.Basic` | PASS |
| `python3 scripts/check_dependency_layers.py` | **PASS** — 673 modules, 0 violations |
| `python3 -m pytest scripts/tests/test_check_dependency_layers.py` | **PASS** — 13 passed |
| `python3 -m pytest scripts/tests/test_export_for_tauceti.py` | **PASS** — 10 passed |
| `python3 scripts/export_for_tauceti.py --cluster approximation-number --check` | **PASS** — all 6 MATCH |
| `python3 scripts/check_davis_kahan_1970_source_census.py` | **PASS** — CLEAN (48 items) |
| `python3 scripts/check_library_structure.py` | pre-existing frontier state (scans only `DavisKahan`/`ForMathlib`; unchanged by this campaign — the campaign added no file to those roots and modified no existing `.lean`) |

DK footprint is **purely additive**: `git status` shows no existing
`DavisKahan/**` or `ForMathlib/**` `.lean` file modified. `DavisKahan.All` and the
trusted-dependency audits are therefore unaffected by construction; the only
lakefile changes are the additive `ForTauCeti` target/default and the (unused by
DK modules) `TauCeti` path require.

## Tau Ceti submodule — validation via throwaway export (NOT committed)

> Everything stays staged in `ForTauCeti`; **no commit is made to the
> `external/TauCeti` submodule** while we reorganize (awaiting roadmap guidance).
> The results below were produced by a *throwaway* `export_for_tauceti.py --write`
> into a temporary branch that was then reset — the submodule is back at pristine
> `main` (`92c79e5e`). Re-run `scripts/export_for_tauceti.py --cluster
> approximation-number --write` in a scratch branch to reproduce them.

| Command | Result |
| --- | --- |
| `lake exe cache get` | PASS — 8639 files |
| `lake build TauCeti.…ApproximationNumber.{FiniteDimensional,MinMax,Adjoint,OperatorModulus}` (+deps Basic, CourantFischer) | **PASS** — Build completed successfully (3036 jobs), **`warningAsError=true`, no warning/error output** |
| `#print axioms` on `approximationNumber_eq_singularValues`, `approximationNumber_adjoint`, `approximationNumber_smul`, `lowerBound_le_approximationNumber_of_finrank`, `norm_rectangularOperatorModulus_apply`, `orthogonal_specSubspace` | **PASS** — each depends only on `{propext, Classical.choice, Quot.sound}` (the Tau Ceti axiom allowlist); no `sorry`, `native_decide`, or custom axiom |
| module-system | **by construction** — all 6 files lead with `module`, `@[expose] public section`, `public import`, and built under `warningAsError`. (`lake exe module-system` / `lake exe axioms` / `scripts/lint-env.sh` enumerate the *whole* `TauCeti` tree and so require a full `lake build TauCeti`, which was not run here — the cluster modules are validated individually above; CI runs the full-tree audits.) |
| file lengths | PASS — all < 1000 (max CourantFischer 526) |
| diff scope | PASS — only `TauCeti/…`, 6 new files, 1662 insertions |

## Post-merge landing simulation (§15, not committed to main)

| Step | Result |
| --- | --- |
| Build the real `TauCeti.…ApproximationNumber.*` cluster **as a dependency from the DK workspace** (DK's newer Mathlib pin `3dffaf2f`) | **PASS** — Build completed successfully (3034 jobs). Confirms forward-compatibility with the newer pin, not only Tau Ceti's own. |
| DK-side consumer probe importing `TauCeti.…ApproximationNumber.{FiniteDimensional,Adjoint,OperatorModulus}` and using `T.approximationNumber_adjoint`, `T.approximationNumber_zero`, `TauCeti.norm_rectangularOperatorModulus_apply` | **PASS** — `lake env lean` exit 0. The declaration names are identical to the `ForTauCeti.*` staging names, so the post-merge switch is a mechanical import repoint, not a proof-repair campaign. |

The simulation probe lives only in the session scratchpad; nothing was committed
to the Davis–Kahan main migration branch (per §15).

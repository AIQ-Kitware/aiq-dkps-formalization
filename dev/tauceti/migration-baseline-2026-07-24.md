# Tau Ceti extraction campaign — baseline record (2026-07-24)

This file is the evidence baseline captured *before* the `ForTauCeti` staging
layer, dependency guards, and approximation-number extraction were introduced.
It is a snapshot; later sections of the campaign are measured against it.

## Repository commits

| Repository | Ref | Commit |
| --- | --- | --- |
| Davis–Kahan (this repo) | `main` | `fc38eb48b9b49f2e1d87fe0c7022dc5e262820a7` |
| `external/TauCeti` submodule | `heads/main` | `92c79e5e0a618f8c5c2b9909be1ce50f6891dde7` |
| `external/Spectra` submodule | `heads/master` | `8dbaaf6728d1342ae16acf79fd7eef7c59b37e63` |

The `external/TauCeti` submodule was at `92c79e5e…` on branch `main`, level
with `origin/main`, working tree clean, before any campaign edit.

## Lean toolchains

| Repository | Toolchain |
| --- | --- |
| Davis–Kahan | `leanprover/lean4:v4.32.0` |
| `external/TauCeti` | `leanprover/lean4:v4.32.0` |

Toolchains are identical, so adding Tau Ceti as a local Lake path dependency
requires no toolchain move.

## Mathlib revisions

| Repository | Mathlib rev | Commit date |
| --- | --- | --- |
| Davis–Kahan | `3dffaf2f18b47d11948f6390838ea6f2ae662aaf` | 2026-07-15 |
| `external/TauCeti` | `81a5d257c8e410db227a6665ed08f64fea08e997` | 2026-07-13 |

`git merge-base --is-ancestor 81a5d257 3dffaf2f` succeeds: the TauCeti pin is a
strict ancestor of the Davis–Kahan pin. **Davis–Kahan's Mathlib is newer.**
Consequently the local Lake path dependency uses the newer Davis–Kahan pin
(the root requirement wins, exactly as it does for vendored Spectra), which is a
*forward* move for the Tau Ceti build — no pin is moved backward. The Tau Ceti
PR itself is validated against Tau Ceti's own pin under Tau Ceti CI.

`ContinuousLinearMap.approximationNumber` (the canonical Mathlib object the
extraction would prefer) **does not exist** in either pinned Mathlib
(`grep` over both `.lake/packages/mathlib/Mathlib` trees returns nothing). The
foundational object therefore remains the locally developed `ℝ≥0`-valued
`ContinuousLinearMap.approximationNumber` staged in
`ForMathlib/Analysis/Normed/Operator/ApproximationNumber.lean`, *not* the
Davis–Kahan real-valued wrapper `approximationSingularValue`.

## Direct Spectra dependency footprint

| Metric | Count |
| --- | --- |
| Files under `DavisKahan/Interop/Spectra/` | 25 |
| Davis–Kahan modules importing a Spectra bridge or `Spectra` directly | 70 |
| Generic modules importing `DavisKahan.Sources` (a source facade) | 2 |
| Production (non-`Experimental`) modules importing `DavisKahan.Experimental` | 3 |
| `ForMathlib` files importing `DavisKahan`/`Spectra` (forbidden) | 0 |

The two generic modules importing a source facade are both in the
approximation-number cluster and are the backwards dependencies this campaign
removes:

* `DavisKahan/OperatorIdeal/ApproximationNumbers/OperatorModulus.lean`
  → `DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.UnitaryInvariantNorm`
* `DavisKahan/OperatorIdeal/ApproximationNumbers/BlockSum.lean`
  → `DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.SingularValueTransport`

Per the Spectra provenance map, the approximation-number cluster has **no
direct Spectra bridge** — it is a clean, self-contained Tier-1 / PR-1
candidate. The only Spectra reach in the cluster is the *modulus-invariance*
theorem, which routes through
`SpectraBridge.lt_approximationNumber_iff_exists_finiteDimensional_lowerBound`
(in `DavisKahan/Interop/Spectra/ApproximationNumberMinMax.lean`). That theorem
is deferred from PR 1 per the campaign's §9.2 option 2.

## Production build status at baseline

Recorded from the pinned checkout with the existing Mathlib build cache. See
`dev/tauceti/migration-build-log-2026-07-24.md` for command output captured
during the campaign. No preexisting production build failure is attributed to
this campaign; scratch modules under `DavisKahan/Experimental/Scratch/**` and
`Challenge/**` placeholders are intentionally out of the default build and are
not touched.

## Approximation-number cluster inventory (current homes)

Clean, Mathlib-only foundation (destined for Tau Ceti):

| File | Lines | Imports beyond Mathlib |
| --- | --- | --- |
| `ForMathlib/Analysis/Normed/Operator/ApproximationNumber.lean` | 354 | none |
| `ForMathlib/Analysis/Normed/Operator/ApproximationNumberAdjoint.lean` | 100 | `…ApproximationNumber` |
| `ForMathlib/Analysis/InnerProductSpace/CourantFischer.lean` | ~490 | none |
| `ForMathlib/Analysis/Normed/Operator/ApproximationNumberSingularValues.lean` | 262 | `…ApproximationNumber`, `…CourantFischer` |
| `ForMathlib/Analysis/Normed/Operator/ApproximationNumberMinMax.lean` | 130 | `…ApproximationNumber`, `…CourantFischer` |
| `ForMathlib/Analysis/InnerProductSpace/OperatorAbsoluteValue.lean` | ~150 | none |

Davis–Kahan-specific / Spectra-coupled (stay downstream or deferred):

| File | Lines | Note |
| --- | --- | --- |
| `DavisKahan/OperatorIdeal/ApproximationNumbers/Core.lean` | 819 | real wrapper `approximationSingularValue`; imports Spectra MinMax bridge |
| `DavisKahan/OperatorIdeal/ApproximationNumbers/OperatorModulus.lean` | 187 | modulus facts (clean) + Spectra-coupled invariance + paper-norm wrappers |
| `DavisKahan/OperatorIdeal/ApproximationNumbers/ScalarGeneric.lean` | 346 | ideal-family glue |
| `DavisKahan/OperatorIdeal/ApproximationNumbers/Real.lean` | 1232 | complexification real descent |
| `DavisKahan/OperatorIdeal/ApproximationNumbers/BlockSum.lean` | 715 | orthogonal block sums; imports Spectra + Sources |
| `DavisKahan/Interop/Spectra/ApproximationNumberMinMax.lean` | 347 | Spectra infinite-dim min–max bridge |

# Tau Ceti submission ladder

**Derived, not hand-maintained** (since 2026-07-29). Regenerate and verify with:

```sh
python3 scripts/derive_tauceti_submission_ladder.py          # report
python3 scripts/derive_tauceti_submission_ladder.py --check  # exit 1 if this document disagrees
```

The import graph is the source of truth. **A number here that the tool does not
reproduce is a bug in this document.**

> **Why this is now derived.** The first version was hand-measured and went
> stale *the same day*: it recorded 127 `ForTauCeti` modules, and 29 more landed
> hours later, so every headline statistic was measured against a tree that no
> longer existed. Its `closed slice` column was also computed two different ways
> — per-rung in isolation for B–E, cumulative for A and F — which is why rung C
> read "closed slice 3" while sitting on twelve modules. Both classes of error
> are now impossible to reintroduce silently.

This document answers one question: *what is the most valuable reorganization
for Tau Ceti submission?*

## The finding

**PR1 is not a PR. It is roughly six topics fused, and the fix is a re-slice, not
a rewrite.**

Tau Ceti accepts **one topic per PR against an accepted roadmap target**.
`tauceti-pr1-approximation-numbers.md` proposes *"Add rectangular approximation
numbers for bounded operators"* and points at 8 modules of approximation-number
content.

Its **dependency-closed slice is 37 `ForTauCeti` modules**, of which **29 are
outside the approximation-number tree**. A reviewer opening it would be asked to
accept, in one sitting:

- Schur--Horn majorization,
- convex majorization and symmetric gauges,
- Courant--Fischer,
- principal angles,
- polar decomposition and the positive operator square root,
- a five-module rectangular unitarily-invariant-norm framework,

*and* approximation numbers. That is not a reviewable unit, and no amount of
docstring or lint polish changes it.

## Why this is cheap to fix

**`ForTauCeti` is not a tangle.** Derived over its 160 modules, counting only
internal (`ForTauCeti.*`) imports:

| statistic | value |
| --- | --- |
| median internal import closure | **3** |
| mean | 8.3 |
| modules that are internal leaves | **43 of 160** |
| modules pulling more than 30 | **13** |
| maximum | 61 |

The library already stratifies: by longest internal chain the 160 modules spread
41/23/14/17/13/9/6/10/3/2/1/1/6/4/2/2/1/1 across eighteen layers. **The ladder exists in the import graph. It needs naming,
not building.** No Lean file has to move for the re-slice; only the submission
plan changes.

## The ladder

Each rung is dependency-closed and lists **only the modules it adds** over the
rungs above it. Submit in order; each PR then reviews as one topic against a
base Tau Ceti has already accepted.

### Rung A — Positive square root, operator modulus, polar decomposition

**7 new, cumulative closed slice 7.**

  - `Analysis.InnerProductSpace.BasisSpan`
  - `Analysis.InnerProductSpace.CourantFischer`
  - `Analysis.InnerProductSpace.OperatorModulus`
  - `Analysis.InnerProductSpace.PartialIsometry`
  - `Analysis.InnerProductSpace.PolarDecomposition`
  - `Analysis.InnerProductSpace.PositiveSqrt`
  - `Analysis.InnerProductSpace.SelfAdjointFunctionalCalculus`

### Rung B — Singular values (square and rectangular)

**2 new, cumulative closed slice 9.**

  - `Analysis.InnerProductSpace.RectangularSingularValues`
  - `Analysis.InnerProductSpace.SingularValues`

### Rung C — Rectangular approximation numbers  ← *this is the advertised PR1 topic*

**3 new, cumulative closed slice 12.**

  - `Analysis.OperatorIdeal.ApproximationNumber.Basic`
  - `LinearAlgebra.Dimension.RankComp`
  - `SetTheory.Cardinal.Lift`

### Rung D — Convex majorization and symmetric gauges

**7 new, cumulative closed slice 19.**

  - `Analysis.Convex.Majorization`
  - `Analysis.InnerProductSpace.KyFan`
  - `Analysis.InnerProductSpace.ProjectionGeometry`
  - `Analysis.InnerProductSpace.SchurHorn`
  - `Analysis.InnerProductSpace.SingularSubspace`
  - `Analysis.InnerProductSpace.Spectrum`
  - `Analysis.InnerProductSpace.UnitarilyInvariantNorm`

### Rung E — Rectangular unitarily invariant norms

**10 new, cumulative closed slice 29.**

  - `Analysis.InnerProductSpace.AlignedBasis`
  - `Analysis.InnerProductSpace.Basic`
  - `Analysis.InnerProductSpace.GramMatrix`
  - `Analysis.InnerProductSpace.PrincipalAngles`
  - `Analysis.InnerProductSpace.RectangularUnitarilyInvariantNorm`
  - `Analysis.InnerProductSpace.RectangularUnitarilyInvariantNorm.Basic`
  - `Analysis.InnerProductSpace.RectangularUnitarilyInvariantNorm.BlockSum`
  - `Analysis.InnerProductSpace.RectangularUnitarilyInvariantNorm.Instances`
  - `Analysis.InnerProductSpace.RectangularUnitarilyInvariantNorm.Majorization`
  - `Analysis.Normed.Operator.LinearIsometry`

### Rung F — Ky Fan gauges and operator ideal families

**12 new, cumulative closed slice 41.**

  - `Analysis.InnerProductSpace.SpectralCutoff`
  - `Analysis.OperatorIdeal.ApproximationNumber.Adjoint`
  - `Analysis.OperatorIdeal.ApproximationNumber.FiniteDimensional`
  - `Analysis.OperatorIdeal.ApproximationNumber.FiniteRestriction`
  - `Analysis.OperatorIdeal.ApproximationNumber.KyFan`
  - `Analysis.OperatorIdeal.ApproximationNumber.MinMax`
  - `Analysis.OperatorIdeal.ApproximationNumber.MinMaxUpper`
  - `Analysis.OperatorIdeal.Family.Basic`
  - `Analysis.OperatorIdeal.Family.KyFan`
  - `Analysis.OperatorIdeal.Family.KyFanDominance`
  - `Analysis.OperatorIdeal.Family.OperatorNorm`
  - `Analysis.OperatorIdeal.Family.TraceClass`

**Cumulative: 41 of 160 `ForTauCeti` modules** — the rest is not yet on the
submission path. See *What is not on the ladder* below; it is 74%.

## The number that makes the case

| | modules in one PR |
| --- | --- |
| PR1 as currently scoped | **37** |
| Rung C, the same advertised topic, after A and B land | **3** |

## What to do with the existing PR1 draft

`tauceti-pr1-approximation-numbers.md` is not wrong about the *content* it wants
to land; it is wrong about the *unit*. Keep it as the rung-C narrative and hang
rungs A, B, D, E, F off this file. Do not submit the 37-module version.

## What is not on the ladder — 119 of 160 modules, 74%

Rungs A–F cover the approximation-number/ideal stack and stop. **Everything
else in `ForTauCeti` has no submission path at all**, and that is now the larger
half of the library. Derived breakdown by subtree:

| modules | subtree | roadmap that should own it |
|---|---|---|
| 19 | `Analysis.InnerProductSpace.LinearPMap` | [`UnboundedOperators`](../../ForTauCetiRoadmap/UnboundedOperators/README.md) |
| 5 | `Analysis.InnerProductSpace.BorelCalculus` | `UnboundedOperators` |
| 4 | `Analysis.InnerProductSpace.OneParameterUnitaryGroup` | `UnboundedOperators` |
| 2 | `Analysis.InnerProductSpace.ProjValMeasure` | `UnboundedOperators` |
| 5 | `Analysis.InnerProductSpace.Sylvester` | [`SpectralSubspacePerturbation`](../../ForTauCetiRoadmap/SpectralSubspacePerturbation/README.md) |
| 3 | `Analysis.InnerProductSpace.SinTheta` | `SpectralSubspacePerturbation` |
| 3 | `Analysis.InnerProductSpace.Residual` | `SpectralSubspacePerturbation` |
| 3 | `Analysis.InnerProductSpace.YuWangSamworth` | `SpectralSubspacePerturbation` |
| 3 | `Analysis.InnerProductSpace.BoundedOperator` | `SpectralSubspacePerturbation` |
| 5 | `Analysis.Fourier.*` (Haagerup–Zsidó and kernel) | **none — no roadmap exists** |
| 2 | `Analysis.SpecialFunctions.Integral` | **none** |
| 1 | `Analysis.CStarAlgebra.SelfAdjointGapInverse` | **none** |

Two conclusions, and they point in opposite directions:

- **The unbounded stack is the biggest unsubmitted block** (30 modules across
  `LinearPMap`, `BorelCalculus`, `OneParameterUnitaryGroup`, `ProjValMeasure`)
  and it already has a roadmap. It needs rungs, not new mathematics.
- **The Davis–Kahan sin-Θ material only just arrived here** — `SinTheta`,
  `Sylvester`, `Residual`, `YuWangSamworth`, `BoundedOperator` are what Y3(b4)
  and Y3(c) migrated on 2026-07-29. It is the mathematics this project exists to
  contribute, its roadmap
  (`SpectralSubspacePerturbation`) names Davis–Kahan Part III as its principal
  worked source, and it is **not on any rung**.

Against the readiness standard in `ForTauCeti/README.md` — that `ForTauCeti`
should already satisfy the *platonic ideal* Tau Ceti roadmap — a 27% ladder is
the honest measure of how far that is. Extending it is lane `LADDER-EXT` in
`dev/LANES.md`.

## Honest limits of this measurement

- The rung boundaries are chosen at natural mathematical topics; the import
  graph constrains their **order**, not their exact cut points. Rungs D/E could
  be split further, or A/B merged, without violating any dependency.
- Module counts are not review effort. Rung F is 12 modules but is the
  ideal-family framework, and is likely the hardest to land.
- This measures `ForTauCeti` only. `DavisKahan/**` is the paper library and is
  not on the submission path.
- Nothing here has been agreed with Tau Ceti. The roadmap-target marker in the
  PR1 draft is still provisional, and the rung names are ours, not theirs.

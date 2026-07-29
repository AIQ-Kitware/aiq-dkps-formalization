# Tau Ceti submission ladder

**Measured 2026-07-29.** This document answers one question: *what is the most
valuable reorganization for Tau Ceti submission?*

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

**`ForTauCeti` is not a tangle.** Measured over its 127 modules, counting only
internal (`ForTauCeti.*`) imports:

| statistic | value |
| --- | --- |
| median internal import closure | **2** |
| mean | 6.4 |
| modules that are internal leaves | **37 of 127** |
| modules pulling more than 30 | **6** |
| maximum | 40 |

The library already stratifies: longest-chain depth spreads 37/19/13/15/9/7/…
across sixteen layers. **The ladder exists in the import graph. It needs naming,
not building.** No Lean file has to move for the re-slice; only the submission
plan changes.

## The ladder

Each rung is dependency-closed and lists **only the modules it adds** over the
rungs above it. Submit in order; each PR then reviews as one topic against a
base Tau Ceti has already accepted.

### Rung A — Positive square root, operator modulus, polar decomposition

**7 new, closed slice 7.**

  - `Analysis.InnerProductSpace.BasisSpan`
  - `Analysis.InnerProductSpace.CourantFischer`
  - `Analysis.InnerProductSpace.OperatorModulus`
  - `Analysis.InnerProductSpace.PartialIsometry`
  - `Analysis.InnerProductSpace.PolarDecomposition`
  - `Analysis.InnerProductSpace.PositiveSqrt`
  - `Analysis.InnerProductSpace.SelfAdjointFunctionalCalculus`

### Rung B — Singular values (square and rectangular)

**2 new, closed slice 4.**

  - `Analysis.InnerProductSpace.RectangularSingularValues`
  - `Analysis.InnerProductSpace.SingularValues`

### Rung C — Rectangular approximation numbers  ← *this is the advertised PR1 topic*

**3 new, closed slice 3.**

  - `Analysis.OperatorIdeal.ApproximationNumber.Basic`
  - `LinearAlgebra.Dimension.RankComp`
  - `SetTheory.Cardinal.Lift`

### Rung D — Convex majorization and symmetric gauges

**7 new, closed slice 13.**

  - `Analysis.Convex.Majorization`
  - `Analysis.InnerProductSpace.KyFan`
  - `Analysis.InnerProductSpace.ProjectionGeometry`
  - `Analysis.InnerProductSpace.SchurHorn`
  - `Analysis.InnerProductSpace.SingularSubspace`
  - `Analysis.InnerProductSpace.Spectrum`
  - `Analysis.InnerProductSpace.UnitarilyInvariantNorm`

### Rung E — Rectangular unitarily invariant norms

**10 new, closed slice 24.**

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

**12 new, closed slice 41.**

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

**Cumulative: 41 of 127 `ForTauCeti` modules** — the rest is not yet on the
submission path.

## The number that makes the case

| | modules in one PR |
| --- | --- |
| PR1 as currently scoped | **37** |
| Rung C, the same advertised topic, after A and B land | **3** |

## What to do with the existing PR1 draft

`tauceti-pr1-approximation-numbers.md` is not wrong about the *content* it wants
to land; it is wrong about the *unit*. Keep it as the rung-C narrative and hang
rungs A, B, D, E, F off this file. Do not submit the 37-module version.

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

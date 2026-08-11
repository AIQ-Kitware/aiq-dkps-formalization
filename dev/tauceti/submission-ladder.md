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

**`ForTauCeti` is not a tangle.** Derived over its 164 modules, counting only
internal (`ForTauCeti.*`) imports:

| statistic | value |
| --- | --- |
| median internal import closure | **3** |
| mean | 8.7 |
| modules that are internal leaves | **43 of 164** |
| modules pulling more than 30 | **15** |
| maximum | 64 |

The library already stratifies. **The ladder exists in the import graph. It needs
naming, not building.** No Lean file has to move for the re-slice; only the
submission plan changes.

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
  - `Analysis.InnerProductSpace.Polar.Decomposition`
  - `Analysis.InnerProductSpace.PositiveSqrt`
  - `Analysis.InnerProductSpace.SelfAdjointFunctionalCalculus`

### Rung B — Singular values (square and rectangular)

**3 new, cumulative closed slice 10.**

  - `Analysis.InnerProductSpace.RectangularSingularValues`
  - `Analysis.InnerProductSpace.Singular.Values`
  - `Analysis.InnerProductSpace.Spectrum`

### Rung C — Rectangular approximation numbers  ← *this is the advertised PR1 topic*

**3 new, cumulative closed slice 13.**

  - `Analysis.OperatorIdeal.ApproximationNumber.Basic`
  - `LinearAlgebra.Dimension.RankComp`
  - `SetTheory.Cardinal.Lift`

### Rung D — Convex majorization and symmetric gauges

**5 new, cumulative closed slice 18.**

  - `Analysis.Convex.Majorization`
  - `Analysis.InnerProductSpace.KyFan`
  - `Analysis.InnerProductSpace.Projection.Geometry`
  - `Analysis.InnerProductSpace.SchurHorn`
  - `Analysis.InnerProductSpace.Singular.Subspace`

### Rung E — Rectangular unitarily invariant norms

**5 new, cumulative closed slice 23.**

  - `Analysis.InnerProductSpace.AlignedBasis`
  - `Analysis.InnerProductSpace.Basic`
  - `Analysis.InnerProductSpace.Gram.Matrix`
  - `Analysis.InnerProductSpace.PrincipalAngles`
  - `Analysis.Normed.Operator.LinearIsometry`

### Rung F — Ky Fan gauges and operator ideal families

**22 new, cumulative closed slice 45.**

  - `Analysis.InnerProductSpace.RectangularUnitarilyInvariantSeminorm`
  - `Analysis.InnerProductSpace.RectangularUnitarilyInvariantSeminorm.Basic`
  - `Analysis.InnerProductSpace.RectangularUnitarilyInvariantSeminorm.BlockSum`
  - `Analysis.InnerProductSpace.RectangularUnitarilyInvariantSeminorm.Instances`
  - `Analysis.InnerProductSpace.RectangularUnitarilyInvariantSeminorm.Majorization`
  - `Analysis.InnerProductSpace.Spectral.Cutoff`
  - `Analysis.InnerProductSpace.UnitarilyInvariantSeminorm`
  - `Analysis.Normed.Operator.FiniteRankCompact`
  - `Analysis.OperatorIdeal.ApproximationNumber.Adjoint`
  - `Analysis.OperatorIdeal.ApproximationNumber.Compact`
  - `Analysis.OperatorIdeal.ApproximationNumber.CompactHilbert`
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
  - `Topology.ENNRealLiminf`

**Cumulative after F: 41 of 271 `ForTauCeti` modules.** Rungs A–F were the whole
ladder until 2026-07-29; rungs G–S below carry the other 123.

### Rung G — Foundations completion — the rest of topics T01-T10

**35 new, cumulative closed slice 80.**

  - `Analysis.CStarAlgebra.RealSpectrumFunctionalCalculus`
  - `Analysis.InnerProductSpace.AngleGeometry`
  - `Analysis.InnerProductSpace.EigenvalueChange`
  - `Analysis.InnerProductSpace.FiniteFrame`
  - `Analysis.InnerProductSpace.FrameFactorization`
  - `Analysis.InnerProductSpace.Gram.Operator`
  - `Analysis.InnerProductSpace.HilbertSchmidt.Energy`
  - `Analysis.InnerProductSpace.HoffmanWielandt`
  - `Analysis.InnerProductSpace.MoorePenroseInverse`
  - `Analysis.InnerProductSpace.NearIsometry`
  - `Analysis.InnerProductSpace.OrthogonalSeries`
  - `Analysis.InnerProductSpace.Polar.Isometry`
  - `Analysis.InnerProductSpace.Polar.PartialIsometry`
  - `Analysis.InnerProductSpace.Projection.Blocks`
  - `Analysis.InnerProductSpace.Projection.Gap`
  - `Analysis.InnerProductSpace.RectangularPartialIsometry`
  - `Analysis.InnerProductSpace.ReducingSubspace`
  - `Analysis.InnerProductSpace.SchattenNorm`
  - `Analysis.InnerProductSpace.Singular.System`
  - `Analysis.InnerProductSpace.Spectral.Gap`
  - `Analysis.InnerProductSpace.Spectral.Subspace`
  - `Analysis.InnerProductSpace.TwoDimensionalSingularValues`
  - `Analysis.Normed.FiniteLpGauge`
  - `Analysis.OperatorIdeal.ApproximationNumber.Core`
  - `Analysis.OperatorIdeal.ApproximationNumber.DiagonalExample`
  - `Analysis.OperatorIdeal.ApproximationNumber.DiagonalSequence`
  - `Analysis.OperatorIdeal.ApproximationNumber.EnergyComparison`
  - `Analysis.OperatorIdeal.ApproximationNumber.Examples`
  - `Analysis.OperatorIdeal.ApproximationNumber.FiniteValueFibers`
  - `Analysis.OperatorIdeal.ApproximationNumber.FiniteValueSeparation`
  - `Analysis.OperatorIdeal.ApproximationNumber.LeadingCutoff`
  - `Analysis.OperatorIdeal.ApproximationNumber.SameSequence`
  - `Analysis.OperatorIdeal.Family.HilbertSchmidt`
  - `Analysis.OperatorIdeal.Family.Schatten`
  - `Analysis.SpecialFunctions.Sqrt`

### Rung H — Hilbert-Schmidt operators (T11)

**4 new, cumulative closed slice 84.**

  - `Analysis.InnerProductSpace.HilbertSchmidt.Conjugation`
  - `Analysis.InnerProductSpace.HilbertSchmidt.Lp`
  - `Analysis.InnerProductSpace.HilbertSchmidt.Pythagoras`
  - `Analysis.InnerProductSpace.HilbertSchmidt.Space`

### Rung I — The Haagerup-Zsido kernel and its Fourier transform (T12)

**8 new, cumulative closed slice 92.**

  - `Analysis.Fourier.ExponentialAbs`
  - `Analysis.Fourier.HaagerupZsido.Defs`
  - `Analysis.Fourier.HaagerupZsido.Fourier`
  - `Analysis.Fourier.HaagerupZsido.Integrability`
  - `Analysis.Fourier.HaagerupZsido.Kernel`
  - `Analysis.Fourier.Poisson.CauchyLattice`
  - `Analysis.SpecialFunctions.Integral.RationalQuadratic`
  - `Analysis.SpecialFunctions.Integral.SineLaplace`

### Rung J — One-parameter unitary groups and Stone's theorem (T13)

**6 new, cumulative closed slice 98.**

  - `Analysis.InnerProductSpace.IntertwiningUnitary`
  - `Analysis.InnerProductSpace.OneParameterUnitaryGroup.Basic`
  - `Analysis.InnerProductSpace.OneParameterUnitaryGroup.Commutant`
  - `Analysis.InnerProductSpace.OneParameterUnitaryGroup.SemigroupBridge`
  - `Analysis.InnerProductSpace.OneParameterUnitaryGroup.Stone`
  - `Analysis.InnerProductSpace.SkewAdjointExponential`

### Rung K — Borel functional calculus and projection-valued measures (T14)

**11 new, cumulative closed slice 109.**

  - `Analysis.InnerProductSpace.BorelCalculus.DiagonalMeasure`
  - `Analysis.InnerProductSpace.BorelCalculus.Multiplicative`
  - `Analysis.InnerProductSpace.BorelCalculus.Operator`
  - `Analysis.InnerProductSpace.BorelCalculus.PVM`
  - `Analysis.InnerProductSpace.BorelCalculus.Polarization`
  - `Analysis.InnerProductSpace.ProjValMeasure.Additivity`
  - `Analysis.InnerProductSpace.ProjValMeasure.Basic`
  - `Analysis.InnerProductSpace.ProjValMeasure.Subspace`
  - `MeasureTheory.CfcMeasurable`
  - `MeasureTheory.CompactExists`
  - `MeasureTheory.HellySelection`

### Rung L — Closed operators on LinearPMap: graphs, constructions and form bounds (T15a)

**7 new, cumulative closed slice 116.**

  - `Analysis.InnerProductSpace.LinearPMap.Closed`
  - `Analysis.InnerProductSpace.LinearPMap.Constructions`
  - `Analysis.InnerProductSpace.LinearPMap.GraphCore`
  - `Analysis.InnerProductSpace.LinearPMap.SubmoduleAdjoint`
  - `Analysis.InnerProductSpace.LinearPMap.Sylvester`
  - `Analysis.InnerProductSpace.QuadraticFormBounds`
  - `Analysis.InnerProductSpace.SpectralOrder.Complex`

### Rung M — Resolvents of self-adjoint LinearPMap operators, and semiboundedness (T15b)

**7 new, cumulative closed slice 123.**

  - `Analysis.CStarAlgebra.SelfAdjointGapInverse`
  - `Analysis.InnerProductSpace.LinearPMap.RealLowerBound`
  - `Analysis.InnerProductSpace.LinearPMap.Resolvent`
  - `Analysis.InnerProductSpace.LinearPMap.ResolventBound`
  - `Analysis.InnerProductSpace.LinearPMap.ResolventOpen`
  - `Analysis.InnerProductSpace.LinearPMap.SelfAdjointResolvent`
  - `Analysis.InnerProductSpace.SeparatedIntertwiner`

### Rung N — The spectral measure of an unbounded self-adjoint operator, and Stone (T15c)

**16 new, cumulative closed slice 139.**

  - `Analysis.InnerProductSpace.BlockLowerBound`
  - `Analysis.InnerProductSpace.LinearPMap.SelfAdjointMaximal`
  - `Analysis.InnerProductSpace.LinearPMap.SpectralCutOperator`
  - `Analysis.InnerProductSpace.LinearPMap.SpectralFormBounds`
  - `Analysis.InnerProductSpace.LinearPMap.SpectralGapInverse`
  - `Analysis.InnerProductSpace.LinearPMap.SpectralGrid`
  - `Analysis.InnerProductSpace.LinearPMap.SpectralMeasure`
  - `Analysis.InnerProductSpace.LinearPMap.SpectralMeasure.Construction`
  - `Analysis.InnerProductSpace.LinearPMap.SpectralProjectionGroup`
  - `Analysis.InnerProductSpace.LinearPMap.SpectralSupport`
  - `Analysis.InnerProductSpace.LinearPMap.SpectralVectorBounds`
  - `Analysis.InnerProductSpace.LinearPMap.StoneUniqueness`
  - `Analysis.InnerProductSpace.LinearPMap.YosidaApproximation`
  - `Analysis.OperatorIdeal.ApproximationNumber.FinitePVMSelection`
  - `Analysis.OperatorIdeal.ApproximationNumber.GramBandPolar`
  - `Analysis.OperatorIdeal.ApproximationNumber.GramSpectralRank`

### Rung O — Sylvester equations and the Rosenblum theorem (T16)

**18 new, cumulative closed slice 157.**

  - `Analysis.InnerProductSpace.CoerciveUnit`
  - `Analysis.InnerProductSpace.HilbertSchmidt.Block`
  - `Analysis.InnerProductSpace.Rosenblum`
  - `Analysis.InnerProductSpace.Sylvester.Basic`
  - `Analysis.InnerProductSpace.Sylvester.BlockEstimate`
  - `Analysis.InnerProductSpace.Sylvester.BlockIdentity`
  - `Analysis.InnerProductSpace.Sylvester.Bound`
  - `Analysis.InnerProductSpace.Sylvester.Generator`
  - `Analysis.InnerProductSpace.Sylvester.Group`
  - `Analysis.InnerProductSpace.Sylvester.Internal.ReciprocalMultiplier`
  - `Analysis.InnerProductSpace.Sylvester.Internal.ReciprocalMultiplier.DoubledPhase`
  - `Analysis.InnerProductSpace.Sylvester.Internal.ReciprocalMultiplier.Fourier`
  - `Analysis.InnerProductSpace.Sylvester.Internal.ReciprocalMultiplier.OrbitAction`
  - `Analysis.InnerProductSpace.Sylvester.Internal.SpectralBounds`
  - `Analysis.InnerProductSpace.Sylvester.Interval`
  - `Analysis.InnerProductSpace.Sylvester.Operator`
  - `Analysis.InnerProductSpace.Sylvester.SpectralDistance`
  - `Analysis.InnerProductSpace.Sylvester.SpectralGap`

### Rung P — Spectral subspace perturbation: the Davis-Kahan sin-Theta theorems (T17)

**15 new, cumulative closed slice 172.**

  - `Analysis.InnerProductSpace.BoundedOperator.Projector`
  - `Analysis.InnerProductSpace.BoundedOperator.SinTheta`
  - `Analysis.InnerProductSpace.Complexification.Basic`
  - `Analysis.InnerProductSpace.Complexification.FunctionalCalculus`
  - `Analysis.InnerProductSpace.DoubleAngle.Vector`
  - `Analysis.InnerProductSpace.ReducedExtension`
  - `Analysis.InnerProductSpace.Residual.AngleEmbedding`
  - `Analysis.InnerProductSpace.Residual.Ritz`
  - `Analysis.InnerProductSpace.Residual.TrialMap`
  - `Analysis.InnerProductSpace.SinTheta.DirectedBounds`
  - `Analysis.InnerProductSpace.SinTheta.OperatorNorm`
  - `Analysis.InnerProductSpace.SinTheta.Perturbation`
  - `Analysis.InnerProductSpace.SinTheta.UnitarilyInvariant`
  - `Analysis.InnerProductSpace.SpectralOrder.Real`
  - `Analysis.OperatorIdeal.ApproximationNumber.MinMaxReal`

### Rung Q — The Yu-Wang-Samworth statistical variant (T18)

**3 new, cumulative closed slice 175.**

  - `Analysis.InnerProductSpace.YuWangSamworth.Residual`
  - `Analysis.InnerProductSpace.YuWangSamworth.SingularSubspace`
  - `Analysis.InnerProductSpace.YuWangSamworth.Statistics`

### Rung R — Matrix spectra and spectral measurability (T19)

**6 new, cumulative closed slice 181.**

  - `Analysis.Matrix.EntrywiseEigenvalue`
  - `Analysis.Matrix.EntrywiseOpNorm`
  - `Analysis.Matrix.SpectralFunctionMeasurable`
  - `Analysis.Matrix.Spectrum`
  - `MeasureTheory.Function.ConvergenceInMeasure`
  - `MeasureTheory.Measure.Typeclasses.Probability`

### Rung S — Sample moments and matrix concentration (T20)

**5 new, cumulative closed slice 186.**

  - `Probability.Moments.CenteredScatter`
  - `Probability.Moments.MatrixConcentration`
  - `Probability.Moments.SampleMean`
  - `Probability.Moments.SampleSecondMoment`
  - `Probability.Moments.Variance`

### Rung T — Matrix rank factorization and positive semidefiniteness (T21)

**2 new, cumulative closed slice 188.**

  - `LinearAlgebra.Matrix.PosDef`
  - `LinearAlgebra.Matrix.RankFactorization`

### Rung U — Berge's maximum theorem and approximate minimizers (T22)

**2 new, cumulative closed slice 190.**

  - `Topology.ApproxMinimizer`
  - `Topology.Berge`
**Cumulative: 179 of 271 `ForTauCeti` modules — the ladder is total.**

It briefly was not.  Three modules merged in after rung U closed on 2026-07-29
and no rung's closure reached them; they were placed on 2026-07-30 by matching
each one's roadmap topic to the rung that carries that topic —
`ApproximationNumber.{CompactHilbert,DiagonalExample}` are T09, so rung G, and
`LinearPMap.SubmoduleAdjoint` is T15a, so rung L.  A module falls off the ladder
whenever it is a leaf nobody imports yet, which is what a new result looks like
before anything consumes it; the fix is to seed it in the rung of its topic, in
`scripts/derive_tauceti_submission_ladder.py`.

## The number that makes the case

| | modules in one PR |
| --- | --- |
| PR1 as currently scoped | **37** |
| Rung C, the same advertised topic, after A and B land | **3** |

## What to do with the existing PR1 draft

`tauceti-pr1-approximation-numbers.md` is not wrong about the *content* it wants
to land; it is wrong about the *unit*. Keep it as the rung-C narrative and hang
rungs A, B, D, E, F off this file. Do not submit the 37-module version.

## What was not on the ladder — the record, and its close

**Closed 2026-07-29 (lane LADDER-EXT). The ladder is total: 164 of 164, nothing
off it.** This section is kept because the finding it recorded was the reason the
lane existed, and because *how* it closed is the useful part.

As written on 2026-07-29, rungs A–F covered the approximation-number/ideal stack
and stopped, leaving **119 of 160 modules — 74% — with no submission path at
all**. The derived breakdown named three blocks: the unbounded stack (30 modules
under `LinearPMap`, `BorelCalculus`, `OneParameterUnitaryGroup`,
`ProjValMeasure`), the Davis–Kahan sin-Θ material that Y3(b4)/Y3(c) had just
migrated (17 modules), and 8 orphans with **no roadmap at all** —
`Analysis.Fourier.*`, `Analysis.SpecialFunctions.Integral.*` and
`Analysis.CStarAlgebra.SelfAdjointGapInverse` — which the lane was told not to
invent a roadmap for.

What closed it was not new mathematics and not a new measurement. It was that a
*validated partition already existed*: `scripts/check_tauceti_roadmap_topics.py`
proves the library's 22 roadmap topics total, disjoint and acyclic in submission
order. Rungs G–S are therefore **one rung per topic, in that order**, seeded with
each topic's own module list, so a rung is exactly a roadmap target — Tau Ceti's
own unit of review. Rung G is the one exception it has to be: A–F predate the
partition and cut across topics T01–T10, so G completes those ten.

**T15 was three rungs, not one** (lane T15-SPLIT, 2026-07-29). The
`review-ForTauCeti-T04-T20` audit found the 25-module topic to be three chains
that barely touch, and the import graph then moved three modules across the cut
the audit proposed: `RealLowerBound` imports `SelfAdjointResolvent`,
`SelfAdjointMaximal` imports `SpectralMeasure`, and `SpectralGapInverse` imports
`SpectralSupport`, so each sits one chain later than its name suggests. Placed by
dependency, the split is rungs **L** (T15a, closedness and graphs, 6), **M**
(T15b, resolvents and semiboundedness, 7) and **N** (T15c, the spectral measure
and Stone, 12) — and **T15b turns out to be independent of every other topic**,
which the undivided T15 could not be. Rungs O–U are the old M–S, shifted.

Two of the three blocks needed nothing but naming. The third dissolved on
inspection:

- **Seven of the eight "no roadmap" orphans are topic T12**, whose roadmap
  (now Part A of `ForTauCetiRoadmap/HilbertSpaceOperatorTheory/SpectralSubspacePerturbation/`) was written the same day. They are
  rung I.
- **The eighth, `Analysis.CStarAlgebra.SelfAdjointGapInverse`, was never an
  orphan** — the topic table already assigns it to T15 (now T15b), where it lands
  as part of rung M. The "needs a decision from jon" caveat on it was measured against the
  subtree listing, not against the topic partition.

Against the readiness standard in `ForTauCeti/README.md` — that `ForTauCeti`
should already satisfy the *platonic ideal* Tau Ceti roadmap — the ladder is no
longer the gap. What remains is per-rung: rungs G–S have derived module lists and
correct order, but only rungs C and I have a written narrative of what the PR
argues. Writing those narratives is the successor work, and it is per topic.

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

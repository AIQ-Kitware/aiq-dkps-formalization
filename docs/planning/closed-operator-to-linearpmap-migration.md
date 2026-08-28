# `DavisKahanExt.ClosedOperator` → `LinearPMap`: how it was done

**Status 2026-08-28: complete.**  The bundled record, its forwarding API, the
`Interop/TauCeti` adapter and every name derived from it are gone.  An unbounded
operator in this repository is a Mathlib `LinearPMap`; density, closedness,
symmetry and self-adjointness are hypotheses.  This file is the record of the
migration, not a plan.

## What the bundle was

```lean
structure ClosedOperator where
  domain : Submodule 𝕜 E
  toLinearMap : domain →ₗ[𝕜] E
  dense_domain : Dense (domain : Set E)
  closed_graph : IsClosed (Set.range fun x : domain => ((x : E), toLinearMap x))
```

A `LinearPMap` plus two properties — and **almost every declaration in its API
was already an `abbrev` forwarding to `TauCeti.LinearPMap.*` at
`A.toLinearPMap`**: `SameDomain`, `MapsDomainTo`, `BoundedExtension`, `Extends`,
`IsSymmetric`, `IsSelfAdjoint`, `graphNorm`, `RelativelyBounded`,
`realResolventSet`, `realSpectrum`, `SpectralSetsSeparated`, `ReducesSubspace`,
`InvariantSubspace`, `reducingRestriction`.  So the mathematics never moved.
What moved was signatures:

| before | after |
| --- | --- |
| `(A : ...ClosedOperator (𝕜 := 𝕜) (E := E))` | `(A : E →ₗ.[𝕜] E)` |
| `A.toLinearPMap` | `A` |
| `A.toLinearMap x` | `A x` |
| `A.dense_domain` | `hA.dense_domain`, from the self-adjointness hypothesis |
| `A.closed_graph` | `hA.isClosed`, likewise |
| `A.IsSelfAdjoint` | `IsSelfAdjoint A` |
| `ClosedOperator.ofBounded A` | `A.toLinearMap.toPMap ⊤` |
| `A.addBounded V` | `TauCeti.LinearPMap.addBounded A V` |

The density and closedness rows are the only ones needing judgement, and the
answer was almost always "no new hypothesis": most generic statements never
touch either, and the ones that do already take self-adjointness.

## Order, and what each step actually cost

1. **The gap predicates.**  `FormBoundedSylvesterGap`,
   `RealSpectrumIntervalExteriorGap`, `SpectralSylvesterGap`,
   `SpectralIntervalExteriorGap`.  Four predicates collapsed to two —
   `UnboundedSylvesterGapPMap` and `UnboundedIntervalExteriorGapPMap` had become
   verbatim copies — and six duplicate constructors to three.
2. **The Sylvester equation and semibounds.**  `SemiboundedBelow`,
   `SemiboundedAbove`, `ClosedSylvesterEquation`, `HasClosedSylvesterEquation`,
   `HasBoundedEverywhereInverse`: five shims over canonical predicates, 134 uses
   renamed.
3. **The engine, the producers and the data record, together.**  Retyping
   `selfAdjointSpectralRestriction` alone was attempted first and reverted: the
   producers, the sine-theta data record and the `BoundedRealization` chain are
   one cluster.  Done together they cost far less than they looked, because
   `selfAdjointSpectralRestriction` *is* `LinearPMap.specRestrict`, `ofBounded A`
   *is* `A.toLinearMap.toPMap ⊤`, and `addBounded` was already in `ForTauCeti`.

   The decision that made this step tractable: `UnboundedSinThetaData` and
   `UnboundedSinThetaDataPMap` were the same record twice, and merging them let
   the six `A_dense`/`A_closed` fields go — every theorem that needs them already
   takes self-adjointness.  That removed the constructor burden at all fourteen
   build sites, and twelve `linearPMap_*` twin theorems with it.
4. **The names.**  `SpectralTheory/ClosedOperator/` → `PartialMap/`; the fifteen
   `linearPMap_`-prefixed declarations lost a prefix that no longer
   distinguished anything; the remaining 230 mentions were renamed.

**One** lemma was added to `ForTauCeti`:
`LinearPMap.isSymmetric_of_isSelfAdjoint`.  `addBounded` was added too and then
removed again — it was already there, in `LinearPMap/Closed.lean`.  Everything
else the migration needed existed.

## Method, and how it misfires

Bottom-up, one predicate or definition family per commit: retype the definition,
`lake build`, and at every `Application type mismatch ... but is expected to have
type ?m →ₗ.[?m] ?m` append `.toLinearPMap` to the reported argument; at every
`Invalid field` rewrite the projection.  The compiler names file, line and
column, so a throwaway patcher driven by the build log converges in four to eight
rebuild rounds per step.  Do **not** keep such a script: it is a one-off, and

**it is blunt.**  Three failure modes cost real time here:

* it rewrote `R.toLinearMap` where `R` was a `ContinuousLinearMap`, silently
  breaking a file with nothing to do with the migration.  Restore that file from
  git and redo it by hand; do not patch the patch.
* a regex deleting structure fields by name deleted them from an *unrelated*
  structure that had fields with the same names.
* `Invalid field` errors report the column of the receiver and Lean counts
  codepoints, so matching at the exact column silently does nothing about half
  the time.  Rewrite the whole reported line instead.

Each produced a green-looking edit that broke something else, and each was caught
only by the next full build.  Also: `lake build Challenge` and
`lake build DavisKahan.Audits.All` before every commit — neither is in
`defaultTargets`, and step 1 broke the `Challenge` leaderboard while a fully
green default build said nothing.

## Size, for calibration

Occurrences of the bundle outside its complexification namespace, by area, at the
point where steps 1 and 2 were done and step 3 began:

```text
SpectralTheory 359   Sources 270   SinTheta 154   Sylvester 123
Specialized 23   TanTheta 26   DoubleAngle 18   TanTwoTheta 8
Interop 8   InfiniteDimensional 4   OperatorIdeal 1
```

Step 3 removed all of them, in one working session.

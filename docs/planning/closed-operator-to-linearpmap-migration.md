# `DavisKahanExt.ClosedOperator` → `LinearPMap`: state and remaining steps

**Status 2026-08-27: in progress, steps 1 and 2 landed.**

`AGENTS.md` closes the representation question: the canonical carrier for an
unbounded operator is Mathlib's `LinearPMap`, with closedness, dense domain,
symmetry, and self-adjointness as *properties*; the bundled DKPS
`ClosedOperator` is a temporary compatibility adapter. This file records how far
that migration has got and what the next commits are, so the next agent does not
have to re-derive the order.

## What the bundle actually is

```lean
structure ClosedOperator where
  domain : Submodule 𝕜 E
  toLinearMap : domain →ₗ[𝕜] E
  dense_domain : Dense (domain : Set E)
  closed_graph : IsClosed (Set.range fun x : domain => ((x : E), toLinearMap x))
```

It is a `LinearPMap` plus two properties, and **almost every declaration in
`SpectralTheory/ClosedOperator/Basic.lean` is already an `abbrev` forwarding to
`TauCeti.LinearPMap.*` at `A.toLinearPMap`** — `SameDomain`, `MapsDomainTo`,
`BoundedExtension`, `Extends`, `IsSymmetric`, `IsSelfAdjoint`, `graphNorm`,
`RelativelyBounded`, `realResolventSet`, `realSpectrum`, `SpectralSetsSeparated`.
So the mathematics does not move. What moves is *signatures*, and the work is
almost entirely mechanical:

| before | after |
| --- | --- |
| `(A : ...ClosedOperator (𝕜 := 𝕜) (E := E))` | `(A : E →ₗ.[𝕜] E)` |
| `A.toLinearPMap` | `A` |
| `A.toLinearMap x` | `A x` |
| `A.dense_domain` | a `(hA : Dense (A.domain : Set E))` hypothesis |
| `A.closed_graph` | a `(hA : A.IsClosed)` hypothesis |
| `A.IsSelfAdjoint` | `IsSelfAdjoint A` (reducibly the same) |

The last two rows are the only ones that need judgement: most generic statements
never use density or closedness at all, and gain no hypothesis.

## Method that worked

Do it bottom-up, one predicate/definition family per commit:

1. retype the definition to take raw partial maps;
2. `lake build`, and at every `Application type mismatch ... but is expected to
   have type ?m →ₗ.[?m] ?m`, append `.toLinearPMap` to the reported argument.
   The compiler names file, line and column, so this is scriptable — a throwaway
   twenty-line patcher driven by the build log converged in four to eight
   rebuild rounds per step. Do **not** keep such a script; it is a one-off.
3. `lake build Challenge` and `lake build DavisKahan.Audits.All` before
   committing. Neither is in `defaultTargets`, and both hold statements that
   mirror migrated signatures. Step 1 broke the `Challenge` leaderboard and a
   fully green default build said nothing.

Each `.toLinearPMap` inserted this way is the temporary adapter, and its count is
the honest progress measure: **413 before the campaign, 774 now.** It goes down,
not up, once the *producers* below are migrated; the current rise is the cost of
having migrated consumers first.

## Landed

* **Step 1 — the gap predicates.** `FormBoundedSylvesterGap`,
  `RealSpectrumIntervalExteriorGap`, `SpectralSylvesterGap` and
  `SpectralIntervalExteriorGap` take raw partial maps. Four predicates collapsed
  to two (`UnboundedSylvesterGapPMap` and `UnboundedIntervalExteriorGapPMap` had
  become verbatim copies), and six duplicate `trial*`/`complement*` constructors
  to three. `realSpectrum_eq_spectraSpectrum` and
  `mem_realResolventSet_iff_mem_spectraResolvent` moved with them.
* **Step 2 — the Sylvester equation and semibounds.** `SemiboundedBelow`,
  `SemiboundedAbove`, `ClosedSylvesterEquation`, `HasClosedSylvesterEquation` and
  `HasBoundedEverywhereInverse` are gone; consumers name the canonical
  `TauCeti.LinearPMap` predicates. `equation_toLinearMap` became
  `SylvesterEquation.equation_of_mem` over raw partial maps.

## Remaining, in dependency order

3. **The producers.** These are what keep the bundle alive downstream, and they
   are the next commits because every one of them removes adapters rather than
   adding them:
   * `selfAdjointSpectralRestriction` (103 uses) is
     `closedOperatorOfSelfAdjointPMap (LinearPMap.specRestrict hA B hB) _`, so
     its body is already a partial map. **Retyping it was attempted and reverted
     on 2026-08-27**, because it is not separable from the two items below it:
     the sine-theta data records hold its result in a `ClosedOperator` field, and
     `semibounded_of_spectrum_subset_Icc` →
     `exists_boundedRealization_of_spectrum_subset_Icc` → `BoundedRealization`
     carry the bundle all the way into `SpectralTheory/FormMethod/**`. Do this
     one *together with* steps 4 and the `BoundedRealization` layer, not before
     them. Two facts learned there are worth keeping: `selfAdjointSpectralSubspace`
     and `specRange` are definitionally equal so the retype elaborates, and a
     consumer that genuinely still needs the bundle can wrap with
     `closedOperatorOfSelfAdjointPMap`, which is the adapter in the correct
     direction.
   * `realSelfAdjointSpectralRestriction` (41), `reducingRestriction` (45),
     `ClosedOperator.addBounded` (174), `ClosedOperator.ofBounded` (121).
     `(ofBounded A).toLinearPMap = A.toLinearMap.toPMap ⊤` by `rfl` already.
4. **The unbounded sine-theta core.** `SinTheta/Unbounded/Core.lean` carries both
   `UnboundedSinThetaData` (bundled) and `UnboundedSinThetaDataPMap` (raw) with
   conversions in both directions. Migrate the consumers to the raw record and
   delete the bundled one; this is the single largest reduction in the
   `SinTheta/**` and `Sources/**` counts.
5. **Tangent, double-angle and source-facing remnants**, then
   `Specialized/FreeBeam/**`.
6. **Delete `DavisKahan/Interop/TauCeti/ClosedOperator.lean`** — its only export,
   `ClosedOperator.ofLinearPMap`, has one consumer,
   `UnboundedSinThetaDataPMap.toClosed`, which step 4 removes — and then
   `DavisKahan/SpectralTheory/ClosedOperator/**` itself.

## Size

Occurrences of the bundle outside `ClosedOperatorComplexification`, by area, at
the end of step 2:

```text
SpectralTheory 359   Sources 270   SinTheta 154   Sylvester 123
Specialized 23   TanTheta 26   DoubleAngle 18   TanTwoTheta 8
Interop 8   InfiniteDimensional 4   OperatorIdeal 1
```

`ClosedOperatorComplexification` (113 further mentions in
`SpectralTheory/Real/SpectralRestriction.lean`) is a namespace prefix, not the
carrier; it migrates with step 3.

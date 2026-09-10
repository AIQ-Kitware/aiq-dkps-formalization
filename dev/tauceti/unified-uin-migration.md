# Unified UIN / Majorization migration

> Historical record. This records the original, uncompiled UIN overlay. Opus later repaired it in commit 59003c6b; this report is not the current validation record.
> See [the current migration notes](remaining-roadmap-migration.md) for the revised port.

## Status

Unverified full-file source migration against `143a43f06c93b18f610cce4a6f25cafef20f5ddf`. Lean and Lake are not installed
in the execution environment. Every attempted `lake build` stopped before compilation
with `lake: command not found`. This is not a declaration that Closure 2 is complete.

The previous compiler certification of the supplied snapshot does not certify these
changes. In particular, the new inherited-field constructors and all downstream
elaboration still require the build sequence below.

## Canonical interface

`TauCeti.UnitarilyInvariantSeminorm 𝕜 E F` extends
`Seminorm 𝕜 (E →ₗ[𝕜] F)` and adds independent raw-unitary invariance
on the codomain and domain. Square operators use `E = F`. There is one `FunLike`
instance and one `SeminormClass` instance for this structure.

Nine surviving constructor sites supply `toSeminorm` using `Seminorm.of` and the
unitary field. The parent construction derives the zero and negation laws from
subadditivity and absolute homogeneity. The former square `opNorm` constructor
and the square/rectangular norm conversions are removed.

One `TauCeti.kyFanSum` is defined on rectangular maps as a sum over `Fin k`.
`kyFanSum_eq_sum_range` supplies the equal natural-number range formula in the
roadmap; there is no second prefix-sum definition. Its triangle inequality,
scaling laws, adjoint law, and variational witnesses are rectangular.

One Frobenius constructor lives in `UnitarilyInvariantSeminorm.Instances`.
`frobenius_apply` uses the standard domain basis; `frobenius_apply_basis` and
`frobenius_sq` accept an arbitrary finite orthonormal domain basis.

`apply_operatorAbs` and the diagonal symmetric-gauge representation specialize
the same structure to endomorphisms. This is the roadmap's square scope for
modulus evaluation, not a separate square norm abstraction. Genuine adjoint
and isometric transport between different map spaces remains available.

## Majorization and dependency direction

Rectangular singular-value prefix domination implies membership in the convex
hull of the two-sided unitary orbit. The orbit certificate bounds every seminorm
of the canonical structure. `kyFanSum_le_iff_forall_seminorm` proves the converse
by selecting each concrete Ky Fan seminorm. This preserves the link between
vector majorization, Ky Fan dominance, and comparison in all UINs.

`ZeroExtension` and `DiagonalOperator` contain operator constructions, not norm
structures. Scalar and variational singular-value facts live in `KyFan`.
Approximation-number modules import that norm-free layer rather than a UIN
constructor merely to prove the triangle inequality.

The generalization of `singularValues_comp_le'` removes its incidental square
restriction on the map being precomposed. Its right factor remains an
endomorphism of the domain, as required by the fixed-map-space ideal property.

Local real-module instances remain local. The closure-1 CFC, modulus, polar,
spectral-order, and real-complexification implementation files are unchanged.

## Consumer migration and regression examples

Active ForTauCeti, Davis--Kahan, YWS, source presentation, exploration, and
challenge references use the canonical type and names. No intentional change
is made to the Davis--Kahan/YWS spectral-gap, residual, or subspace hypotheses.
The source census's live declaration references are updated; its dated historical
narrative is retained.

`RoadmapBridge.Integration` exercises the parent `Seminorm`, all inherited laws,
raw-unitary invariance, rectangular Ky Fan subadditivity and Fan equivalence,
modulus evaluation, basis-independent Frobenius evaluation, Schatten-2, and
finite Hilbert--Schmidt energy. These examples have not been compiled here.

## Static validation

- The maintained source import graph has 1,090 modules, no cycles, and no missing
  internal import targets. The repository import-policy checker passes.
- The old square/rectangular type names, conversion names, and
  `rectangularKyFanSum` have no remaining references in the active Lean packages.
- No new `sorry`, `admit`, or `axiom` declarations were introduced. Existing
  challenge placeholders remain; this is not a claim that the whole repository
  contains no placeholders.
- `git diff --check` passes. No changed or newly moved Lean line exceeds 100
  characters. Pre-existing long lines outside the edited expressions are retained.
- The declaration-name gate remains red with the same 21 findings as the supplied
  baseline, with no added findings after the census migration. These are existing
  references in `dev/production-namespace-migration-map.json`.
- Submission-ladder module lists and counts were refreshed from the import graph.
  Its checker is not green: 109 modules remain outside the seeded ladder, the same
  set as in the supplied baseline. The broader topic-assignment debt is not closed.

Static checks do not establish Lean elaboration, proof correctness, absence of
unused simp arguments, or source-signature conformance. Those remain compiler gates.

## Deletions

Remove these tracked files after extracting the overlay:

- `ForTauCeti/Analysis/InnerProductSpace/RectangularUnitarilyInvariantSeminorm.lean`
- `ForTauCeti/Analysis/InnerProductSpace/RectangularUnitarilyInvariantSeminorm/Basic.lean`
- `ForTauCeti/Analysis/InnerProductSpace/RectangularUnitarilyInvariantSeminorm/Majorization.lean`
- `ForTauCeti/Analysis/InnerProductSpace/RectangularUnitarilyInvariantSeminorm/BlockSum.lean`
- `ForTauCeti/Analysis/InnerProductSpace/RectangularUnitarilyInvariantSeminorm/Instances.lean`
- `DavisKahan/FiniteDimensional/Norms/Rectangular.lean`

## Required build sequence

```bash
lake build \
  ForTauCeti.Analysis.InnerProductSpace.ZeroExtension \
  ForTauCeti.Analysis.InnerProductSpace.KyFan \
  ForTauCeti.Analysis.InnerProductSpace.DiagonalOperator
lake build \
  ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm \
  ForTauCeti.Analysis.InnerProductSpace.SchattenNorm \
  ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.KyFan
lake build ForTauCeti
lake build RoadmapBridge
lake build DavisKahan.All
lake build DavisKahan.Explorations.SourceUnitaryInvariantNormFanDominance
lake build YuWangSamworth2015
lake build Challenge
lake build
```

The exploration and challenge targets are explicit because ordinary aggregate
builds do not necessarily include them. Do not mark the closure green or commit
it as completed before all affected builds and warning checks succeed.

# Roadmap ↔ topic map

**Internal bookkeeping. Not part of the roadmap family, and not written for a Tau Ceti
reviewer.**

`internal/candidate-topic-design.md` partitions every `ForTauCeti` module into fine-grained
topic keys. This file says which roadmap directory owns which keys, and
`scripts/check_tauceti_roadmap_topics.py` reads it: the gate fails on a topic no roadmap
claims, a topic two roadmaps claim, a roadmap directory that claims nothing, or a cycle in
the resulting roadmap-level dependency graph.

The map lives here rather than in the roadmap READMEs so that the READMEs stay ordinary
mathematical prose. Topic keys are internal identifiers; they carry no meaning for a reader
of the specification and appear nowhere in it.

Keys are stable and are never renumbered — a key's *number* records when it was introduced,
not its place in the ladder. `T23` is the clearest case: it was split out of `T15c` and sits
between `T15c` and `T16` in submission order.

| roadmap directory | topics |
|---|---|
| `OperatorTheory/PolarDecomposition` | T01 T02 T03 T26 |
| `OperatorTheory/Majorization` | T05 T07 |
| `OperatorTheory/PrincipalAngles` | T04 T06 T08 |
| `OperatorTheory/SelfAdjointSpectralTheory` | T13 T14 T15a T15b T15c |
| `OperatorTheory/OperatorIdeals` | T09 T10 T11 |
| `OperatorTheory/SpectralSubspacePerturbation` | T12 T16 T17 T18 |
| `OperatorTheory/MatrixSpectralStatistics` | T19 T20 T21 |
| `BergeMaximumTheorem` | T22 |
| `(delivered, not roadmapped)` | T23 T24 T25 |

## Delivered, not roadmapped

`(delivered, not roadmapped)` is a reserved row, not a directory. Its topics are proved in
`ForTauCeti` and no roadmap proposes them, so they stay out of the roadmap dependency graph
rather than being attached to a roadmap whose mathematics does not cover them.

| topic | modules | why it is not proposed |
|---|---|---|
| T23 | `Analysis.OperatorIdeal.ApproximationNumber.{GramSpectralRank, FinitePVMSelection, GramBandPolar}` | the ingredients of the unbounded spectral-band approximation-number theorem; the theorem itself is not proved, and the bounded cutoff bound it would generalize is already `ApproximationNumber.MinMax` |
| T24 | `Analysis.OperatorIdeal.ApproximationNumber.MinMaxReal` | the real min-max by complexification; its only consumers are `DavisKahan/**` |
| T25 | `Analysis.InnerProductSpace.{HilbertSchmidt.Block, Sylvester.BlockEstimate, Sylvester.BlockIdentity, Sylvester.Generator, Sylvester.Group, Sylvester.SpectralGap}` | the Hilbert--Schmidt Sylvester flow, whose unbounded endpoint is not proved; the bounded `sin Θ` theory does not import it |

## Why `T04` was split

`T04` mixed two layers. `Gram.Matrix`, `OrthogonalSeries`, `Projection.Geometry` and
`ReducingSubspace` import nothing above `T01`; `Projection.Blocks`, `Projection.Gap`,
`Spectral.Gap` and `Spectral.Subspace` import `T04` itself and belong with the angle layer.
Keeping them together forced `Majorization` to depend on `PrincipalAngles` — `KyFan` uses
`Orthonormal.norm_sq_starProjection_span_image` and
`RectangularUnitarilyInvariantSeminorm.Basic` uses
`exists_linearIsometryEquiv_map_eq_of_inner_eq` — while `PrincipalAngles` depends on
`Majorization` seven ways. `T26` carries the foundational half to `PolarDecomposition` and
the cycle is gone.

## Why `T23` is owned by `OperatorIdeals`

`Analysis.OperatorIdeal.ApproximationNumber.{GramSpectralRank, FinitePVMSelection,
GramBandPolar}` compute approximation numbers and finite ranks of spectral bands. They were
filed under `T15c` because they import the unbounded spectral measure, and that import made
the *spectral theory* roadmap look like a consumer of the *operator ideal* roadmap — the
edge ran the wrong way round for the mathematics.

Measured: those three modules are the sole source of the `T15c → T09` and `T15c → T02`
edges, and nothing outside the three imports any of them. Splitting them off as `T23` and
giving them to `OperatorIdeals` leaves `SelfAdjointSpectralTheory` depending only on
`PolarDecomposition`, which is what its mathematics says. No Lean module moved.

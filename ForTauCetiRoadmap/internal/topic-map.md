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
| `HilbertSpaceOperatorTheory/HilbertSpaceOperatorFoundations` | T01 T02 T03 T04 |
| `HilbertSpaceOperatorTheory/MajorizationAndAngles` | T05 T06 T07 T08 |
| `HilbertSpaceOperatorTheory/SelfAdjointSpectralTheory` | T13 T14 T15a T15b T15c |
| `HilbertSpaceOperatorTheory/OperatorIdeals` | T09 T10 T11 T23 |
| `HilbertSpaceOperatorTheory/SpectralSubspacePerturbation` | T12 T16 T17 T18 |
| `HilbertSpaceOperatorTheory/MatrixSpectralStatistics` | T19 T20 T21 T22 |

## Why `T23` is owned by `OperatorIdeals`

`Analysis.OperatorIdeal.ApproximationNumber.{GramSpectralRank, FinitePVMSelection,
GramBandPolar}` compute approximation numbers and finite ranks of spectral bands. They were
filed under `T15c` because they import the unbounded spectral measure, and that import made
the *spectral theory* roadmap look like a consumer of the *operator ideal* roadmap — the
edge ran the wrong way round for the mathematics.

Measured: those three modules are the sole source of the `T15c → T09` and `T15c → T02`
edges, and nothing outside the three imports any of them. Splitting them off as `T23` and
giving them to `OperatorIdeals` leaves `SelfAdjointSpectralTheory` depending only on
`HilbertSpaceOperatorFoundations`, which is what its mathematics says. No Lean module moved.

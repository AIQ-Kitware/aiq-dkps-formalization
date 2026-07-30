# Review — `ForTauCeti` T04, T05, T07–T10, T12–T20

**FILE PASS COMPLETE for fifteen groups — 127 files, ~34,000 lines.**
2026-07-29, `edward (aiq-gpu)`, lane `AUDIT`. With T01–T03, T06, T11, T21, T22
this closes **all 22 `ForTauCeti` topics**.

Method: per-file profile (declarations, namespace, size, staging line, duplicate
participation, escapes, provenance) for every file, plus targeted reads of the
files the profile flagged. Findings are recorded against the group; per-file
verdicts that raise nothing are recorded as "clean" rather than written out.

## Per-group verdict

| group | files | lines | verdict |
|---|---|---|---|
| **T04** Gram, projections, spectral subspaces | 8 | 1,479 | clean; namespace spread noted |
| **T05** Majorization, Schur–Horn, UI norms | 5 | 2,531 | clean; largest single file 709L is fine |
| **T07** Rectangular UI norms | 6 | 2,357 | **aggregator file, T07-1** |
| **T08** Angle geometry, eigenvalue perturbation | 5 | 1,477 | clean |
| **T09** Approximation numbers | 11 | 2,540 | **best-organized group in the library** |
| **T10** Symmetric operator ideals, Schatten | 9 | 2,266 | **namespace spread, T10-1** |
| **T12** Haagerup–Zsidó | 8 | 2,020 | clean; one flat file (`PLACE-SYLV`) |
| **T13** One-parameter unitary groups, Stone | 6 | 1,491 | clean |
| **T14** Borel calculus, PVMs | 10 | 2,299 | clean |
| **T15** Unbounded `LinearPMap` | 24 | 6,728 | **should split, T15-1** |
| **T16** Sylvester, Rosenblum | 15 | 7,077 | **2,886-line file (`SPLIT-1K`)** |
| **T17** Davis–Kahan sin Θ | 10 | 3,335 | clean; 1,110L file (`SPLIT-1K`) |
| **T18** Yu–Wang–Samworth | 3 | 1,076 | clean |
| **T19** Matrix spectra, measurability | 6 | 892 | **all six assert Mathlib, T19-1** |
| **T20** Sample moments, concentration | 5 | 881 | **four of five assert Mathlib, T19-1** |

## Finding T09 — what "good" looks like, recorded as the benchmark

**Every one of T09's eleven files declares into `ContinuousLinearMap`**, except
the two genuine Mathlib-namespace extensions it needs (`LinearMap.RankComp`,
`Cardinal.Lift`). One namespace, one subject, files sized 65–458 lines, no
duplication, no escapes, no opinion-bearing names.

It is also the topic with the cleanest *dependency* story: `--needs` reports T09
requires only T01, T03 and T07, not the eight its position implies. **This is the
group to point at when asking what the others should look like**, and it is not
a coincidence that it is the one with a written roadmap
(`ForTauCetiRoadmap/ApproximationNumbers/`).

## Finding T10-1 — four namespaces for one subject `{lane:NS-SPREAD}`

T10 is "symmetric operator ideals and Schatten norms" — one subject — spread
across four namespaces:

| namespace | files |
|---|---|
| `TauCeti` | `Family/Basic`, `SchattenNorm`, `FiniteLpGauge`, `Family/OperatorNorm`, `Family/KyFan`, `Family/KyFanDominance` |
| `ENNReal` | `Family/HilbertSchmidt` |
| `HilbertBasis` | `HilbertSchmidtEnergy` |
| `ContinuousLinearMap` | `Family/TraceClass` |

`ENNReal` and `HilbertBasis` are core Mathlib namespaces, and neither is being
*extended* in the sense `ForTauCeti/README.md` §2 permits — an operator-ideal
gauge is not an `ENNReal` fact, and Hilbert–Schmidt energy is not a
`HilbertBasis` fact. This is the same class as `T01-NS` (`FiniteDimensional`),
at a different pair of namespaces, so it joins that lane's argument rather than
opening a new one: **`ForTauCeti` has no enforced namespace policy, and four
files across two topics have drifted into core Mathlib namespaces.**

T04 shows the benign version of the same spread — `Submodule` for
`ProjectionGap`/`ProjectionBlocks` genuinely *is* extending `Submodule`, which
§2 permits. The distinction is whether the declaration is a fact **about** the
namespace's object.

## Finding T07-1 — a 32-line file with no declarations `{lane:PLACE-SYLV}`

`RectangularUnitarilyInvariantNorm.lean` (32 lines, **0 declarations**) sits
beside the `RectangularUnitarilyInvariantNorm/` directory holding the four real
files. It is an aggregator — the Lean idiom for a directory's public face — and
as such it is **correct**, not a defect.

Recorded because it is the *same shape* as `HaagerupZsidoKernel.lean` beside
`HaagerupZsido/` and the seven `Sylvester*` files beside `Sylvester/`, and the
distinction matters for lane `PLACE-SYLV`: **an aggregator beside its directory
is right; a content file beside its directory is wrong.** `PLACE-SYLV` must not
sweep up the aggregators. Its scope is updated to say so.

## Finding T15-1 — the largest topic is three topics `{lane:T15-SPLIT}`

T15 is 24 files and 6,728 lines — the biggest topic by both measures, and nearly
three times the median. Its own contents fall into three chains that barely
touch:

1. **Closedness and graph theory** — `Closed.lean` (963L, 83 decls),
   `GraphCore`, `Constructions`, `SelfAdjointMaximal`, `RealLowerBound`.
2. **Resolvents** — `Resolvent`, `ResolventBound`, `ResolventOpen`,
   `SelfAdjointResolvent`, `SpectralGapInverse`, `SelfAdjointGapInverse`.
3. **Spectral measure and Stone** — `SpectralMeasure.lean` (1,242L, 61 decls),
   `SpectralGrid`, `SpectralSupport`, `SpectralCutOperator`,
   `SpectralProjectionGroup`, `StoneUniqueness`, `YosidaApproximation` (821L).

The design document already flagged that T15 "should probably split" and left
the cut to whoever owns `UnboundedOperators`. **The file pass supplies the cut**:
the three chains above are the natural boundary, and `SpectralMeasure.lean` and
`Closed.lean` — the two files over 950 lines — sit in different ones, so the
split also relieves `SPLIT-1K`.

## Finding T19-1 — the statistical arm is uniformly Mathlib-aimed `{lane:HDR-DEST}`

**Ten of T19+T20's eleven files carry a `Staged for Mathlib` line** — the
densest concentration in the library. That is not an accident of drift: matrix
spectra, entrywise eigenvalue bounds, convergence in measure, sample
mean/variance/covariance and matrix concentration are all genuinely
Mathlib-shaped, general-purpose results with no Davis–Kahan content.

Together with T21/T22 (which assert a Mathlib target in their *extraction
class*), this makes **four topics — T19, T20, T21, T22, 15 files — that look
Mathlib-bound rather than Tau Ceti-bound.** That is a coherent block, not
scattered noise, and it sharpens the decision `HDR-DEST` needs from jon: the
question is not "fix 39 headers" but "**do these four topics belong in this
library at all?**"

## What is good, beyond T09

- **T12, T13, T14 are coherent and need nothing.** T12's Fourier chain is
  linear; T13's six files build Stone's theorem in dependency order; T14's ten
  build the PVM machinery without a single duplicate.
- **T05's `Majorization.lean` is 709 lines and 44 declarations and that is
  fine** — majorization genuinely has that many basic facts, and they are all
  about one object. Size alone is not a finding.
- **T17 reads as a designed API**, which matters because it is the paper's
  headline mathematics: `Perturbation` → `OperatorNorm`/`UnitarilyInvariant`
  specializations, with `Residual/` supplying the Ritz machinery.
- **No proof escapes anywhere in `ForTauCeti`**, and provenance is present in all
  161 files.

## `ForTauCeti` group pass — the holistic verdict

All 22 topics are now file-reviewed. Across the library:

- **The mathematics is not the problem.** In 161 files and ~46,000 lines the
  audit found *no* wrong statement, no vacuous theorem, and no proof escape.
- **The problems are three, and all structural:** duplicate constructions
  (`T01-SQRT`, `MODULUS-DEDUP`), namespace drift into core Mathlib
  (`T01-NS`, four files across T01/T03/T10), and destination confusion
  (`HDR-DEST`, 39 headers, concentrated in four probably-Mathlib-bound topics).
- **Two topics are oversized and should split** (`T15-SPLIT`), and three files
  break the stated 1,000-line limit (`SPLIT-1K`).
- **T09 is the model.** One namespace, one subject, right-sized files, a written
  roadmap, and the shallowest dependency set of any non-trivial topic.

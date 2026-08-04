# Candidate roadmap topic design for Tau Ceti

This internal design partitions all **187** `ForTauCeti` modules into **25 stable topic
keys**, including the `T15a`/`T15b`/`T15c` split and the later `T23` spectral-band bridge.
The keys are dependency-sized implementation stages; the public specification groups them
into six roadmaps under `HilbertSpaceOperatorTheory/`.

Roadmap ownership is declared in [`topic-map.md`](topic-map.md), not in public roadmap prose.
The checker validates both the module partition and the roadmap-level DAG:

```sh
python3 scripts/check_tauceti_roadmap_topics.py          # report
python3 scripts/check_tauceti_roadmap_topics.py --check  # exit 1 on any violation
python3 scripts/check_tauceti_roadmap_topics.py --topic T15c
python3 scripts/check_tauceti_roadmap_topics.py --roadmaps
```

## Why a new design was needed

The existing ladder (`dev/tauceti/submission-ladder.md`, rungs A–F) puts **41 of
160** modules on a submission path. The other **119 have none** — including all
17 Davis–Kahan sin-Θ modules, which are the mathematics this project exists to
contribute. And only four roadmap directories exist, covering perhaps a third of
the library.

Against the readiness standard — `ForTauCeti` should already satisfy the
*platonic ideal* Tau Ceti roadmap — you cannot claim readiness for a roadmap
that does not cover the library. So the first job is a **total** partition.

## What the design guarantees

The checker enforces three properties. Each is here because the draft violated it:

- **Total.** Every module is assigned. Adding a module without assigning it
  fails `--check`. A design that quietly omits modules is exactly how 119 ended
  up unplaced.
- **Disjoint.** No module in two topics.
- **Acyclic in submission order.** No module imports anything in a *later*
  topic. This is the property that makes a topic submittable at all: a forward
  reference means the PR cannot compile against what Tau Ceti has accepted so far.

**Draft 1 had 24 forward references. Draft 2 had 12. This one has 0.** Every fix
was a fact about the mathematics, not bookkeeping — see *What the violations
taught us*.

## The ladder

Sizes are module counts. **"Needs" is derived from the import graph, not
asserted** — it is the exact set of topics a reviewer must already have accepted,
printed by the checker.

| # | Topic | n | Needs |
|---|---|---:|---|
| **T01** | Positive square root, operator modulus, functional calculus | 9 | **— independent** |
| **T02** | Polar decomposition and partial isometries | 6 | T01 |
| **T03** | Singular values and the singular system | 4 | T01 |
| **T04** | Gram matrices, orthogonal projections, and spectral subspaces | 8 | T01 |
| **T05** | Majorization, Schur–Horn, and unitarily invariant norms | 5 | T01, T02, T04 |
| **T06** | Principal angles, aligned bases, and finite frames | 3 | T03, T04, T05 |
| **T07** | Rectangular unitarily invariant norms | 6 | T03, T04, T05, T06 |
| **T08** | Angle geometry and eigenvalue perturbation | 5 | T01, T02, T04, T05, T06, T07 |
| **T09** | Approximation numbers | 21 | T01, T03, T05, T07 |
| **T10** | Symmetric operator ideals and Schatten norms | 12 | T03, T05, T07, T09 |
| **T11** | Hilbert–Schmidt operators | 4 | T10 |
| **T12** | The Haagerup–Zsidó kernel and its Fourier transform | 8 | **— independent** |
| **T13** | One-parameter unitary groups and Stone's theorem | 5 | **— independent** |
| **T14** | Borel functional calculus and projection-valued measures | 11 | **— independent** |
| **T15a** | Closed operators on `LinearPMap`: graphs, constructions, form bounds | 7 | T04 |
| **T15b** | Resolvents of self-adjoint `LinearPMap` operators, semiboundedness | 7 | **— independent** |
| **T15c** | The spectral measure of an unbounded self-adjoint operator, and Stone | 12 | T13, T14, T15b |
| **T23** | Approximation numbers and finite ranks of spectral bands | 3 | T02, T09, T15a, T15c |
| **T16** | Sylvester equations and the Rosenblum theorem | 18 | T04, T07, T11, T12, T13, T15b, T15c |
| **T17** | Spectral subspace perturbation: the Davis–Kahan sin-Θ theorems | 15 | T01, T03–T09, T15a, T16 |
| **T18** | The Yu–Wang–Samworth statistical variant | 3 | T01, T05, T06, T08, T17 |
| **T19** | Matrix spectra and spectral measurability | 6 | T01, T14 |
| **T20** | Sample moments and matrix concentration | 5 | T19 |
| **T21** | Matrix rank factorization and positive semidefiniteness | 2 | **— independent** |
| **T22** | Berge's maximum theorem and approximate minimizers | 2 | **— independent** |

**187 modules.** The table is generated from
`scripts/check_tauceti_roadmap_topics.py --needs`; do not edit its counts or dependency
column by hand. `T23` separates three approximation-number consequences of spectral bands
from the foundational spectral-measure topic. This preserves the intrinsic ownership
boundary: self-adjoint spectral theory no longer depends on operator ideals, while the
operator-ideal roadmap explicitly consumes the spectral theory needed to prove those
consequences.

**This is a DAG, not a chain — that is the most useful property of the design.**
The numbering is *a* valid submission order, but it is not the only one, and
several topics need far less than their position suggests:

- **Seven topics are fully independent** and can go first, in any order or at
  once: **T01**, **T12** (Haagerup–Zsidó, 8 modules), **T13** (Stone, 5),
  **T14** (Borel calculus and PVMs, 11), **T15b** (resolvents of self-adjoint
  partial maps, 7), and the two ex-`ForMathlib` pairs **T21** and **T22**.
  Two of those seven are new since the design was written, and both are worth
  noticing: `T13` shed its `T02` dependency, and the `T15` split exposed `T15b`,
  which had been buried inside a 24-module block that looked like it needed
  everything.
- **T09, approximation numbers — the advertised PR1 topic — needs T01, T03, T05
  and T07**, not the eight topics its position implies. The `T05` entry is new:
  majorization joined the closure as the Ky Fan layer grew, and the earlier
  claim of *"only T01, T03 and T07"* no longer holds. It is a small correction
  in submission terms — `T05` is 5 modules and already sits below `T07` — but a
  reviewer checking the sentence would have found it false.
- **T13 needs nothing at all**, where this document previously said it needs
  `T02`. Stone's theorem does not wait on the polar decomposition either.
- **T19/T20 are a near-independent statistical arm**, reachable via T14 alone.

Three observations worth arguing about:

- **T17 is the endpoint, and its transitive depth is real.** It needs T15a and
  T16, and through them most of the library — note it needs only the *first*
  slice of the old T15 directly, though T16 pulls in T15b and T15c. That is the honest cost of
  submitting Davis–Kahan as reusable mathematics rather than as one paper's
  formalization. The lever for getting sin-Θ upstream sooner is not reordering —
  it is finding out which of T01–T16 Tau Ceti already has.
- **T12 and T14 are the cheapest real submissions** and both are independent.
  Either is a good first contact with Tau Ceti review, where the thing being
  tested is the *process* rather than the mathematics.
- ~~**T15 is 24 modules and should probably split** before submission. It is left
  whole here because its internal cut is a mathematical judgement (resolvents /
  spectral measure / Stone) belonging to whoever owns `UnboundedOperators`.~~
  **SPLIT 2026-07-29 (lane T15-SPLIT, `jon (yardrat)`), and the judgement was
  made rather than deferred:**

  | key | modules | contents |
  |---|---|---|
  | `T15a` | 6 | closed operators on `LinearPMap`: graphs, constructions, the domain-aware Sylvester equation, and quadratic-form bounds |
  | `T15b` | 7 | resolvents of self-adjoint `LinearPMap` operators, semiboundedness, and the gap inverse |
  | `T15c` | 12 | the spectral measure, spectral projections, maximality, Stone uniqueness, and Yosida |

  **Keys are suffixed, not renumbered.** Pushing T16–T22 up would invalidate every
  `Txx` reference in the audit files, in this document and in the written
  roadmaps, for no gain.

  **The import graph moved three modules across the cut the audit proposed**, and
  that is the part worth keeping: `RealLowerBound` imports `SelfAdjointResolvent`,
  `SelfAdjointMaximal` imports `SpectralMeasure`, and `SpectralGapInverse` imports
  `SpectralSupport`. Each therefore sits one chain *later* than its subject matter
  suggests, and `--check` reports a forward reference if they are placed by name.

  **One result the undivided topic could not have**: `--needs` now reports
  **T15b as independent of every other topic**. The unbounded resolvent theory is
  submittable on its own.

## What the violations taught us

Each fix below changed the design because the import graph contradicted the
intuition. These are the load-bearing findings.

1. **The unbounded stack is a prerequisite of the bounded Sylvester theory, not
   a sequel to it.** `Rosenblum`, `SylvesterSpectralGap` and `SylvesterGroup`
   import `LinearPMap.{Resolvent,ResolventOpen,RealLowerBound,SpectralGrid,
   SpectralProjectionGroup,StoneUniqueness}` and `OneParameterUnitaryGroup.Stone`.
   Draft 1 had Sylvester at T9 and the unbounded work at T10–T12; that ordering
   is impossible.
2. **`OneParameterUnitaryGroup` and `BorelCalculus` sit *below* `LinearPMap`,
   not above it.** Measured: `LinearPMap → OneParameterUnitaryGroup` 3 edges,
   `LinearPMap → BorelCalculus` 1 edge, and **zero** in either reverse
   direction. The unbounded area is cleanly stratified, which is why T13/T14/T15
   can be three topics instead of one 30-module lump.
3. **Subspace geometry and norm theory interleave; neither is one topic.**
   Geometry → norms had 7 edges and norms → geometry had 3, so the two are
   mutually dependent as originally drawn. The resolution is a *foundational*
   geometry layer (T04: Gram, projections, spectral subspaces), then norms
   (T05), then the geometry that needs norms (T06–T08). `KyFan` needs
   `ProjectionGeometry`; `RectangularUnitarilyInvariantNorm.Basic` needs
   `GramMatrix` and `PrincipalAngles`.
4. **The Haagerup–Zsidó kernel is not an orphan — it is a Sylvester
   prerequisite.** `Sylvester.Internal.ReciprocalMultiplier` imports
   `Analysis.Fourier.HaagerupZsidoKernel`. It was previously listed as one of
   eight modules "belonging to no roadmap at all"; it belongs to the sharp
   Sylvester constant. This is the single most useful thing the check found,
   because it converts an orphan into a dependency with a reason.

## Inconsistently placed modules, and where they should go

Found by comparing each module's path against its content and its family. **None
of these was fixed here** — they are `.lean` moves needing a build.

**A and B have since been done** (lane PLACE-SYLV, `jon (yardrat)`, 2026-07-29),
minus one file; C and D are still open. The two sections are kept as written,
each with its outcome recorded at the end.

### A. Seven `Sylvester*` modules sit beside a `Sylvester/` directory

`Analysis/InnerProductSpace/Sylvester/` already exists and holds `Basic.lean`,
`Interval.lean`, `SpectralDistance.lean` and `Internal/`. Yet seven siblings use
the flat prefix convention instead:

| now | proposed |
|---|---|
| `SylvesterBound.lean` | `Sylvester/Bound.lean` |
| `SylvesterOperator.lean` | `Sylvester/Operator.lean` |
| `SylvesterGroup.lean` | `Sylvester/Group.lean` |
| `SylvesterGenerator.lean` | `Sylvester/Generator.lean` |
| `SylvesterBlockIdentity.lean` | `Sylvester/BlockIdentity.lean` |
| `SylvesterBlockEstimate.lean` | `Sylvester/BlockEstimate.lean` |
| `SylvesterSpectralGap.lean` | `Sylvester/SpectralGap.lean` |

One family, two conventions, in one directory. This is the clearest elegance
defect in the library and it is mechanical to fix.

**DONE 2026-07-29, six of the seven** (lane PLACE-SYLV). `Bound`, `Operator`,
`Generator`, `BlockIdentity`, `BlockEstimate` and `SpectralGap` are now inside
`Sylvester/`, with every import repointed and the T16 table in
`scripts/check_tauceti_roadmap_topics.py` updated in the same commit.
**`SylvesterGroup.lean` was deliberately left flat**: `jon (namek)` holds a live
`dev/LANES.md` row on it that still reads `in progress`, and renaming a file
under an agent who is adding declarations to it is a merge collision, not a
tidy-up. It is the one move left in this section; whoever closes that row should
do it.

### B. `HaagerupZsidoKernel.lean` sits beside `HaagerupZsido/`

Same shape: `Analysis/Fourier/HaagerupZsido/` exists (`Defs`, `Fourier`,
`Integrability`) and `Analysis/Fourier/HaagerupZsidoKernel.lean` sits next to it.
Proposed: `HaagerupZsido/Kernel.lean`.

**DONE 2026-07-29** (lane PLACE-SYLV). The module is now
`Analysis/Fourier/HaagerupZsido/Kernel.lean`. Worth recording why the move was
free: that file is a *re-export aggregate* whose own docstring already told
consumers to import `ForTauCeti.Analysis.Fourier.HaagerupZsido.Kernel` — the
path it did not yet have. The move made the docstring true.

### C. `GramMatrix.lean` is misnamed, and overlaps `GramOperator.lean`

It declares into `TauCeti.LinearMap`, not `Matrix`, and its content is
kernel/range identities for linear maps with equal inner products — Gram
*operators*, not matrices. A reviewer searching for matrix results will not find
what the name promises, and a reviewer reading `GramOperator.lean` will find an
adjacent module covering related ground. **Needs a decision: rename, or merge
the two.** Recommend deciding it inside T04 rather than as a standalone rename.

**DECIDED 2026-07-29 (lane PLACE-GRAM, `jon (yardrat)`): neither. Both names
stay and the two modules stay apart** — the premise above does not survive
reading the file, and the correction is worth more than the rename would have
been.

- `GramMatrix.lean` **does** declare into `Matrix`: it opens `namespace Matrix`
  at line 201, and its headline corollary is
  `TauCeti.Matrix.gram_eq_gram_iff_exists_linearIsometryEquiv_map_eq`, stated as
  `Matrix.gram 𝕜 φ = Matrix.gram 𝕜 ψ ↔ ∃ W : E ≃ₗᵢ[𝕜] E, ∀ i, W (φ i) = ψ i`.
  What is true is that its *engine* — `LinearMap.ker_eq_ker_of_inner_eq` and
  `LinearMap.rangeEquivOfInnerEq`, an isometric first isomorphism theorem — lives
  in `LinearMap`, which is where a general fact about a pair of linear maps
  belongs. A module whose engine is general and whose headline is a matrix
  statement is well factored, not misnamed.
- The name is also the **destination**: the file imports
  `Mathlib.Analysis.InnerProductSpace.GramMatrix` and names that module as its
  intended upstream home. Renaming it here would only have to be undone at PR
  time.
- The overlap is verbal. `GramOperator.lean` is about `A⋆A` and `AA⋆` — their
  symmetry and the perturbation bound `‖Â⋆Â - A⋆A‖ ≤ (‖Â‖ + ‖A‖)‖Â - A‖` — as
  the carriers of singular-subspace theory. The two modules share no declaration
  and no notion beyond the word *Gram*. Merging a rigidity theorem about vectors
  with equal inner products into a file about singular-value carriers would
  create the defect this section is trying to remove.

The one thing a reviewer might still ask for is a sentence in `GramMatrix.lean`'s
docstring distinguishing the two senses of *Gram*. That is a docstring line, not
a placement decision, and it belongs to whoever holds the docstring lane.

### D. `CenteredScatter.lean` is statistics living under `InnerProductSpace`

It proves facts about finite means and centered scatter operators — the content
of T20, and it is assigned there. It is also **imported by nothing**, so moving
it is free. Proposed: `Probability/Moments/CenteredScatter.lean`.

**DONE 2026-07-29** (lane PLACE-GRAM). The module is now
`ForTauCeti/Probability/Moments/CenteredScatter.lean`, beside `SampleMean`,
`SampleCovariance`, `Variance` and `MatrixConcentration`, and the T20 entry in
`scripts/check_tauceti_roadmap_topics.py` follows it.
**Correction to "imported by nothing":** nothing in `ForTauCeti` imports it, but
`DkpsQuench2026/Spectral/GramSpectrum.lean` does. One import line, repointed in
the same commit — cheap, but not free, and a lane that skipped the build on the
strength of that sentence would have broken a paper library.

### E. `Analysis.Normed.Operator.LinearIsometry` is a foundation, filed late

It was drafted into the approximation-number topic; `GramMatrix` imports it, so
it must precede T04. It is assigned to T01. No file move needed — this is a
correction to the *reading* of where it belongs, not to the tree.

## What this design does not settle

- **Which topics Tau Ceti already has.** Every "needs" column here is internal.
  The first real reviewer contact should be used to find out how much of
  T01–T08 is already upstream, because that is what determines whether T17 is 14
  topics away or four.
- ~~**Whether T15 splits**, and where.~~  **Settled 2026-07-29 (lane `T15-SPLIT`):**
  into T15a (closedness and graphs), T15b (resolvents and semiboundedness) and
  T15c (the spectral measure and Stone), which is how the table above reads.  Left struck through rather than deleted,
  because the open-questions list is also a record of what got decided.
- **`M-SWITCH`** — how the clusters actually go upstream once a topic is
  accepted — is still open and still jon's call.
- **Topic names.** These are ours, not Tau Ceti's. The `tauceti-target:v1`
  markers in the existing roadmaps are provisional and none has been confirmed
  against `TauCetiRoadmap`.

## Relationship to the existing artifacts

- `dev/tauceti/submission-ladder.md` rungs A–F are **subsumed**: they are
  T01–T10 restricted to the approximation-number path. The ladder document stays
  as the narrative of why PR1 was mis-scoped; this file is the total design.
- The four existing directories map on: `ApproximationNumbers` → T09;
  `SymmetricOperatorIdeals` → T10; `UnboundedOperators` → T13–T15;
  `SpectralSubspacePerturbation` → T16–T18. **Sixteen of twenty topics have no
  roadmap directory yet**; writing them is the work this design makes possible.

## Addendum, 2026-07-29 — T21 and T22 arrived when `ForMathlib` retired

`jon (namek)` completed lane `FM-RETIRE` the same day: `ForMathlib` is **0
modules** and its last four moved here, taking `ForTauCeti` from 156 to 160.
`check_tauceti_roadmap_topics.py --check` went red on exactly the property it
exists to hold — the partition stopped being total — which is the gate working.

They are two independent pairs, mathematically unrelated to the operator theory
and to each other, so they are two topics rather than an appendix to an existing
one:

- **T21** `LinearAlgebra.Matrix.{RankFactorization, PosDef}`. Algebra-side matrix
  results. Deliberately *not* folded into T19 (`Analysis.Matrix.*`), which is the
  analysis side with a different Mathlib destination.
- **T22** `Topology.{ApproxMinimizer, Berge}`. Berge's maximum theorem — general
  topology and optimization, with no operator theory in it at all.

Both are leaves inside `ForTauCeti`: nothing in the library imports them. Their
consumers are the paper libraries (`Acharyya2024`, `Acharyya2025`) and three
`Challenge/MathlibPending/**/Leaderboard.lean` files.

**These are the two topics most plausibly bound for Mathlib rather than Tau
Ceti**, which is what the retired "genuinely Mathlib-shaped remainder" reading
was gesturing at before jon closed that question. The decision is settled — they
live in `ForTauCeti` — but if any topic here is ever *re*-aimed at Mathlib, it is
these two, and their `Challenge/MathlibPending/` directory name would then be
right rather than a misnomer.

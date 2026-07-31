# `ForTauCetiRoadmap/` — roadmap drafts for Tau Ceti

Tau Ceti admits new mathematics only against an **accepted roadmap target**, one
topic per PR. These are our drafts of those targets, written as if accepted and
mirroring the sibling `TauCetiRoadmap` layout, so that a submission arrives as a
proposal Tau Ceti recognizes rather than as a pile of files.

They are kept honest against [`../ForTauCeti/`](../ForTauCeti/README.md), the
elegant package this repository builds. A roadmap here is not aspirational: the
standard is that `ForTauCeti` should already satisfy the **platonic ideal**
version of it — the roadmap a Tau Ceti reviewer *would* write — so that whatever
is accepted, we already have what it needs. That includes paper references,
adversarial review of every statement, and Mathlib-quality elegance. See
`ForTauCeti/README.md` §*The readiness standard*.

## The shape: six roadmaps, sized like real ones

The real `TauCetiRoadmap` covers all of mathematics in fourteen roadmaps —
*Partial differential equations*, *Representation theory*, each an area with
milestones inside it. Our first cut partitioned one operator-theory library
into twenty-four single-topic directories, which is a granularity no reviewer
upstream would recognize as a roadmap. The library is now specified as **six
roadmaps**, each a coherent body of mathematics whose Parts are the fine-grained
topics of the [candidate topic design](CANDIDATE-TOPIC-DESIGN.md) (`T01`–`T22`,
with the `T15a/b/c` split). The topics survive as the module-level partition and
as PR-sized stages inside each roadmap; the roadmap is the unit a reviewer reads.

| Roadmap | Parts | Modules | Needs |
|---|---|---|---|
| [`FiniteDimensionalOperators/`](FiniteDimensionalOperators/README.md) — the functional calculus of a symmetric operator, the positive square root and modulus, polar decomposition and partial isometries, singular values and the Moore–Penrose inverse, Gram matrices, projections and spectral subspaces. The foundation everything else names. | T01–T04 | 27 | — independent |
| [`MajorizationAndAngles/`](MajorizationAndAngles/README.md) — majorization and Schur–Horn, unitarily invariant norms square and rectangular, principal angles as singular values of the overlap operator, the angle dictionary and eigenvalue perturbation. One roadmap because the import graph says so: geometry and norm theory interleave (T05 < T06 < T07 < T08). | T05–T08 | 19 | FiniteDimensionalOperators |
| [`OperatorIdeals/`](OperatorIdeals/README.md) — approximation numbers as the infinite-dimensional continuation of singular values, symmetric operator ideals and Schatten norms, and Hilbert–Schmidt operators realised as `ℓ²` of columns. | T09–T11 | 28 | FiniteDimensionalOperators, MajorizationAndAngles |
| [`SpectralTheory/`](SpectralTheory/README.md) — one-parameter unitary groups and Stone's theorem, the bounded Borel functional calculus and projection-valued measures, and the unbounded self-adjoint theory on Mathlib's `LinearPMap`: closed operators, resolvents, and the spectral measure. Opens with the representation decision the whole stack inherits. | T13, T14, T15a–c | 40 | FiniteDimensionalOperators |
| [`SpectralSubspacePerturbation/`](SpectralSubspacePerturbation/README.md) — the endpoint: the Haagerup–Zsidó kernel behind the sharp `π/2` constant, Sylvester equations and the Rosenblum theorem, the Davis–Kahan sin Θ theorems, and the Yu–Wang–Samworth statistical variant. | T12, T16–T18 | 40 | all four above |
| [`MatrixStatistics/`](MatrixStatistics/README.md) — matrix rank factorization and the MDS embedding step, Berge's maximum theorem for argmin stability, matrix spectra and spectral measurability, sample moments and matrix concentration. Its first two Parts are independent leaves. | T19–T22 | 15 | FiniteDimensionalOperators, SpectralTheory |

## The meta-roadmap: how everything reaches Tau Ceti

The six roadmaps form a DAG, and the DAG is the submission plan for
contributing everything in `ForTauCeti`. It is validated against the import
graph — run the tool rather than trusting the prose:

```sh
python3 scripts/check_tauceti_roadmap_topics.py --roadmaps   # this table, from ground truth
python3 scripts/check_tauceti_roadmap_topics.py --check      # total, disjoint, acyclic, covered
```

```text
              FiniteDimensionalOperators          (wave 1)
                 │                 │
       ┌─────────┴──────┐          │
       ▼                ▼          │
MajorizationAndAngles  SpectralTheory             (wave 2)
       │      │            │   │
       ▼      │            │   ▼
 OperatorIdeals            │  MatrixStatistics    (wave 3)
       │      │            │
       └──────┴─────┬──────┘
                    ▼
     SpectralSubspacePerturbation                 (wave 4)
```

Reading the waves:

1. **`FiniteDimensionalOperators` goes first** — it is the only roadmap with no
   prerequisite, and five of the six name it. Within wave 1 the independent
   Parts of later roadmaps are also submittable immediately: Stone's theorem,
   the Borel calculus, and the unbounded resolvent theory (`SpectralTheory`
   Parts A, B, D), the Haagerup–Zsidó kernel (`SpectralSubspacePerturbation`
   Part A), and rank factorization and Berge (`MatrixStatistics` Parts A, B).
   Those are the cheap first contacts with Tau Ceti review, where the thing
   being tested is the *process* rather than the mathematics.
2. **`MajorizationAndAngles` and `SpectralTheory` unlock in parallel** once the
   foundation is accepted; neither needs the other.
3. **`OperatorIdeals` and `MatrixStatistics`** follow their respective arms.
4. **`SpectralSubspacePerturbation` is the endpoint** and needs everything.
   That transitive depth is the honest cost of submitting Davis–Kahan as
   reusable mathematics rather than as one paper's formalization. The lever for
   getting sin Θ upstream sooner is not reordering — it is finding out which of
   the earlier roadmaps Tau Ceti already has.

What the DAG does **not** settle: which parts Tau Ceti or Mathlib already
cover (the first real reviewer contact should measure that), and how accepted
topics are packaged into PRs (`../dev/tauceti/submission-ladder.md`).

## The candidate topic design

[`CANDIDATE-TOPIC-DESIGN.md`](CANDIDATE-TOPIC-DESIGN.md) records the partition
of every `ForTauCeti` module into the fine-grained topics, ordered as a
submission ladder and validated against the import graph
(`scripts/check_tauceti_roadmap_topics.py`: total, disjoint, and acyclic in
submission order). The topic keys (`T01`…`T22`) are stable identifiers: audit
files, the checker, and the roadmap Parts all cite them, and they are never
renumbered. Each roadmap README declares the topics it covers
(`**Topic Txx of the candidate design**`), and the checker derives the
directory-to-topic map from those declarations — there is no hand-maintained
table to go stale.

## Roadmap format

Each roadmap directory holds:

- **`README.md`** — the definitive specification, written the way the real
  `TauCetiRoadmap` demands (see its *Writing a roadmap* section): motivation,
  the bar for done, a generality bar with conventions pinned up front, what
  Mathlib already has, Parts with objects / API / milestones / acceptance
  examples, dependency ordering, references, and a clearly secondary
  provenance section.
- **`Suggested.lean`** — representative target signatures for the milestones,
  with placeholder bodies, so contributors and reviewers converge on names and
  forms. The markdown stays definitive; the prototypes are neither exhaustive
  nor prescriptive about proof architecture.

## Related

- [`../dev/tauceti/submission-ladder.md`](../dev/tauceti/submission-ladder.md) —
  how the staged library slices into reviewable, dependency-closed PRs. A
  roadmap says *what* a topic is; the ladder says *what order* the PRs go in.
- [`../dev/tauceti/public-api-integration-review.md`](../dev/tauceti/public-api-integration-review.md) —
  the API-shape principles a submission is judged against: generic mathematics
  in canonical namespaces, paper numbering confined to source-facing wrappers,
  existing Tau Ceti and Mathlib vocabulary winning over repository-local wrappers.
- [`../docs/planning/upstream-readiness-audit.md`](../docs/planning/upstream-readiness-audit.md) —
  per-candidate reviewer objections and readiness ratings.

## Editing rules

- One directory per roadmap: `<Roadmap>/README.md` plus `Suggested.lean`. The
  markdown is definitive.
- **This file is an index and the meta-roadmap.** A roadmap's content belongs
  in its own directory, never here. (Until 2026-07-29 this file held a stale
  full copy of one roadmap, five passages diverged from the real one — the
  lesson is recorded so it is not relearned.)
- Specify mathematics **intrinsically**. DKPS file and identifier names belong
  in each roadmap's provenance section, not in the specification prose — a
  roadmap Tau Ceti can accept must read as mathematics, not as a migration
  checklist.

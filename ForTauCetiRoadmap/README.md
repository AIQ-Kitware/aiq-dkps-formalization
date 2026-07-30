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

**Five of twenty-two topics are written** (2026-07-29). The design below
partitions the library into twenty-two; the table under *Roadmaps* is the
written ones. Seventeen remain, and `python3
scripts/check_tauceti_roadmap_topics.py --needs` names the ones that can go
first: **T01** and **T14** are still unwritten and have no prerequisites at all.

## The candidate topic design

[`CANDIDATE-TOPIC-DESIGN.md`](CANDIDATE-TOPIC-DESIGN.md) proposes a partition of
every `ForTauCeti` module into roadmap topics, ordered as a submission ladder and
validated against the import graph (`scripts/check_tauceti_roadmap_topics.py`:
total, disjoint, and acyclic in submission order). The design text says *156
modules into 20 topics*; **the live partition is 164 modules into 22 topics** —
run the tool rather than quoting the prose, which was written before T21 and T22
were added and before lane SPLIT-1K added four modules (`jon (yardrat)`,
2026-07-29). The directories below are the topics written so far; the rest have
no directory yet, and writing them is the work that design makes possible.

## Roadmaps

| Topic | Covers |
|---|---|
| [`HaagerupZsidoKernel/`](HaagerupZsidoKernel/README.md) | T12 — a finite-mass Fourier kernel for the reciprocal on `1 ≤ \|x\|`: the hyperbolic weight and its Laplace transform, Poisson summation for the Cauchy lattice, the closed-form sine–Laplace and rational-quadratic integrals, the exterior identity `∫ k(t) e^{itx} dt = 1/x`, and the exact `L¹` mass `π / 2` that is the sharp Sylvester constant. Independent of every other topic. |
| [`ApproximationNumbers/`](ApproximationNumbers/README.md) | Approximation numbers and Hilbert-space singular values: the field-generic theory, addition and composition laws, the approximable/compact boundary, adjoint invariance, the rectangular modulus, Eckart–Young, and the min–max principles. Carries [`Suggested.lean`](ApproximationNumbers/Suggested.lean). |
| [`SpectralSubspacePerturbation/`](SpectralSubspacePerturbation/README.md) | Spectral subspace perturbation, operator angles, and Sylvester equations: projection geometry, graph subspaces and Riccati equations, closed and possibly unbounded self-adjoint operators. Davis–Kahan Part III is its principal worked source and acceptance suite. Carries [`Suggested.lean.md`](SpectralSubspacePerturbation/Suggested.lean.md). |
| [`SymmetricOperatorIdeals/`](SymmetricOperatorIdeals/README.md) | Symmetric operator ideals. |
| [`UnboundedOperators/`](UnboundedOperators/README.md) | Unbounded operators on Mathlib `LinearPMap`, the canonical carrier fixed by the U1 decision in `AGENTS.md`. |

`SpectralSubspacePerturbation` is the roadmap target the live `approximation-number`
cluster in `dev/tauceti/extraction-manifest.json` names
(`SpectralSubspacePerturbation Part B … / public-api-integration-review PR 1`).

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

- One directory per topic: `<Topic>/README.md`, optionally with a `Suggested.lean`
  sketching the intended public API. The markdown is definitive; the prototypes
  are neither exhaustive nor prescriptive about proof architecture.
- **This file is an index.** Until 2026-07-29 it held a *full copy* of the
  `ApproximationNumbers` roadmap — an older revision, five passages diverged from
  the real one, including a Related-Work section still weighing options that
  `ApproximationNumbers/README.md` had already decided, and a truncated Ullrich
  citation carrying a leaked assistant tool-call marker where the journal name
  and year belonged. A topic's content belongs in its own directory, never here.
- Specify mathematics **intrinsically**. DKPS file and identifier names belong in
  the provenance and implementation notes, not in the specification prose — a
  roadmap Tau Ceti can accept must read as mathematics, not as a migration
  checklist.

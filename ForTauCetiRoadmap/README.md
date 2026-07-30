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

**Twelve of twenty-four topics are written** (2026-07-29/30; T15 became
T15a/T15b/T15c on the second day). The design below partitions the library into
twenty-four; the table under *Roadmaps* is the written ones, in topic order. Twelve remain, and `python3 scripts/check_tauceti_roadmap_topics.py --needs`
reports **no independent topic left unwritten** — T01, T12, T14, T15b, T21
and T22 all have roadmaps now, so every remaining topic waits on one of them.

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
| [`PositiveSqrtAndModulus/`](PositiveSqrtAndModulus/README.md) | T01 — the finite-dimensional `RCLike` functional calculus of a symmetric operator, and what it builds: the positive square root with its uniqueness theory, the modulus and polar decomposition, Courant–Fischer min–max and Weyl. Independent, and named directly by seven other topics. |
| [`PolarDecomposition/`](PolarDecomposition/README.md) | T02 — polar decomposition and partial isometries: the algebraic notion `u * star u * u = u` shared across settings, the finite-dimensional `RCLike` decomposition with a genuine unitary, the bounded-below isometry, the general rectangular `ℂ` partial isometry with `polarInitial = (ker M)ᗮ`, and the near-isometric factorisation. Answers the question a reviewer will ask — why *two* polar decompositions — by showing they differ on three axes and neither subsumes the other, because the two moduli of T01 have complementary limitations. |
| [`SingularValues/`](SingularValues/README.md) | T03 — singular values and the singular system: a `ContinuousLinearMap` accessor over Mathlib's `LinearMap` notion (naming surface only, deliberately), the shared nonzero spectrum of `A†A` and `AA†` with multiplicity, the intrinsic singular **vectors** Mathlib lacks — including the extension of the left family to an orthonormal basis — and the Moore–Penrose inverse with all four Penrose identities **and** the uniqueness converse. Everything stated basis-free, because T06, T07 and T17 are. |
| [`ProjectionsAndSpectralSubspaces/`](ProjectionsAndSpectralSubspaces/README.md) | T04 — Gram matrices, orthogonal projections and spectral subspaces: the sharp projector-difference identity `‖P − Q‖ = max(‖(1−Q)P‖, ‖(1−P)Q‖)` that upgrades two one-sided sin-Θ estimates to a factor-one bound **with no equal-rank hypothesis**, the shared spectral-gap predicates four theorem families state their hypotheses in, reducing subspaces kept independent of the perturbation theory, and an orthogonal-series constructor for non-unit vectors that Mathlib lacks. `GramMatrix` has already been through mathlib4 PR #40567 and was generalised past the review feedback afterwards. Seven dependents, one prerequisite. |
| [`MajorizationAndUINorms/`](MajorizationAndUINorms/README.md) | T05 — majorization, Schur–Horn and unitarily invariant norms. The topic's architectural claim is checkable in one command: `Analysis/Convex/Majorization` — the Hardy–Littlewood–Pólya engine under every UI-norm inequality here — imports **no operator theory at all**, so it can go to `Mathlib.Analysis.Convex` independently. Mathlib has the spectral theorem and Birkhoff but neither a majorization predicate nor Schur–Horn, so neither half duplicates upstream. Schur–Horn via the doubly-stochastic `schurWeight`, Ky Fan sums and the trace inequality, `diagOp` turning tuples back into operators. |
| [`ApproximationNumbers/`](ApproximationNumbers/README.md) | Approximation numbers and Hilbert-space singular values: the field-generic theory, addition and composition laws, the approximable/compact boundary, adjoint invariance, the rectangular modulus, Eckart–Young, and the min–max principles. Carries [`Suggested.lean`](ApproximationNumbers/Suggested.lean). |
| [`SymmetricOperatorIdeals/`](SymmetricOperatorIdeals/README.md) | Symmetric operator ideals. |
| [`HilbertSchmidtOperators/`](HilbertSchmidtOperators/README.md) | T11 — Hilbert–Schmidt operators realised as `ℓ²` of columns in a fixed Hilbert basis: the `columns`/`ofLp` bijection and its two round trips, the `ℓ²` norm as the Hilbert–Schmidt norm, invariance of that norm under conjugation by isometries (which is what makes the Sylvester flow a unitary group), and the Pythagoras splitting of the energy along an orthogonal family. Records why the `ℓ²` model is used rather than the Hilbert tensor product, and the three `ofLp` lemmas this roadmap found stranded in T16 and moved back. |
| [`SylvesterRosenblum/`](SylvesterRosenblum/README.md) | T16 — Sylvester equations and the Rosenblum theorem: the finite-dimensional core, the coercive bound `‖X‖ ≤ ‖Y‖/(2δ)` with its Lax–Milgram unit, the Hilbert–Schmidt block layer, and the flow `W t Z = U_A t ∘ Z ∘ (U_B t)⋆` whose generator Stone's theorem identifies as `Z ↦ A Z − Z B`. Records the two decisions a reviewer should check: Rosenblum is proved **without** a Borel functional calculus (using that `1` is null for every diagonal measure), and the sharp constant `π / 2` comes from T12 — where a real certificate provably cannot do better than `5 / 3`. The hinge of the DAG: seven prerequisites, and T17 consumes it. |
| [`StoneTheorem/`](StoneTheorem/README.md) | T13 — one-parameter unitary groups and the forward direction of Stone's theorem: the generator as a `LinearPMap` on exactly the vectors where the difference quotient converges, self-adjointness via surjectivity of `generator + i` with density *derived* rather than assumed, the commutant lemma, and the Duhamel estimate behind the Yosida approximation. **Independent** — this roadmap found that its only edge to T02 came from a misfiled module (`IntertwiningUnitary`, reassigned), so Stone can now be submitted first. |
| [`HaagerupZsidoKernel/`](HaagerupZsidoKernel/README.md) | T12 — a finite-mass Fourier kernel for the reciprocal on `1 ≤ \|x\|`: the hyperbolic weight and its Laplace transform, Poisson summation for the Cauchy lattice, the closed-form sine–Laplace and rational-quadratic integrals, the exterior identity `∫ k(t) e^{itx} dt = 1/x`, and the exact `L¹` mass `π / 2` that is the sharp Sylvester constant. Independent of every other topic. |
| [`BorelCalculus/`](BorelCalculus/README.md) | T14 — the bounded Borel functional calculus of a normal operator and the projection-valued measures it produces: diagonal spectral measures from Riesz–Markov–Kakutani, the polarised transport principle that carries every continuous-calculus identity to bounded Borel symbols, multiplicativity, and `ProjValMeasure` on the Borel sets of `ℝ`. Independent, and the topic the whole unbounded stack (T15) rests on. |
| [`ClosedPartialMaps/`](ClosedPartialMaps/README.md) | T15a — closed partial linear maps: the U1 decision in force (an unbounded operator *is* a `LinearPMap`; closedness and self-adjointness are hypotheses), domain transport, graph norms and graph cores, the domain-preserving perturbation, the domain-aware Sylvester equation, and quadratic-form bounds. |
| [`UnboundedResolvent/`](UnboundedResolvent/README.md) | T15b — resolvents of unbounded self-adjoint operators: the resolvent set of a `LinearPMap` (Mathlib's `spectrum` does not apply to a partial map), the named resolvent and the first resolvent identity, openness, real spectrum with `‖R z‖ ≤ \|Im z\|⁻¹`, the real-point variant, and the intertwining chain up to the continuous functional calculus. Independent — one of the four topics that need nothing else. |
| [`UnboundedSpectralMeasure/`](UnboundedSpectralMeasure/README.md) | T15c — the spectral measure of an unbounded self-adjoint operator via the Cayley transform, its resolvent formula, spectral projections and the reduction to a spectral subspace; Yosida approximants, Stone's uniqueness half, and the three shapes a Hilbert–Schmidt block argument needs. |
| [`UnboundedOperators/`](UnboundedOperators/README.md) | **The pre-split T15 roadmap**, kept for its full statement of the U1 decision — unbounded operators on Mathlib `LinearPMap` as the canonical carrier (`AGENTS.md`). Its milestones are now distributed over T15a, T15b and T15c above. |
| [`SpectralSubspacePerturbation/`](SpectralSubspacePerturbation/README.md) | Spectral subspace perturbation, operator angles, and Sylvester equations: projection geometry, graph subspaces and Riccati equations, closed and possibly unbounded self-adjoint operators. Davis–Kahan Part III is its principal worked source and acceptance suite. Carries [`Suggested.lean.md`](SpectralSubspacePerturbation/Suggested.lean.md). |
| [`MatrixRankFactorization/`](MatrixRankFactorization/README.md) | T21 — rank factorization `M = L * R` through `Fin r`, and the positive-semidefinite case `B = Aᴴ * A` with at most `d` rows: the multidimensional-scaling embedding step, stated as an iff. Independent, and a leaf. |
| [`BergeMaximum/`](BergeMaximum/README.md) | T22 — Berge's maximum theorem over a *fixed* compact feasible set: stability of minimizers under approximate minimization, upper hemicontinuity of the argmin correspondence through Mathlib's own predicate, continuity of the value function, and a uniform `ε`–`δ` modulus. Independent, and a leaf. |

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

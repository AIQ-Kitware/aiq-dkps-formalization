# Roadmap: approximation numbers and symmetric operator ideals

Approximation numbers `aₙ(T)` — the operator-norm distance from `T` to operators
of rank `≤ n` — are the backbone of the quantitative theory of compact operators:
they are the singular values in the Hilbert-space case, they define the Schatten
and, more generally, the symmetrically-normed (Calkin) operator ideals, and they
are the natural language for Eckart–Young low-rank approximation, for
perturbation bounds on singular subspaces, and for the entropy/approximation
scale in approximation theory.

Mathlib has the *static* stack these rest on — `ContinuousLinearMap`, the
operator norm, `LinearMap.rank`, finite-dimensional spectral theory, the
continuous functional calculus, the polar decomposition of a compact/continuous
operator via `|T| = (T⋆T)^{1/2}` — but **not the approximation-number layer**:
there is no `s`-number function of a bounded operator, no development of its order
and ideal (`sub`-additivity, two-sided multiplicativity) theory, no
identification with singular values, and no symmetrically-normed-ideal /
Ky-Fan-norm theory built on top.

The goal is to **build the reusable theory of these objects**, not to race to a
handful of named theorems. The bar for "done": a researcher in operator theory,
numerical linear algebra, or perturbation theory finds approximation numbers
defined at their natural generality, equipped with the full elementary API
(order, additive and multiplicative ideal inequalities, homogeneity, adjoint
invariance, singular-value identification, min–max characterizations), and the
symmetric-ideal theory (Ky Fan gauges, symmetrically normed ideals, the
Hilbert–Schmidt and trace-class examples) built *on top of it* rather than as
isolated endpoints.

Suggested home: `TauCeti/Analysis/OperatorIdeal/ApproximationNumber/` for the
`s`-number layer, `TauCeti/Analysis/OperatorIdeal/Symmetric/` for the symmetric
ideal theory. See `Suggested.lean` for prototype signatures.

## Generality bar (decide these up front; do not silently specialize)

- **The `s`-number layer is field-generic, not Hilbert-specific.** The
  approximation number and its order/ideal API are defined for a
  `T : E →L[𝕜] F` over a `NontriviallyNormedField 𝕜` with `E`, `F` seminormed
  `𝕜`-spaces, and with **independent source and target universes**. Nothing in
  the definition, the antitonicity, the additive inequality
  `aₘ₊ₙ(S+T) ≤ aₘ(S) + aₙ(T)`, the two-sided ideal inequalities, or absolute
  homogeneity needs an inner product. State them at that generality; the
  Hilbert-space results are a strictly later layer that *imports* this one.
- **Zero-based indexing, `ℝ≥0`-valued.** `aₙ(T)` is indexed from `n = 0` (so
  `a₀(T) = ‖T‖`, the distance to rank-`0` maps) and valued in `ℝ≥0` (`NNReal`).
  This must be pinned: the literature is split between `sₙ` (one-based) and `aₙ`
  (zero-based). We commit to zero-based `aₙ` and prove the one-based bridge
  lemma, not the reverse. Rationale: the infimum over `rank ≤ n` is the clean
  primitive, and `n = 0` is then the operator norm with no off-by-one.
- **Adjoint invariance is Hilbert-space, `RCLike`-generic.** `aₙ(T⋆) = aₙ(T)`
  requires an adjoint, so it lives in the Hilbert layer over `[RCLike 𝕜]` with
  `E`, `F` inner-product spaces; real and complex are the two instances, decided
  now to be a single `RCLike` statement, not two.
- **Singular-value identification is finite-dimensional first.** The theorem
  `aₙ(T) = σₙ(T)` (the `n`th singular value, zero-based, from the sorted spectrum
  of `|T|`) is stated for finite-dimensional inner-product spaces, where `σₙ` is
  already meaningful. The infinite-dimensional min–max characterization is a
  separate milestone and is stated as a **two-sided bound package**, honest about
  which half is unconditional.
- **Symmetric ideals via gauges on `ℝ≥0`-sequences.** A symmetric norming
  function is a symmetric gauge `Φ` on finitely-supported `ℝ≥0` sequences; the
  ideal `S_Φ` is `{T : Φ(a(T)) < ∞}` with norm `Φ(a(T))`. Decide now: the
  primitive is the **gauge on the approximation-number sequence**, and Schatten
  `p`-norms and the Ky Fan `k`-norms `∑_{n<k} aₙ` are *instances*, never the
  definition. This keeps the theory symmetric-ideal-first, Schatten-second.
- **Rectangular throughout.** `E` and `F` are distinct spaces; do not silently
  specialize to `E = F`. The rectangular operator modulus (`|T|` acting on the
  source) and the rectangular singular system are first-class.

## What Mathlib already has (consume, and connect to)

- **Operators & rank:** `ContinuousLinearMap`, `‖·‖`/`‖·‖₊` operator (semi)norm
  (`Mathlib.Analysis.Normed.Operator.NNNorm`), `LinearMap.rank` and its finiteness
  API (`Mathlib.LinearAlgebra.Dimension.{LinearMap,Finite}`). The approximation
  number is `⨅ R, ‖T − R‖₊` over `{R // R.rank ≤ (n : Cardinal)}`; tie every rank
  bound to `LinearMap.rank`, and use `Cardinal.lift` for the cross-universe
  comparisons (natural-number bounds are lift-invariant).
- **Self-adjoint / positive operators & functional calculus:** `IsSelfAdjoint`,
  the `ℝ≥0`/`ℝ` continuous functional calculus, `CFC.sqrt` and `cfc` for the
  positive square root — the source of `|T| = (T⋆T)^{1/2}` (the rectangular
  modulus `T⋆T : E →L E`). Do not re-derive positivity of `T⋆T` or the square
  root; consume the CFC API.
- **Finite-dimensional spectral theory:** the spectral theorem for self-adjoint
  operators, eigenvalue enumeration, and Courant–Fischer min–max for eigenvalues
  of a self-adjoint operator on a finite-dimensional inner-product space — the
  route to singular values as `σₙ(T) = √(λₙ(T⋆T))` and to `aₙ = σₙ`.
- **Adjoints:** `ContinuousLinearMap.adjoint` on Hilbert space, `‖T⋆‖ = ‖T‖`,
  `(T⋆)⋆ = T`, and rank invariance of the adjoint — the ingredients of
  `aₙ(T⋆) = aₙ(T)`.
- **Order / `NNReal` / `ENNReal`:** `ℝ≥0`, `ℝ≥0∞`, `ciInf`/`iInf` order API,
  `tsum` for the `ℓ^p` gauges. Symmetric-gauge domination and the Schatten norms
  are stated with these; use `tsum`/`Summable` rather than a bespoke summability
  predicate.

**Check what is already in motion.** This development was adapted from
**Mathlib PR #32126** (approximation numbers of continuous linear maps). Before
this roadmap is used to author code upstream, re-check that PR's status, the open
Mathlib operator-ideal PRs, and the Lean Zulip: some `s`-number API may land in
Mathlib directly, in which case the milestones below refactor onto it and this
roadmap becomes the *symmetric-ideal* layer above Mathlib's `s`-numbers. Cite
what is found; do not duplicate an API Mathlib is already building.

## Milestones

The layers are ordered so each rests only on Mathlib, Tau Ceti, or an earlier
layer here. Harder material is later, but nothing is optional.

### Layer A — the approximation number and its ideal theory (field-generic)

The `s`-number function and its complete elementary theory over
`NontriviallyNormedField`, no inner product.

1. **A.1 Definition and order.** `approximationNumber T n : ℝ≥0` as the infimum
   over rank-`≤ n` maps; the characterizing inequalities (`aₙ(T) ≤ ‖T − R‖` for
   admissible `R`; the universal lower bound); `a₀(T) = ‖T‖`; antitonicity in
   `n`; `aₙ(T) ≤ ‖T‖`; `aₙ(0) = 0`; nonnegativity; the strict-approximant
   witness `aₙ(T) < aₙ(T) + ε` realized by some admissible `R`.
2. **A.2 Additivity.** `a_{m+n}(S + T) ≤ aₘ(S) + aₙ(T)` and its diagonal
   corollary; the reverse-triangle `|aₙ(S) − aₙ(T)| ≤ ‖S − T‖` (Lipschitz in the
   operator norm).
3. **A.3 Ideal (multiplicativity).** the two-sided ideal inequalities
   `a_{m+n}(A∘T∘B) ≤ ‖A‖·aₘ(T)·… ` in the precise rank-additive form:
   `aₙ(T ∘ B) ≤ aₙ(T)·‖B‖`, `aₙ(A ∘ T) ≤ ‖A‖·aₙ(T)`, and the composed
   `a_{m+n}(A∘T) ≤ …` rank-splitting bound; absolute homogeneity
   `aₙ(c • T) = ‖c‖·aₙ(T)`.
4. **A.4 Rank and finite-rank characterization.** `aₙ(T) = 0` for `n ≥ rank T`
   when `T` has finite rank; the approximation number as the mechanism defining
   the approximable (norm-limit-of-finite-rank) operators, connecting to
   Mathlib's compact-operator API where it exists.

### Layer B — Hilbert-space identification (adjoint, singular values)

Adds an inner product; identifies `aₙ` with singular values.

5. **B.1 Adjoint invariance.** `aₙ(T⋆) = aₙ(T)` over `[RCLike 𝕜]`, via rank
   invariance of the adjoint and `‖T − R‖ = ‖T⋆ − R⋆‖`.
6. **B.2 Rectangular operator modulus.** `|T| := (T⋆T)^{1/2} : E →L E` (positive,
   self-adjoint, `‖ |T| x‖ = ‖T x‖`), and `aₙ(T) = aₙ(|T|)` — the reduction of
   the rectangular problem to a positive operator on the source.
7. **B.3 Singular values, finite-dimensional.** `σₙ(T)` as the zero-based sorted
   eigenvalue sequence of `|T|`; `aₙ(T) = σₙ(T)` on finite-dimensional
   inner-product spaces (Eckart–Young). This is the theorem that pins the whole
   development to the classical singular-value picture.
8. **B.4 Min–max (Courant–Fischer for `s`-numbers).** the two-sided
   characterization `aₙ(T) = min_{dim V ≤ n} max_{x ⟂ V, ‖x‖=1} ‖T x‖` in finite
   dimensions, and the **unconditional lower-bound half** in infinite dimensions
   (an `(n+1)`-dimensional subspace on which `T` is bounded below by `c` forces
   `aₙ(T) ≥ c`), stated honestly as the half that holds without compactness.

### Layer C — symmetric operator ideals

Builds the ideal theory on the `s`-number sequence.

9. **C.1 Symmetric gauges.** a symmetric norming function `Φ` on finitely
   supported `ℝ≥0` sequences (monotone, symmetric, `Φ(e₀)=1`); the induced ideal
   `S_Φ = {T // Summable/finite Φ(a(T))}` with `‖T‖_Φ := Φ(a(T))`.
10. **C.2 Ky Fan norms and dominance.** the Ky Fan `k`-norms
    `‖T‖_{(k)} = ∑_{n<k} aₙ(T)`; Ky Fan dominance (`∀k, ∑_{n<k} aₙ(S) ≤ ∑_{n<k}
    aₙ(T)` ⟹ `Φ`-domination for every symmetric gauge `Φ`); the triangle
    inequality for each `‖·‖_Φ` as a consequence.
11. **C.3 Schatten instances.** the `ℓ^p` gauge `Φ_p(a) = (∑ aₙ^p)^{1/p}` and the
    Schatten `p`-ideals as instances of C.1; Hilbert–Schmidt (`p = 2`,
    `∑ aₙ² = ∑ ‖T eᵢ‖²`, basis-independent) and trace class (`p = 1`) as named
    examples with their defining identities.
12. **C.4 Block sums and scalar/real–complex transport.** `aₙ` of an orthogonal
    block-diagonal sum `T₁ ⊕ T₂` as the sorted merge of the two `s`-sequences;
    invariance of the whole theory under real ⇆ complex complexification, so the
    real-scalar ideal theory is a transported instance, not a re-proof.

## Conventions pinned here

- **`approximationNumber`, zero-based, `ℝ≥0`-valued**, extending the Mathlib
  namespace `ContinuousLinearMap` for dot notation (`T.approximationNumber n`).
  This is a **global-namespace commitment** and a candidate Mathlib upstreaming
  name; it is called out for maintainer review rather than hidden. If Tau Ceti
  prefers a `TauCeti`-namespaced `sNumber`, the change is mechanical and decided
  before Layer A merges — not after.
- **`σ`/singular values** reuse the finite-dimensional eigenvalue enumeration of
  `|T|`; no private singular-value predicate.
- **Symmetric gauge first, Schatten second.** Schatten `p`-norms and Ky Fan
  `k`-norms are instances of the symmetric-gauge ideal, never the primitive.
- **`Bornology.IsBounded` / explicit `∀ x, ‖T x‖ ≤ C`** for boundedness in
  hypotheses; no "bounded on a set" wrapper.
- Any universe-`lift` helper (e.g. `Cardinal.le_natCast_of_lift_le`) is a generic
  Mathlib-namespace lemma justified on its own terms, not smuggled in because one
  proof needed it — its inclusion is reviewed under the API gate.

## Provenance (secondary — not prescriptive)

This section records where a working formalization of Layers A–B already exists,
so reviewers can coordinate; it is **not** the specification and must not be read
as prescribing file layout or proof architecture. The roadmap above is
definitive.

- A staged implementation of Layer A and most of Layer B lives in the DKPS
  (Davis–Kahan) repository under `ForTauCeti/Analysis/OperatorIdeal/`
  `ApproximationNumber/{Basic,Adjoint,FiniteDimensional,MinMax,OperatorModulus}`
  and `ForTauCeti/Analysis/InnerProductSpace/CourantFischer`, in final `TauCeti.*`
  / `ContinuousLinearMap.*` namespaces, module-system-converted and axiom-clean.
- That code was itself adapted from **Mathlib PR #32126**; Layer A's
  `approximationNumber` and order/ideal API and the `Cardinal` universe helper
  come from there. Coordinate with that PR before upstreaming.
- Copyright (c) 2026 Kitware, Inc., Apache 2.0; authors Jon Crall,
  OpenAI GPT-5.6 Thinking, Niels Voss, Arnav Mehta, Rawad Kansoh.
- Per the "improve, don't canonize" rule: the staged code is a starting point.
  Apply the generality bar and conventions above — in particular the
  symmetric-gauge-first structure of Layer C, which the staged code does not yet
  have — rather than following the existing files.

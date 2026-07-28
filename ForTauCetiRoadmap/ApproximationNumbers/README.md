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
`s`-number layer, `TauCeti/Analysis/OperatorIdeal/Family/` for the symmetric
ideal theory (this document once said `.../Symmetric/`; `Family/` is what
shipped, and is what decision 7 and `ForTauCeti/README.md` name). See
`Suggested.lean` for prototype signatures.

## Generality bar (decide these up front; do not silently specialize)

- **The `s`-number layer is field-generic, not Hilbert-specific.** The
  approximation number and its order/ideal API are defined for a
  `T : E →L[𝕜] F` over a `NontriviallyNormedField 𝕜` with `E`, `F` seminormed
  `𝕜`-spaces, and with **independent source and target universes**. Nothing in
  the definition, the antitonicity, the additive inequality
  `aₘ₊ₙ(S+T) ≤ aₘ(S) + aₙ(T)`, the two-sided ideal inequalities, or absolute
  homogeneity needs an inner product. State them at that generality; the
  Hilbert-space results are a strictly later layer that *imports* this one.
- **Zero-based indexing, `ℝ`-valued.** `aₙ(T)` is indexed from `n = 0` (so
  `a₀(T) = ‖T‖`, the distance to rank-`0` maps) and valued in `ℝ` with
  `approximationNumber_nonneg`. Both halves are now *decided*, not merely
  proposed: see decisions 1 (index) and 2 (codomain) below.
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

1. **A.1 Definition and order.** `approximationNumber T n : ℝ` as the infimum
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

   The *target* of this construction is fixed: it produces a
   `TauCeti.SymmetricOperatorIdealFamily` (decision 7 below), whose gauge is
   `Φ ∘ a` read in `ℝ≥0∞`. The abstract family structure is already staged in
   `ForTauCeti/Analysis/OperatorIdeal/Family/` and now has **two** instances,
   the operator norm and the finite Ky Fan gauges (see C.2); C.1's job is to add
   the Calkin construction as the third.
10. **C.2 Ky Fan norms and dominance.** the Ky Fan `k`-norms
    `‖T‖_{(k)} = ∑_{n<k} aₙ(T)`; Ky Fan dominance (`∀k, ∑_{n<k} aₙ(S) ≤ ∑_{n<k}
    aₙ(T)` ⟹ `Φ`-domination for every symmetric gauge `Φ`); the triangle
    inequality for each `‖·‖_Φ` as a consequence.

    **Partly landed 2026-07-28.** The `k`-norm is
    `kyFanApproximationGauge k` and it now has a canonical family form,
    `kyFanSymmetricIdealFamily k hk : TauCeti.SymmetricOperatorIdealFamily 𝕜`,
    with a completeness instance. Both are parked in
    `DavisKahan/OperatorIdeal/ApproximationNumbers/ScalarGeneric.lean` rather
    than here, because `kyFanApproximationGauge` and the capability class
    supplying its triangle inequality are not yet extracted; the intended home
    is `ForTauCeti/Analysis/OperatorIdeal/Family/KyFan.lean` and the note is on
    the declaration. Dominance is bundled as `KyFanDominantIdealFamily`, which
    is a three-field structure over the canonical family — converting it to a
    genuine mixin is the item that remains.
11. **C.3 Schatten instances.** the `ℓ^p` gauge `Φ_p(a) = (∑ aₙ^p)^{1/p}` and the
    Schatten `p`-ideals as instances of C.1; Hilbert–Schmidt (`p = 2`,
    `∑ aₙ² = ∑ ‖T eᵢ‖²`, basis-independent) and trace class (`p = 1`) as named
    examples with their defining identities.
12. **C.4 Block sums and scalar/real–complex transport.** `aₙ` of an orthogonal
    block-diagonal sum `T₁ ⊕ T₂` as the sorted merge of the two `s`-sequences;
    invariance of the whole theory under real ⇆ complex complexification, so the
    real-scalar ideal theory is a transported instance, not a re-proof.

## Conventions pinned here

- **`approximationNumber`, zero-based, `ℝ`-valued**, extending the Mathlib
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
- Any universe-`lift` helper is a generic Mathlib-namespace lemma justified on
  its own terms, not smuggled in because one proof needed it — its inclusion is
  reviewed under the API gate. ***Settled 2026-07-27:*** the one such helper,
  formerly `Cardinal.le_natCast_of_lift_le` sitting inside the approximation-number
  file, now lives in its own dependency-closed module
  `ForTauCeti/SetTheory/Cardinal/Lift.lean` and is stated as the iff
  `Cardinal.lift_le_natCast : lift.{w} c ≤ ↑n ↔ c ≤ ↑n`, matching the shape of its
  Mathlib neighbours `Cardinal.aleph_natCast_le_lift` / `beth_natCast_le_lift` /
  `omega_natCast_le_lift`. It is separately upstreamable to
  `Mathlib/SetTheory/Cardinal/Order.lean`, so the operator-ideal PR no longer
  carries a `Cardinal` namespace extension at all. Privatizing was not an option:
  it has four call sites in three ForTauCeti modules plus a downstream consumer.

## Open representation decisions (settle in A0, before any A1 code PR)

A declaration-level adversarial-review audit of the staged code
(`dev/tauceti-signature-polish-todo.md`, baseline `543b46f`) surfaced the
representation and API decisions a Tau Ceti reviewer will demand this roadmap
answer up front. Settle them here before writing names — **do not run a blanket
rename pass first**; renaming a parallel abstraction only makes duplication
harder to remove. The decisions (with this roadmap's current stance):

1. **Index convention.** ***Decided: zero-based*** (2026-07-27). `aₙ(T)` is the
   infimum over `rank ≤ n`, so `a₀(T) = ‖T‖`; the one-based `s`-numbers of the
   operator-ideal literature (Pietsch: `sₙ(T) = dist(T, {rank < n})`,
   `s₁(T) = ‖T‖`) are `sₙ = a_{n-1}`. **Only one of the two is developed** —
   carrying both would duplicate the entire API for an index shift, which is the
   same "do not carry both" rule that settled decision 2.

   The audit demanded this be "explicitly approved … or the entire API reindexed
   before any PR", so here is the argument a reviewer should be given, in order
   of force:

   * **The flagship theorem is index-free only in the zero-based convention.**
     Mathlib's `LinearMap.singularValues` is zero-indexed, so the identification
     reads `aₙ(T) = σₙ(T)`
     (`ContinuousLinearMap.approximationNumber_eq_singularValues`). One-based
     numbering turns it into `sₙ(T) = σ_{n-1}(T)` — and `n - 1` on `ℕ` is
     *truncated* subtraction, so the statement would additionally need an
     `n ≠ 0` side condition or would be silently false at `n = 0`. Putting
     truncated subtraction into the headline theorem of the development is a
     worse defect than departing from Pietsch's numbering.
   * **The ideal inequalities are off-by-one free.** `a_{m+n}(S + T) ≤ aₘ(S) +
     aₙ(T)` (`approximationNumber_add_le_add`) against the one-based
     `s_{m+n-1}(S + T) ≤ sₘ(S) + sₙ(T)`; likewise for the two-sided
     multiplicative bounds. Every one of these would acquire a `- 1`.
   * **`n = 0` is not a special case.** `a₀(T) = ‖T‖` is a theorem
     (`approximationNumber_zero`) with the same proof as every other index. The
     one-based convention has to *define* `s₀` by fiat, since `rank < 0` is
     empty and the infimum is over an empty set.
   * **It matches the ambient library.** Mathlib indexes sequences, `Fin`
     families, and sorted eigenvalues (`Matrix.IsHermitian.eigenvalues₀`) from
     zero; a one-based `s`-number API would be the odd one out and would force
     `Nat.succ`/`Fin.succ` shims at every interface with the singular-value and
     Courant–Fischer layers.

   **What is deliberately *not* done:** no one-based `sNumber` definition and no
   `sₙ = a_{n-1}` bridge *theorem* is added. A bridge theorem needs a one-based
   definition to bridge to, and adding one purely to state the translation would
   reintroduce exactly the duplicate API this decision exists to avoid. The
   translation is documented instead — in the module docstring of
   `ApproximationNumber/Basic.lean` and in the first sentence of the
   definition's own docstring, as the audit requires.
2. **Codomain: `ℝ≥0` vs `ℝ`.** ***Decided: `ℝ`*** (2026-07-24; executed, whole
   workspace green). `approximationNumber : ℝ` with
   `approximationNumber_nonneg`, and **no** `ℝ≥0` API — not even an accessor —
   so the "do not carry both" rule holds exactly.

   Rationale, in the order it should be presented to a reviewer:

   * **Mathlib precedent.** `Metric.infDist` is the same shape — an infimum of
     nonnegative reals — and Mathlib defines it real-valued with a separate
     `infDist_nonneg`. The same holds for the norm-like quantities this object
     sits beside: `norm`, `dist`, and `LinearMap.singularValues` are all `ℝ`
     (the `₊` versions are secondary accessors, not the primary definition).
   * **The `ℝ≥0` choice was paying a tax at *both* boundaries.** Upward, the
     flagship Eckart–Young statements read
     `(⟨T.singularValues n, T.singularValues_nonneg n⟩ : NNReal) ≤ …` — exactly
     the `⟨value, proof⟩` exposure this document forbids. Downward, the paper
     layer had already built a real-valued wrapper
     (`approximationSingularValue : ℝ`) used in *more* files than the `ℝ≥0`
     original, together with a tautological `_nonneg` lemma for it.
   * **Cost paid.** The lattice-completeness convenience is replaced by two
     small private facts (a `Nonempty` index instance, already present, and a
     `BddBelow` range lemma) discharged once inside the two characterization
     lemmas; every later lemma goes through those. `0 ≤ aₙ` becomes a one-line
     theorem instead of `bot_le`.
   * **What it deleted.** Two entire NNReal↔ℝ bridging layers in the downstream
     (the complex and real Courant–Fischer localization files) lost their
     coercion machinery outright, and the `congrArg (coe)`-plus-`simpa` idiom
     that wrapped roughly a dozen paper-facing restatements is gone.
3. **Namespace: extend `ContinuousLinearMap` vs live under `TauCeti`.** Current
   stance: extend `ContinuousLinearMap` for dot notation (candidate Mathlib
   name). *Flagged for maintainer review* — a global-namespace commitment.
4. **Canonical rectangular modulus name and unification.** `|T| = (T⋆T)^{1/2}`
   is the single source modulus (candidate `ContinuousLinearMap.modulus`); the
   square-operator `operatorAbs` is its **specialization and must be deleted**,
   not shipped as a peer API. Record which Mathlib `CFC.sqrt`/`cfc` lemmas make
   modulus lemmas redundant (consume them, don't re-derive).
5. **The Courant–Fischer product is an equality, not support lemmas.** Layer B.4
   must expose an actual min–max/max–min equality as the headline; the coordinate
   helpers become private/secondary. The staged `specSubspace` is a *coordinate
   span of an arbitrary basis*, not intrinsically spectral — rename/relocate to
   `OrthonormalBasis.spanIndices` (it contains no operator or spectrum).
6. **Hilbert–Schmidt: one predicate + norm.** Layer C.3 fixes a single
   `IsHilbertSchmidt`/`hilbertSchmidtNorm`; the basis-column, tensor,
   singular-value, and Frobenius presentations are **equivalence theorems** for
   that one object, never peer definitions.
7. **Representation of an operator ideal family.** ***Decided: one `ℝ≥0∞`-valued
   gauge*** (2026-07-27; staged as `ForTauCeti/Analysis/OperatorIdeal/Family/`).
   A symmetric operator ideal family is presented by a *single* datum

   ```lean
   gauge : ∀ {E F} [...], (E →L[𝕜] F) → ℝ≥0∞
   ```

   with the ideal recovered as its finiteness domain
   (`OperatorIdealFamily.carrier : Submodule 𝕜 (E →L[𝕜] F)`), not by a
   membership predicate plus an independent real gauge.

   Rationale, in the order it should be presented to a reviewer:

   * **It is the only presentation that has an extensionality theorem.** With
     membership and gauge as independent data, the laws constrain the gauge only
     *on* members, so two families can agree on every ideal element and still
     differ off it. That is the API-design rubric's "free data" failure mode, and
     it makes `ext` unstatable. With the finiteness-domain presentation the gauge
     is the only field and `OperatorIdealFamily.ext` is immediate.
   * **It is the classical presentation.** A symmetric norming function
     (Gohberg–Krein, Calkin) is defined on everything and the ideal *is* where it
     is finite; `ℝ≥0∞` is the honest codomain of an ideal norm. Note this does
     **not** conflict with decision 2: `approximationNumber` is a real number
     attached to a single operator, while an ideal gauge is genuinely `∞` off its
     ideal.
   * **Every law becomes unconditional.** In `ℝ≥0∞` subadditivity, homogeneity
     `gauge (c • A) = ‖c‖ₑ * gauge A`, the two-sided ideal bound
     `gauge (L ∘L A ∘L R) ≤ ‖L‖ₑ * gauge A * ‖R‖ₑ`, and `‖A‖ₑ ≤ gauge A` all hold
     verbatim at non-members. No axiom and no downstream lemma carries a
     membership hypothesis.
   * **The axiom list collapses from fourteen fields to four.** Closure under
     `0`, `+`, `•`, `-` and finite sums is `Submodule` membership for the carrier;
     `gauge 0 = 0` follows from homogeneity at `c = 0` (which also rules out the
     everywhere-`∞` gauge); definiteness follows from `‖A‖ₑ ≤ gauge A`.
   * **Completeness is a typeclass, not a Cauchy criterion.** The ideal carries a
     `NormedAddCommGroup`/`NormedSpace` structure on
     `OperatorIdealFamily.Elem` — a type synonym, because the bare subtype already
     inherits the *operator* norm and the two differ — and completeness is
     `OperatorIdealFamily.IsComplete`, i.e. `CompleteSpace` for that norm.
   * **Layering, with a genuine obstruction recorded.** The base layer keeps
     **independent source and target universes**. Adjoint symmetry cannot be
     added there: the adjoint exchanges source and target, so a family closed
     under adjoints must live on one universe. Hence two structures —
     `OperatorIdealFamily` and `SymmetricOperatorIdealFamily`, the latter
     extending the diagonal instantiation — rather than one with an optional
     field.
   * **Hilbert, not Banach — corrected 2026-07-28.** This bullet previously read
     "the base layer is stated over Banach spaces … per the generality bar
     above", and both halves of that were wrong. The citation was a
     mis-attribution: the generality bar in this document is scoped to the
     **`s`-number layer** (`approximationNumber` over a
     `NontriviallyNormedField`, seminormed spaces), which is unchanged and stays
     field-generic. And the Banach setting cannot hold the examples. The four
     laws are norm-only and are meaningful verbatim over Banach spaces, but of
     the five gauges this development has — operator norm, finite Ky Fan,
     Schatten `p`, trace class, Hilbert–Schmidt — only the first survives
     outside Hilbert space, and the obstruction is `gauge_add_le`. The finite Ky
     Fan gauge `∑_{n<k} aₙ` is *defined* at full Banach generality yet its
     subadditivity is Hilbertian: the proof runs through singular values and
     majorization, and the classical additivity of approximation numbers,
     `a_{m+n}(S + T) ≤ aₘ(S) + aₙ(T)`, does not recover it — at `k = 2` it only
     yields `a₀(S) + 2a₀(T) + a₁(S)`. A Banach-wide base would therefore be a
     structure with one instance and no way to acquire the motivating ones. The
     space parameters are `[RCLike 𝕜]`, `InnerProductSpace` and `CompleteSpace`
     throughout; re-widening is mechanical (no proof in the module uses the
     inner product, only the norm) should an instance ever appear.
   * **Validation, and it is live in production.** The historical Davis–Kahan
     record `RectangularSymmetricIdealFamily` is *derivable*: every one of its
     fourteen fields, including the hand-rolled `gauge_complete`, is a theorem
     about the canonical family (`SymmetricOperatorIdealFamily.toRectangular`).
     The converse map does not exist, which is the defect restated. Since
     2026-07-28 that derivation is not merely a validation exercise:
     `KyFanDominantIdealFamily` stores the canonical family and *is* read
     through `toRectangular`, so the historical record survives only as its
     real-valued view.
8. **API hygiene (per-declaration).** Hide definition bodies (drop blanket
   `@[expose] public section`; expose one `_eq_iInf` characterization instead);
   name every lemma from its conclusion outward with the quantifier matching the
   statement; keep proof-only helpers `private`; the universe-`lift` `Cardinal`
   helper stays `private` unless independently useful.

The per-declaration name/disposition sketches live in the audit doc
(§5–§6, Appendix A name-change index) and are *sketches to verify against
adjacent Mathlib naming*, not a compile-ready patch. The **pre-PR declaration
checklist** (audit §14) is the per-declaration gate that complements this repo's
cluster-level acceptance gates.

## PR slicing (from the audit §4)

`A0` roadmap + representation decisions (this section) → `A1` `Basic` only, after
conventions settled → `A2` adjoint invariance + finite-dimensional singular-value
identification → `A3` min–max lower bound + Courant–Fischer support ending in the
actual min–max theorem → `A4` one canonical modulus, deleting `operatorAbs`
downstream. (`U1` LinearPMap unbounded-operator convergence and `S1+` Spectra
ports belong to the later roadmaps, not this one.) A PR must not mix a P0
convergence refactor with downstream theorem additions.

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

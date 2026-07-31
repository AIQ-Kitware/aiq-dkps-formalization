# Roadmap: finite-dimensional operator theory — the functional calculus, polar decomposition, singular values, and spectral subspaces

> ## ✅ DELIVERED — this topic is complete (verified 2026-07-31)
>
> **All 30 signatures in `Suggested.lean` are proved in the library.** This README is
> kept for its design rationale, which still describes why the theory is shaped the way
> it is — but it is a **record, not a plan**. Nothing below is outstanding work.
>
> The `sorry` bodies in `Suggested.lean` are deliberate and must stay: `ForTauCetiRoadmap.lean`
> exists *"so that a broken suggested signature is a build failure"*. The statements are
> the content; the bodies are placeholders by design.
>
> ### Where each signature landed
>
> * **`CourantFischer.lean`** — `abs_eigenvalues_sub_le_opNorm`, `eigenvalues_eq_iSup_iInf_re_inner`
> * **`Gram/Matrix.lean`** — `exists_linearIsometryEquiv_map_eq_of_inner_eq`, `rangeEquivOfInnerEq`
> * **`MoorePenroseInverse.lean`** — `eq_moorePenroseInverse_of_penrose`, `moorePenroseInverse`
> * **`OperatorModulus.lean`** — `modulus`
> * **`OrthogonalSeries.lean`** — `orthogonalFamily_of_pairwise_inner_eq_zero`
> * **`PartialIsometry.lean`** — `IsPartialIsometry`, `isPartialIsometry_iff_norm_map`
> * **`Polar/Decomposition.lean`** — `abs`, `exists_polar_decomposition_unitary`
> * **`Polar/PartialIsometry.lean`** — `polarInitial`, `polarInitial_orthogonal_eq_ker`, `polarPartial`, `polarPartial_comp_modulus`
> * **`PositiveSqrt.lean`** — `sqrt_unique`
> * **`Projection/Gap.lean`** — `norm_starProjection_sub_eq_max`
> * **`SelfAdjointFunctionalCalculus.lean`** — `selfAdjointFunctionalCalculus`, `selfAdjointFunctionalCalculus_apply_of_apply_eq_smul`, `sqrt`
> * **`Singular/System.lean`** — `apply_rightSingularBasis_eq_smul_leftSingularVector`, `eq_sum_singularValue_rankOne`, `exists_orthonormalBasis_extending_leftSingularVector`, `leftSingularVector`, `rightSingularBasis`
> * **`Spectral/Gap.lean`** — `SpectraSeparated`
> * **`Spectral/Subspace.lean`** — `IsEigenvectorAt`, `restrictedSpectrum`, `spectralSubspace`
>
> Verified name-by-name against `ForTauCeti/**` and `DavisKahan/**`, not by topic-level
> count. One caution for anyone re-running the check: `sqrt` is declared as
> `_root_.LinearMap.IsPositive.sqrt`, so a pattern anchored on `def sqrt` at line start
> reports it missing when it is present.


Spectral perturbation theory — the Davis–Kahan sin Θ theorems and everything in their
orbit — is written in a small, stable vocabulary: apply a real function to a symmetric
operator; factor an operator through its modulus; expand a rectangular map in its
singular system; measure the gap between two orthogonal projections; separate two
pieces of a spectrum. Mathlib has the *static* ingredients — the spectral theorem
(`LinearMap.IsSymmetric.eigenvalues` / `eigenvectorBasis`), positivity
(`LinearMap.IsPositive`), adjoints, the continuous functional calculus over `ℂ`, and
singular *values* (`LinearMap.singularValues`) — but **not the operator-theoretic
layer over `RCLike`**: no functional calculus for a symmetric `LinearMap` covering `ℝ`
and `ℂ` together, no positive square root with its uniqueness theory at that
generality, no partial-isometry API at all, no polar decomposition, no singular
*vectors*, no Moore–Penrose inverse, no sharp projector-difference identity, and no
shared vocabulary of spectral-separation hypotheses.

The goal is to **build the reusable theory of these objects**, not to race to a
handful of named theorems. The bar for "done": a researcher in matrix analysis or
spectral perturbation finds each object defined once, at its natural generality, with
its complete basic API — closure and composition laws, kernels and ranges, the
standard identities, the connections to existing Mathlib structures — so that the
headline results (uniqueness of the square root, the polar factorizations, the
singular expansion, the Penrose identities with their converse, the projector-gap
identity) are *consequences of a developed theory* rather than isolated endpoints. A
PR that proves a headline theorem but leaves the surrounding object without its basic
API is not yet what we want.

Suggested home: `TauCeti/Analysis/InnerProductSpace/` for the four developments below,
with the two scalar square-root estimates in `TauCeti/Analysis/SpecialFunctions/` and
the subspace-equality isometry lemma in `TauCeti/Analysis/Normed/Operator/`.

## Generality bar (decide these up front; do not silently specialize)

- **Scalars are `𝕜 : RCLike`; finite dimension exactly where the eigenbasis is
  used.** The functional calculus is a finite sum over
  `LinearMap.IsSymmetric.eigenvectorBasis`, so `[FiniteDimensional 𝕜 E]` is what makes
  the definition exist, not a convenience. Supporting material that needs neither the
  spectral theorem nor finite dimension (inner products of linear combinations,
  orthogonal series, the projection-gap geometry) must not assume them.
- **One square root, defined once.** The positive square root *is* the functional
  calculus at `Real.sqrt` — by definition, not by a bridging lemma. A reader must
  never meet two constructions of one object; the square-root-specific theory
  (uniqueness, kernel, range, the isometry-defect identity) attaches to that single
  definition.
- **Two moduli, and neither subsumes the other.** The square modulus
  `abs A = sqrt (A⋆ ∘ₗ A)` is `RCLike`-generic and finite-dimensional; the rectangular
  modulus `modulus T = CFC.sqrt (T.adjoint ∘L T)` is complex and works on complete
  spaces, because Mathlib registers the C⋆-algebra instances on `E →L[𝕜] E` only for
  `𝕜 = ℂ`. One is more general in the field, the other in the shape; deleting either
  loses theorems. They must be proved to agree exactly where both are defined
  (`abs_toContinuousLinearMap_eq_cfcAbs`).
- **One partial-isometry notion, stated algebraically.** `IsPartialIsometry u` is
  `u * star u * u = u` in a monoid with `StarMul`, so it applies verbatim to
  `E →ₗ[𝕜] E`, to `E →L[ℂ] E`, and to any C⋆-algebra. The geometric characterization —
  isometric on `(ker u)ᗮ`, zero on `ker u` — is a theorem, never the definition.
- **Three polar factorizations, one hierarchy.** Finite-dimensional endomorphisms over
  `RCLike` factor through a genuine unitary; a rectangular complex operator with
  invertible modulus factors through an isometry; a general bounded rectangular
  complex operator factors through a partial isometry. Dropping finite dimension costs
  the unitary; invertibility of the modulus buys an isometry back. All three are
  stated, each with its own theory.
- **Intrinsic, basis-free statements.** The singular system is built for a *linear map
  between spaces*, never for a matrix in a chosen pair of bases: the consumers
  (principal angles, unitarily invariant norms, spectral-subspace perturbation) are
  basis-free, and a matrix-mediated development would force each to carry a basis
  choice and prove independence of it.
- **Total operations at zero singular values.** The left singular vector is
  `σᵢ⁻¹ • A vᵢ` through total field inversion, so it is defined (and zero) at
  `σᵢ = 0`; orthonormality is asserted on the subtype of indices with nonzero singular
  value, and the singular relation `A vᵢ = σᵢ • uᵢ` holds *including* the zero case.
- **Shared separation predicates, defined once.** Several theorem families (sine,
  tangent, double-angle, Sylvester) state their hypotheses as a spectral separation.
  One family of named predicates serves all of them, so "the same gap hypothesis" is a
  checkable claim rather than an informal one.
- **Equalities where equalities hold.** The projector-difference identity
  `‖P − Q‖ = max (‖(1−Q)P‖, ‖(1−P)Q‖)` is an *equality*, with factor one and no
  equal-rank hypothesis. Do not weaken it to a two-sided estimate.

## What Mathlib already has (consume, and connect to)

- **The spectral theorem:** `LinearMap.IsSymmetric` with `eigenvalues` /
  `eigenvectorBasis`, `LinearMap.IsPositive` with `nonneg_eigenvalues`, adjoints, and
  the rank-one operators `InnerProductSpace.rankOne`. Part A is a finite sum of these.
- **The continuous functional calculus over `ℂ`:** `CFC.sqrt` and `CFC.abs` on
  `E →L[ℂ] E`. The C⋆-instances exist only for `𝕜 = ℂ`, which is why the `RCLike`
  calculus of Part A is build-here and why there are two moduli. Bridge to it; do not
  duplicate it.
- **Singular values:** `LinearMap.singularValues : ℕ →₀ ℝ` between finite-dimensional
  inner product spaces — zero-indexed, antitone, zero past the rank. Mathlib has the
  *values*; Part C adds the vectors, the two-sided spectrum bridge, and the
  pseudoinverse.
- **Projections:** `Submodule.starProjection` with `HasOrthogonalProjection`,
  `IsStarProjection`, `Submodule.reflection` — the raw material of Part D.
- **Orthogonal families:** `OrthogonalFamily`, whose only vector-level constructor
  `Orthonormal.orthogonalFamily` requires *unit* vectors — the hole Part D fills for
  the non-normalized families the singular expansion produces.
- **Gram matrices:** `Matrix.gram` and the matrix-side spectral theory; Part D's
  rigidity theorem characterizes `Matrix.gram` equality.

---

## Part A — the functional calculus, the positive square root, and the two moduli

**Topic T01 of the candidate design** — the base of the roadmap: Parts B, C and D all
consume it, and nothing in it rests on anything but Mathlib.

**Objects.** The finite self-adjoint functional calculus
`selfAdjointFunctionalCalculus hT f = ∑ᵢ f(λᵢ) • rankOne eᵢ eᵢ` for a symmetric
endomorphism over `RCLike`; the positive square root `sqrt hT`, *defined as* the
calculus at `Real.sqrt`; the rectangular complex modulus
`modulus T = CFC.sqrt (T.adjoint ∘L T)`; and the supporting algebra — the expansion of
`⟪∑ aᵢ • vᵢ, ∑ bⱼ • vⱼ⟫` over pairwise inner products, spans of orthonormal
subfamilies, the eigenvector cross-term identity
`⟪eᵢ, (S−T) fⱼ⟫ = (μⱼ − λᵢ) ⟪eᵢ, fⱼ⟫`, and two scalar square-root estimates near `1`.

**API to develop.**
- The calculus: diagonal action on the eigenbasis; symmetry of the result; `id`
  recovers `T`; functions agreeing on the eigenvalues give equal operators;
  composition is pointwise multiplication; the *eigenvector-stable* form —
  `T x = λ • x` implies `calculus f x = f λ • x`, which is what makes the calculus
  well-behaved on repeated eigenspaces; the commutant property (anything commuting
  with `T` commutes with every `calculus f`).
- The square root: positive, symmetric, squares to `T`; `ker (sqrt hT) = ker T`,
  `range (sqrt hT) = range T`; the isometry-defect identity
  `‖sqrt hT x‖² = re ⟪T x, x⟫`; invertible when `T` is.
- The rectangular modulus: nonneg, self-adjoint, `|T|² = T⋆T`; the pointwise isometry
  `‖|T| x‖ = ‖T x‖` with its kernel corollary; `‖|T|‖ = ‖T‖`; composition norm laws;
  the characterization as the unique nonneg square root of the Gram operator.
- Courant–Fischer and Weyl: the quadratic form in the eigenbasis, the min–max
  equality, eigenvalue monotonicity, the perturbation bound.

**Milestone — uniqueness, at both layers.** The square root is the *unique* positive
operator squaring to `T` (Horn–Johnson 7.2.6); and the calculus itself is the unique
symmetric operator acting as `f (λᵢ)` on each eigenvector of `T` — the
characterization a reviewer looks for first.

```lean
noncomputable def selfAdjointFunctionalCalculus
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (f : ℝ → ℝ) : E →ₗ[𝕜] E

theorem sqrt_unique {T S : E →ₗ[𝕜] E} (hT : T.IsPositive) (hS : S.IsPositive)
    (h : S ∘ₗ S = T) : S = sqrt hT
```

**Milestone — Courant–Fischer and Weyl.** The `k`-th sorted eigenvalue is the sup–inf
of the Rayleigh quotient over `(k+1)`-dimensional subspaces (Horn–Johnson 4.2.6), and
a symmetric perturbation moves each eigenvalue by at most the operator norm:

```lean
theorem abs_eigenvalues_sub_le_opNorm
    {T S : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : finrank 𝕜 E = n) (k : Fin n) :
    |hT.eigenvalues hn k - hS.eigenvalues hn k| ≤
      ‖LinearMap.toContinuousLinearMap (T - S)‖
```

**Milestone — agreement with the continuous functional calculus.** Over `ℂ` the
`RCLike` calculus and Mathlib's CFC compute the same operator: at `Real.sqrt` this is
the bridge `abs_toContinuousLinearMap_eq_cfcAbs`; the statement for a general
continuous `f` lets a consumer move between the two calculi freely, and is a target
here, not a remark.

**Acceptance examples.** `calculus id = T`; the calculus of a constant is that
multiple of the identity; on a concrete diagonal operator the square root and modulus
take their expected diagonal values; the Weyl bound is sharp for a rank-one
perturbation of the identity.

## Part B — polar decomposition and partial isometries

**Topic T02 of the candidate design** — every operator factors as an isometric part
times its modulus. That statement appears in two genuinely different forms, and the
first question a reviewer will ask — why both — has a precise answer: the two forms
differ on three axes, and each direction of generalization loses something.

| | square decomposition | rectangular decomposition |
|---|---|---|
| scalars | `[RCLike 𝕜]` — **ℝ and ℂ** | **ℂ only** |
| dimension | `[FiniteDimensional]` | `[CompleteSpace]` — infinite allowed |
| shape | `E →ₗ[𝕜] E`, endomorphism | `E →L[ℂ] F`, rectangular |
| isometric factor | genuine **unitary** `E ≃ₗᵢ[𝕜] E` | **partial isometry** |

The obstruction is upstream, in Part A: the two moduli have complementary limitations,
so there is no single modulus and hence no single polar decomposition subsuming both.
The two decompositions share exactly one piece of vocabulary — the algebraic
partial-isometry predicate — and nothing else.

**Objects.** `IsPartialIsometry`; the square modulus `abs A = sqrt (A⋆ ∘ₗ A)`; the
polar factor `polarFactor A` (the partial isometry `|A| x ↦ A x` extended by zero) and
its unitary witnesses (`polarUnitaryEquiv`, canonical as `A |A|⁻¹` when `A` is
invertible; `choosePolarUnitary` in general); on the rectangular side, the initial
space `polarInitial M` (the closure of `range |M|`), the partial isometry
`polarPartial M`, and the bounded-below isometry `polarIsometryOfIsUnitModulus`; the
near-isometry factorization; and Davis's intertwining unitary for a pair of complete
orthogonal projection families (`OrthoProjFamily`, `intertwiningUnitary`).

**API to develop.**
- The partial-isometry dictionary: `star u * u` is a star projection; closure under
  `star`; isometries are partial isometries; the operator characterization — `u` is a
  partial isometry iff it is norm-preserving on `(ker u)ᗮ` (Conway VI.3.2).
- The square decomposition: `‖|A| x‖ = ‖A x‖`, `ker (abs A) = ker A`,
  `range (abs A) = (ker A)ᗮ`; `polarFactor` with `ker = ker A`, `range = range A`,
  partial isometry, and the defining property `polarFactor A (|A| x) = A x`; the
  normal case (`A` commutes with `|A|`); uniqueness of the polar factor among
  unitary-times-positive factorizations of an invertible `A`.
- The rectangular decomposition: `polarPartial M ∘L |M| = M`; isometric on
  `polarInitial M`, zero on its complement; `ker (polarPartial M) = (polarInitial M)ᗮ`;
  the adjoint formulas and the final space `polarFinal M = closure (range M)`;
  uniqueness: any `V` with `V ∘L |M| = M` vanishing on `(polarInitial M)ᗮ` is
  `polarPartial M`.
- The bounded-below rung: when `|M|` is a unit the factor is an isometry outright,
  with the quantitative comparison `‖M − W‖ ≤ ‖|M| − 1‖`. This rung stays separate
  from the general one: bounded-below is the hypothesis perturbation estimates
  actually have, and under it the conclusion is strictly stronger.

**Milestone — the two decompositions.** The second statement below is the content of
the general one: the initial space is *proved* equal to `(ker M)ᗮ`, never taken as its
definition.

```lean
theorem exists_polar_decomposition_unitary (A : E →ₗ[𝕜] E) :
    ∃ U : E ≃ₗᵢ[𝕜] E, A = (U : E →ₗ[𝕜] E) ∘ₗ abs A

theorem polarInitial_orthogonal_eq_ker (M : E →L[ℂ] F) :
    (polarInitial M)ᗮ = LinearMap.ker M.toLinearMap
```

**Milestone — the near-isometry factorization.** A real finite-dimensional map whose
quadratic form is uniformly `δ`-close to the identity (`δ < 1`) factors as
`M = W ∘ₗ S` with `W` an isometry equivalence and `S` the positive square root of the
Gram operator, with `‖S x − x‖ ≤ δ‖x‖`; consequently `‖M − W‖ ≤ 2δ` for `δ ≤ 1/2`.
This is what a perturbation argument needs and what the exact decompositions cannot
give.

**Milestone — Davis's intertwining unitary.** For two complete orthogonal families of
projections `(Pⱼ)`, `(P'ⱼ)` satisfying Davis's non-degeneracy condition, the block
polar factors assemble into a unitary `U` with `U ∘ₗ Pⱼ = P'ⱼ ∘ₗ U` for every `j` —
this part's modulus-inverse-times-operator construction applied to a projection pair.

**Acceptance criteria.** That the two decompositions are not redundant (the table
above — in particular that the general one is `ℂ`-only); that `IsPartialIsometry` is
stated algebraically, so the shared vocabulary really is shared; and that
`polarInitial M = (ker M)ᗮ` is a theorem.

## Part C — singular values and the singular system

**Topic T03 of the candidate design** — Mathlib has `LinearMap.singularValues`; this
part adds everything around it, and each layer answers a different question:

| layer | what is missing upstream |
|---|---|
| accessor | a `ContinuousLinearMap`-level view of `singularValues` — naming surface only |
| spectrum bridge | that `A⋆A` and `AA⋆` share their nonzero spectrum **with multiplicity** |
| singular system | the singular **vectors** — Mathlib has the values, not the system |
| Moore–Penrose | the pseudoinverse, with all four Penrose identities and the converse |

The accessor exists so that operator-norm consumers (approximation numbers, Ky Fan
norms, Eckart–Young) never spell `T.toLinearMap.singularValues` in a public statement;
its lemmas are one-line delegations, and a reviewer should confirm exactly that — any
lemma there with real content belongs at the `LinearMap` level instead.

**Objects.** The right singular basis `rightSingularBasis A` (the sorted orthonormal
eigenbasis of `A⋆A`); the left singular vectors
`leftSingularVector A i = σᵢ⁻¹ • A vᵢ` (total, zero at zero singular values); the
Moore–Penrose inverse `moorePenroseInverse A`, built from the singular system with
coefficient `(σᵢ²)⁻¹` against rank-one maps.

**API to develop.**
- The spectrum bridge: `A⋆A` and `AA⋆` are symmetric and positive; their sorted
  eigenvalue lists agree at every index below both dimensions (no relation between the
  dimensions required — both lists are zero past the rank); consequently
  `singularValues A.adjoint = singularValues A`. This is what lets a rectangular map
  carry *one* singular sequence rather than two.
- The singular system: `A⋆A` acts on `vᵢ` by `σᵢ²`; the singular relation
  `A vᵢ = σᵢ • uᵢ` including the zero case; the `uᵢ` with `σᵢ ≠ 0` are orthonormal and
  are eigenvectors of `AA⋆` at `σᵢ²`; `A⋆ uᵢ = σᵢ • vᵢ`; the singular expansion of
  `A x` and the rank-one reconstruction of `A`; the extension of the nonzero left
  family to an orthonormal basis of the codomain — the statement downstream consumers
  actually need, and not automatic for a rectangular map.
- Moore–Penrose: action on the singular basis; the four Penrose identities
  (`A A⁺ A = A`, `A⁺ A A⁺ = A⁺`, symmetry of `A A⁺` and of `A⁺ A`); left/right inverse
  behaviour under injectivity/surjectivity.

**Milestone — the singular expansion.**

```lean
theorem eq_sum_singularValue_rankOne (A : E →ₗ[𝕜] F) :
    A = ∑ i : Fin (finrank 𝕜 E),
      ((A.singularValues i : ℝ) : 𝕜) •
        (InnerProductSpace.rankOne 𝕜
          (leftSingularVector A i) (rightSingularBasis A i)).toLinearMap
```

**Milestone — the Penrose characterization.** Any `B` satisfying all four identities
*is* the constructed pseudoinverse. Without this converse the construction is merely
*a* generalized inverse; with it, the name is earned.

```lean
theorem eq_moorePenroseInverse_of_penrose (A : E →ₗ[𝕜] F) (B : F →ₗ[𝕜] E)
    (h1 : A ∘ₗ B ∘ₗ A = A) (h2 : B ∘ₗ A ∘ₗ B = B)
    (h3 : (A ∘ₗ B).IsSymmetric) (h4 : (B ∘ₗ A).IsSymmetric) :
    B = moorePenroseInverse A
```

**Acceptance criteria.** That the accessor layer has no mathematical content; that no
statement of the singular system mentions a basis of the ambient spaces beyond the
constructed singular one; that the uniqueness converse is proved, not just the four
identities; that zero singular values are handled in the singular relation — the case
a rectangular treatment gets wrong first.

## Part D — Gram matrices, orthogonal projections, and spectral subspaces

**Topic T04 of the candidate design** — the vocabulary the perturbation theory is
stated in, and the one sharp identity that vocabulary exists for:

```
‖P − Q‖ = max (‖(1−Q) P‖, ‖(1−P) Q‖)        for orthogonal projections P, Q
```

Perturbation arguments naturally produce two *one-sided* estimates; this equality
upgrades the pair to a bound on `‖P − Q‖` itself with factor one and **no equal-rank
hypothesis**. Without it a development loses a factor of two or carries a rank
condition through every statement. The proof is the block decomposition
`(P−Q)² = P(1−Q)P + (1−P)Q(1−P)` with the C⋆-norm identities, scalar-generic over
`RCLike`.

**Objects.** The isometric first isomorphism theorem `rangeEquivOfInnerEq` (two maps
out of a common module with equal pullback inner products have canonically isometric
ranges) and the Gram-rigidity theorems it yields; reflections, diagonal and
off-diagonal parts of an operator relative to `U ⊕ Uᗮ`; the symmetric and directed
projection gaps; invariant and reducing subspaces; restricted spectra with the
canonical spectral subspace `spectralSubspace A Ω` and projector
`spectralProjection A Ω`; the separation predicates (`SpectraSeparated`, `HybridGap`,
`InternalGap`, `TwoBlockFormGap`, `IntervalExteriorGap`, `OrderedGap`,
`OrderedInternalGap`); the orthogonal-series constructor for pairwise orthogonal, *not
necessarily unit*, vectors.

**API to develop.**
- Gram rigidity: equal pullback inner products give equal kernels and the range
  isometry; for families, equal pairwise inner products give a span-to-span isometry
  sending `φ i ↦ ψ i`, extended (in finite dimension) to an isometry equivalence of
  the ambient space; the `Matrix.gram` characterization as an iff.
- Projection geometry: projections onto spans of orthonormal families; reflections
  with involutivity, isometry, and commutation-when-reducing; the diagonal/off-diagonal
  calculus (`2·diag = A + R A R`, `2·offdiag = A − R A R`).
- The gap: symmetry, the directed-gap comparison, the max identity above.
- Invariance: invariant and reducing kept as *distinct named notions* (they coincide
  for symmetric operators, and that coincidence is a theorem); restriction of a
  symmetric operator to an invariant subspace and its restricted spectrum; the
  quadratic-form bridges `SpectrumIn A U (Iic a) → re ⟪A x, x⟫ ≤ a‖x‖²` on `U`, with
  their converses. Reducing subspaces stay independent of all perturbation theory, so
  they are separately reviewable and separately consumable.
- Separation predicates: the implications among them (ordered implies absolute;
  spectral inclusion on opposite sides of a cut gives the ordered internal gap), so
  that theorem families with different hypotheses are comparable.
- Orthogonal series: a pairwise-orthogonal family of vectors spans an orthogonal
  family of lines (the constructor Mathlib's unit-vector hypothesis blocks);
  Pythagoras for finite sums; summability iff square-norm summability; Parseval for a
  family with a specified sum. The families this roadmap produces are `σᵢ • uᵢ` —
  orthogonal but not normalizable when some `σᵢ` vanish, which is why the unit-vector
  constructor does not suffice.

**Milestone — the sharp gap identity, and Gram rigidity.**

```lean
theorem norm_starProjection_sub_eq_max (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖(U.starProjection - V.starProjection : E →L[𝕜] E)‖ =
      max ‖(1 - V.starProjection) ∘L U.starProjection‖
          ‖(1 - U.starProjection) ∘L V.starProjection‖

theorem exists_linearIsometryEquiv_map_eq_of_inner_eq
    [FiniteDimensional 𝕜 E] {φ ψ : ι → E}
    (h : ∀ i j, ⟪φ i, φ j⟫_𝕜 = ⟪ψ i, ψ j⟫_𝕜) :
    ∃ W : E ≃ₗᵢ[𝕜] E, ∀ i, W (φ i) = ψ i
```

**Acceptance criteria.** That the gap identity is an equality with no equal-rank
hypothesis; that the separation predicates are shared, not parallel definitions with
one name; that reducing subspaces import no perturbation theory; that the
orthogonal-series constructor fills the non-unit-vector hole rather than duplicating
`OrthogonalFamily`.

## Dependency ordering

Part A comes first: Parts B, C and D each consume it and nothing else — B needs both
moduli, C needs the Gram operator's eigenbasis and the eigenvalue-counting lemmas, D
needs the eigenvalue API behind its quadratic-form bridges. B, C and D are mutually
independent and can proceed in parallel once A lands. **This roadmap is independent:**
it rests only on Mathlib, and it is the foundation the subsequent roadmaps (norms and
angles, operator ideals, and the spectral-subspace perturbation endpoint) cite as
their prerequisite.

## References

- R. A. Horn, C. R. Johnson, *Matrix Analysis*, 2nd ed., Cambridge (2013) — Thm 7.2.6
  (unique positive square root), 7.2.7(b), 7.3.1 (polar decomposition), 4.2.6
  (Courant–Fischer), Weyl's perturbation inequality.
- J. B. Conway, *A Course in Functional Analysis*, 2nd ed. — §VI.3 (partial
  isometries, VI.3.2, VI.3.9); M. Reed, B. Simon, *Methods of Modern Mathematical
  Physics I*, §VI — the polar decomposition on Hilbert space.
- C. Davis, *The rotation of eigenvectors by a perturbation*, J. Math. Anal. Appl.
  **6** (1963) — the intertwining unitary and the projection geometry.
- R. Penrose, *A generalized inverse for matrices*, Proc. Cambridge Philos. Soc.
  **51** (1955) — the four identities and the uniqueness characterization.
- T.-Y. Chien, S. Waldron, *A characterization of projective unitary equivalence of
  finite frames and applications*, SIAM J. Discrete Math. **30** (2016),
  arXiv:1312.5393 — Gram rigidity in its frame-theoretic form.

## Provenance and decision record

*Where the staged material came from and how its conventions were decided; not part of
the specification, and a reader can skip it.*

- **Origin.** All four parts are staged, proof-complete, in the `ForTauCeti/` library
  of the Davis–Kahan/DKPS formalization (Kitware, Inc.), namespaces `TauCeti.*`:
  Part A is topic T01 (nine modules), Part B topic T02 (six), Part C topic T03 (four),
  Part D topic T04 (eight); `scripts/check_tauceti_roadmap_topics.py --topic T01`
  (… T04) lists them and validates the partition. The import graph confirms the
  ordering above: no T02/T03/T04 module imports anything outside Mathlib and T01.
- **Mathlib review history.** The Gram-matrix material was submitted as mathlib4
  PR #40567 and reshaped on @wwylele's review (the linear-combination identity moved
  to its natural home; the quotient plumbing became the standalone
  `rangeEquivOfInnerEq`). After the PR closed — Mathlib is no longer the destination —
  the module was generalized *past* what the review asked for. Lane HDR-DEST re-aimed
  the library's headers at Tau Ceti while keeping that history.
- **Lane decisions (2026-07-29/30).** "One square root, defined once" is lane
  T01-SQRT: the root had been a second definition proved equal by `rfl`, and the
  duplicate was collapsed into the calculus. "Two moduli, neither subsumes the other"
  is lane MODULUS-DEDUP, which examined merging them and declined (different shape and
  different field); the two polar decompositions are the same decision one level up. A
  one-concept-one-name rename of the square modulus was considered and declined (71
  call sites, consistency not correctness); if a Tau Ceti reviewer asks, that is the
  measured cost.
- **A module reassignment.** Davis's intertwining unitary was listed under the Stone's
  theorem topic (T13) until 2026-07-30, on no stronger ground than the word "unitary".
  It is a polar construction with only Part-B dependencies, and moving it here removed
  the sole T13→T02 edge, making the Stone roadmap independent.
- **Naming notes.** `IsInvariant` was renamed from `Reduces` after a collision with
  the strictly stronger `ContinuousLinearMap.Reduces`; the projection onto a span of
  basis vectors was renamed from `spectralProjection` (it is not one) to
  `spanIndicesProjection`. The old single-topic T01 draft also listed the square
  modulus and polar decomposition among its own contents; in the staged partition they
  live in T02 modules, and this roadmap follows the partition (Part B).
- **Ladder position.** T01 is rung G of the staged submission ladder; its direct
  dependents are T02, T03, T04, T09, T17, T18 and T19, and T04's are T05, T06, T07,
  T15a, T16 and T17 — between them, most of the finite-dimensional library. Written
  2026-07-30 under lane ROADMAP-WRITE; consolidated from the four single-topic drafts.

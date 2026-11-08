# 125000 — Non-isometric frames and unequal dimensions

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `015000`, `017000`, `035000`, `108000`, `124000`. **Next:** `126000`, weak spectral gaps and Hilbert–Schmidt estimates.

<!-- BEGIN SPOKEN LECTURE -->

# Non-isometric frames and unequal dimensions

A trial subspace is often represented by orthonormal columns, but computational trial frames may be scaled, nonorthogonal, or redundant. The Gram operator measures their failure to have orthonormal coordinates, and that error affects how residual estimates are normalized.

Davis and Kahan's Theorem six point one keeps the trial map itself rather than silently replacing it with an isometry. It permits a non-isometric frame and different dimensions of the trial and exact subspaces. Its additional factor, epsilon, comes directly from a lower bound on that frame.

## Distinguish a frame from its range

Let F be a coordinate Hilbert space and H the ambient Hilbert space. A trial frame E zero is a bounded linear map from F to H. Its range is the trial subspace, assuming it has closed range as guaranteed here by a positive lower bound.

If E zero is an isometry, the length of every coordinate vector is preserved. But for a general frame that is false. The same ambient trial subspace can be described by many different frames, such as an orthonormal frame multiplied by an invertible matrix.

We assume there is a positive epsilon such that the length of E zero x is at least epsilon times the length of x for every coordinate vector x. This says the frame does not collapse any coordinate direction. It also says the inverse on its range has norm at most one over epsilon.

Notice that epsilon is a lower bound on lengths. If an implementation instead stores the smallest eigenvalue of E zero adjoint E zero, then the corresponding length bound is its square root. Mixing these conventions would give an incorrect factor.

## Obtain orthonormal coordinates by polar decomposition

Take the positive modulus of E zero, the square root of E zero adjoint E zero. The lower-frame hypothesis implies this modulus is bounded below by epsilon and therefore has a bounded inverse.

Write the polar decomposition of E zero as W times its modulus. Because E zero is injective with closed range, W is an isometry of F onto the trial subspace. This is a canonical way to normalize the frame without changing its range.

If the smallest singular value of E zero is epsilon, then the inverse of its modulus has operator norm at most one over epsilon. That one inequality will explain the entire normalization penalty.

## Choose exact spectral coordinates

Let A be a possibly unbounded self-adjoint operator on H. Choose an exact reducing spectral decomposition with an exact selected component and its orthogonal complement. Let F one be an isometric coordinate map into that complementary component, and let Lambda one denote the restricted operator there.

Choose a self-adjoint trial coordinate operator A zero on F. Suppose E zero maps the trial coordinates into the domain of A and satisfies the residual equation: A applied to E zero equals E zero followed by A zero, plus a bounded residual map R.

The domain clause is necessary if A is unbounded. We cannot even write the residual for all coordinates unless E zero lands in the domain. The exact complement is also required to reduce A, so its restricted operator is well-defined on the appropriate domain.

## Compress the residual equation

Apply F one adjoint to the residual identity. Because F one identifies the exact complementary reducing space, F one adjoint A E zero becomes Lambda one applied to F one adjoint E zero.

Define X as F one adjoint E zero. The remaining term is X A zero. Thus we obtain the Sylvester equation: Lambda one X minus X A zero equals F one adjoint R.

The spectral hypothesis is a genuine ordered or interval-versus-exterior Sylvester gap of size delta between A zero and Lambda one. Under that hypothesis, the applicable ideal estimate gives delta times the ideal norm of X no greater than the ideal norm of R. Projection by F one adjoint does not increase the relevant singular values.

But X still contains the nonorthonormal scaling of E zero. It is not yet the intrinsic sine map of the trial subspace.

## Remove the scaling, and find epsilon

Replace E zero by its polar factorization W times the modulus. Then X equals F one adjoint W followed by that modulus.

The map F one adjoint W is the directed escape from the normalized trial space into the exact complementary space. Its singular values are the directed sines. Let us call it S.

We have X equals S times the modulus. Multiply on the right by the inverse modulus. Then S equals X times that inverse. Since the inverse has norm at most one over epsilon, every supported unitarily invariant ideal norm obeys epsilon times the norm of S at most the norm of X.

Combine this with the Sylvester bound. The conclusion is delta times epsilon times the directed sine norm no greater than the residual norm.

The two factors have different sources. Delta comes from spectral separation. Epsilon comes from frame conditioning. Neither can be omitted without changing the data being estimated.

## Check the constant in one dimension

Take the ambient plane with A diagonal, with eigenvalues zero and d, where d is positive. Choose the exact selected subspace as the horizontal axis and its complement as the vertical axis.

Let the trial coordinate space be one-dimensional. Map the unit coordinate to epsilon times the unit vector at angle theta above the horizontal axis. Take the trial coordinate operator A zero to be zero. The residual is simply A applied to the trial vector, which has length epsilon d sine theta.

Here the cross operator X has length epsilon sine theta and the normalized directed sine has value sine theta. The gap delta between the trial zero and the complementary eigenvalue d is exactly d.

Thus delta epsilon sine theta equals the residual norm. The estimate is sharp for every positive epsilon and every theta between zero and a right angle.

If we had omitted epsilon, shrinking the frame would make the residual arbitrarily small while the subspace angle stayed fixed. The inequality would become false. The factor is therefore mathematically necessary.

## Unequal dimensions require a direction

Now consider a line U inside a plane V in three-dimensional space. The directed sine from U toward V is zero because every vector of U lies in V. But the reverse directed sine from V toward U is one, since V contains a direction perpendicular to U.

An ambient projection difference registers that missing direction and has norm one. A theorem based only on the trial map E zero and the complementary part of the exact decomposition generally controls the first directed sine, not the entire ambient projection difference.

Theorem six point one therefore allows the trial and exact selected coordinates to have different dimensions without pretending that both directed angles are equal. The conclusion is stated for a representative having the appropriate directed sine singular values.

This is also why a convenient rectangular operator representative is allowed in the formal statement. Different source and target coordinate spaces can carry the same nonzero singular-value list, possibly supplemented by zeros. The ideal norm depends on that list rather than on how the representative is embedded.

## What the theorem does and does not promise

A positive lower-frame bound does not itself establish spectral separation. A small residual does not determine which exact cluster to compare against. The theorem needs the self-adjoint coordinate operators, exact spectral decomposition, domain-aware residual, positive frame bound, and a legitimate Sylvester gap.

In a symmetric ideal one must also assume the residual belongs to the ideal and prove that the sine representative belongs to it. That membership is part of the conclusion, not a default property of arbitrary bounded operators.

The original Section six theorem uses interval-versus-exterior spectral separation, with either ordering allowed. A modern proof layer may express the same analytic work through a form-bounded gap interface. We distinguish the source hypothesis from the generalization.

## Summary

The result can be reconstructed from three moves. Compress the residual to obtain a Sylvester equation. Bound the crossed operator X by the residual using the spectral gap. Normalize the frame by polar decomposition, paying exactly the inverse lower-frame bound.

The formula is delta epsilon times the directed sine norm at most the residual norm.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)


For \(E_0:F\to H\), the Lean predicate `LowerFrameBound E₀ ε` records \(\|E_0x\|\ge\varepsilon\|x\|\). Polar decomposition gives \(E_0=W|E_0|\), with \(W^*W=I_F\) and \(\||E_0|^{-1}\|\le1/\varepsilon\). The raw crossed map \(X=F_1^*E_0\) satisfies a domain-aware Sylvester equation; the normalized directed sine is represented by \(S=F_1^*W=X|E_0|^{-1}\). Thus
\[\delta\,\varepsilon\,N(S)\le N(R).\]
`SinThetaRepresentativeAcross` permits equivalent rectangular realizations, while `IsTrialResidualEquation` and `IsExactSpectralDecomposition` encode the actual domain and exact-reduction obligations. The paper-facing spectral condition is interval/exterior separation, rather than an arbitrary `PairwiseSpectrumGap`.


### Exact Lean declaration excerpts


`DavisKahan/Sources/DavisKahan1970/Theorem61.lean` — `theorem6_1_complex` (exact declaration header; proof body omitted):

```lean
theorem theorem6_1_complex
    {E₀' F₀' : Type v}
    [NormedAddCommGroup E₀'] [InnerProductSpace ℂ E₀'] [CompleteSpace E₀']
    [NormedAddCommGroup F₀'] [InnerProductSpace ℂ F₀'] [CompleteSpace F₀']
    (N : SymmetricNormingFunction)
    (A : E →ₗ.[ℂ] E) (A₀ : F →ₗ.[ℂ] F) (Λ₁ : G →ₗ.[ℂ] G)
    (E₀ : F →L[ℂ] E) (F₀ : H →L[ℂ] E) (F₁ : G →L[ℂ] E) (R : F →L[ℂ] E)
    (hA : IsSelfAdjoint A) (hA₀ : IsSelfAdjoint A₀) (hΛ₁ : IsSelfAdjoint Λ₁)
    (htrial : IsTrialResidualEquation A A₀ E₀ R)
    (hexact : IsExactSpectralDecomposition A Λ₁ F₀ F₁)
    {ε : ℝ} (hε : 0 < ε) (hframe : LowerFrameBound E₀ ε)
    {δ : ℝ} (hδ : 0 < δ) (hgap : FormBoundedSylvesterGap A₀ Λ₁ δ)
    (S : SinThetaRepresentativeAcross (E₀ :=
```


`DavisKahan/Sources/DavisKahan1970/Section6SourceScope.lean` — `theorem6_1_printedGap_sourceExact_complex` (exact declaration header; proof body omitted):

```lean
theorem theorem6_1_printedGap_sourceExact_complex
    [NormedAddCommGroup E₀'] [InnerProductSpace ℂ E₀'] [CompleteSpace E₀']
    [NormedAddCommGroup F₀'] [InnerProductSpace ℂ F₀'] [CompleteSpace F₀']
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (N : NormalizedUnitaryInvariantNorm.{0, v} ℂ)
    (A : E →ₗ.[ℂ] E) (A₀ : F →ₗ.[ℂ] F) (Λ₁ : G →ₗ.[ℂ] G)
    (E₀ : F →L[ℂ] E) (F₀ : H →L[ℂ] E) (F₁ : G →L[ℂ] E) (R : F →L[ℂ] E)
    (hA : IsSelfAdjoint A) (hA₀ : IsSelfAdjoint A₀) (hΛ₁ : IsSelfAdjoint Λ₁)
    (htrial : IsTrialResidualEquation A A₀ E₀ R)
    (hexact : IsExactSpectralDecomposition A Λ₁ F₀ F₁)
    {ε : ℝ} (hε : 0 < ε) (hframe : LowerFrameBound E₀ ε)
    {δ : ℝ} (hδ : 0 < δ) {β α : ℝ} (hβα : β ≤ α)
    (hgap : DavisKahan.Sylvester.RealSpectrumIntervalExteriorGap A₀ Λ₁ β α δ)
    (S : SinThetaRepresentativeAcross (E₀ :=
```



**Mapping.** `E₀` is the bounded, potentially non-isometric trial map; `F₀` and `F₁` give exact spectral coordinates. `A`, `A₀`, and `Λ₁` are the closed self-adjoint ambient, trial, and complementary operators. `htrial` and `hexact` carry domain and reduction data; `hframe` and `hε` expose the normalization factor. `S` specifies a singular-value-equivalent sine representative; `hR` asserts ideal membership.


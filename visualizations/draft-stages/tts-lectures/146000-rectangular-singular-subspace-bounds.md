# 146000 — Rectangular singular-subspace bounds

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `023000`, `034000–038000`, `052000–054000`, `106000–113000`. **Next:** `147000`.

<!-- BEGIN SPOKEN LECTURE -->

# Rectangular singular-subspace bounds

The original Davis–Kahan theorems concern self-adjoint operators and their spectral subspaces. Many data matrices are rectangular, and their most informative subspaces are spanned by left or right singular vectors instead of eigenvectors of the original map. Rectangular singular-subspace perturbation can be reduced to self-adjoint spectral theory in two ways: Hermitian dilation and positive Gram operators.

## One rectangular map, two subspaces

Let A map a q-dimensional input space to a p-dimensional output space. Its singular-value decomposition pairs a right singular vector v with a left singular vector u and a nonnegative singular value sigma. The defining equations say that applying A to v gives sigma times u, and applying the adjoint of A to u gives sigma times v.

The right singular vectors live in the input space. The left singular vectors live in the output space. If the two spaces have different dimensions, even their ambient geometries differ. We must therefore choose explicitly which subspace error we want to estimate.

Let A hat equal A plus a rectangular perturbation D. We may want the principal angles between selected right singular subspaces of A and A hat. Or we may want the corresponding left-side angles. These two errors are not generally equal, even when they come from the same singular values.

For a rectangular map A, A adjoint A acts on the input, while A A adjoint acts on the output. Their nonzero eigenvalues are the squared singular values. This converts both singular-subspace problems into self-adjoint eigen-subspace problems, provided we keep track of how the perturbation affects each Gram operator.

## Perturbing the right Gram operator

Write G for A adjoint A and G hat for A hat adjoint A hat. Expand A hat as A plus D. Then G hat minus G equals A adjoint D plus D adjoint A plus D adjoint D.

Take operator norms. The first two terms are at most the product of the norms of A and D. The last is at most the square of the norm of D. Consequently the Gram perturbation norm is bounded by two times the norm of A, plus the norm of D, all multiplied by the norm of D.

If the largest singular value of A is sigma one, its operator norm is sigma one. Thus the bound is the quantity two sigma one plus perturbation norm, multiplied by perturbation norm.

The same calculation works for the left Gram operator. In Frobenius norm, each product obeys a mixed norm inequality: the Frobenius norm of A adjoint D is at most the operator norm of A times the Frobenius norm of D. Therefore the Gram perturbation's Frobenius norm has the analogous bound with the final perturbation norm replaced by its Frobenius norm.

These estimates are algebraic. No eigenvalue ordering or spectral gap was needed yet. The gap enters when we apply a sine-theta theorem to the Gram operators.

## The squared spectral gap

Suppose we select a consecutive block of singular values, from index r through index s. They correspond to an eigenvalue block of G consisting of their squares. To separate the selected block from the other right Gram eigenvalues, we need gaps at its upper and lower boundaries. The natural denominator is the smaller of these two squared-singular-value gaps.

For example, if the singular values are five, three, and one, and we select the middle one, the squared eigenvalues are twenty-five, nine, and one. The upper squared gap is sixteen, and the lower gap is eight. The relevant boundary separation is eight.

This may look different from a gap between singular values themselves. It is. The difference of two squares equals the difference of the singular values times their sum. A theorem expressed through the Gram operator is sensitive to this product.

We must also handle zero singular values. For a rectangular matrix with rank below the input dimension, the right Gram operator has a genuine zero eigenspace. A selected singular block ending at the last positive singular value is still separated from that zero eigenspace only by the square of the last positive singular value.

A rank-boundary gap must be computed in the full ambient right or left Gram space, including zero eigenvalues beyond the positive rank. Treating the next eigenvalue as infinitely separated while an ambient zero eigenvalue remains gives an invalid boundary convention.

## Passing from Gram perturbation to sine bounds

Apply the self-adjoint perturbation framework to G and G hat. Under a positive population boundary gap Delta and the hypotheses identifying the selected singular blocks, a Frobenius principal-sine estimate can be written in terms of the Gram perturbation.

The resulting rectangular singular-subspace estimate has a factor two multiplying the quantity two sigma one plus the norm of D. That quantity is then multiplied by the smaller of square root of the selected block dimension times the operator norm of D, and the Frobenius norm of D, and divided by Delta.

The constants and the particular gap assumptions belong to the theorem; one should not silently replace the precise ambient boundary gap with a gap involving the perturbed singular values. The bound is useful because it depends only on the original matrix's singular-value separation, plus the size of the perturbation.

If the right singular block has dimension d, the sine distance here is the Frobenius norm of its list of principal sines. The operator norm of the sine map instead measures only the largest principal sine. They are related, but their dimension factors differ.

## A concrete two-by-three calculation

Take a two-by-three matrix whose first row is three, zero, zero, and whose second row is zero, one, zero. Its nonzero singular values are three and one. The right Gram operator is diagonal with eigenvalues nine, one, and zero. The left Gram operator is diagonal with eigenvalues nine and one.

Now perturb only the entry in the first row and second column by a small epsilon. This is a rectangular change of operator norm equal to the absolute value of epsilon.

Compute the new right Gram matrix. Its first two coordinates have entries nine, three epsilon, three epsilon, and one plus epsilon squared. The third coordinate remains zero. The off-diagonal coupling between the top and second right singular directions is three epsilon. Their original squared spectral gap is eight. For small epsilon, the right singular direction rotates by approximately three epsilon over eight.

Compute the new left Gram matrix. Its diagonal entries are nine plus epsilon squared and one, while its off-diagonal entries are epsilon. The same original gap is eight, but the leading left singular direction now rotates by approximately epsilon over eight.

The singular values of the perturbed matrix of course belong to both Gram operators. Yet the right and left singular vectors exhibit different first-order rotations. This example proves why a theorem about right singular subspaces is not automatically a theorem about left singular subspaces with the same exact error.

## The Hermitian dilation gives another route

There is a second construction. Form a square self-adjoint block operator on output plus input space, with zero diagonal blocks, A in the upper-right block, and A adjoint in the lower-left block. This is the Hermitian dilation of A.

For each positive singular triple, the vector formed from u and v, normalized by square root of two, is an eigenvector of the dilation with eigenvalue sigma. The vector formed from u and minus v has eigenvalue minus sigma. Remaining null directions have eigenvalue zero.

Thus the dilation has spectral values equal to positive and negative singular values, together with zeros. Perturbing A by D perturbs the dilation by a self-adjoint off-diagonal block whose operator norm equals the norm of D. Davis–Kahan can then control selected dilation eigenspaces using separations among signed singular values.

The advantage is a perturbation of size D rather than one containing A times D. The complication is that a selected dilation eigenvector mixes left and right singular vectors, and the signed spectrum introduces extra separation conditions. Recovering separate left- and right-side conclusions requires an additional geometric argument.

This is related to Wedin-type bounds on the sines of principal angles. The Gram route and dilation route each expose different constants and gap assumptions; neither should be substituted for the other without checking which subspace is being selected.

## From angles to aligned frames

Suppose the selected right singular subspaces have the same dimension and are represented by orthonormal frames V and V hat. The principal sines measure subspace distance but not basis alignment. A repeated singular value permits arbitrary rotations inside its eigenspace.

We therefore allow an orthogonal d-by-d matrix O that realigns the perturbed frame. A Procrustes argument bounds the Frobenius difference between V and V hat times O in terms of the Frobenius sine distance. This gives a concrete error guarantee for computed singular-vector coordinates, up to their natural orthogonal ambiguity.

The rectangular theory gives both right and left singular-subspace sine bounds and aligned-frame estimates. Positive singular values pair right and left singular vectors through the equations A v equals sigma u and A adjoint u equals sigma v.

Keep three choices independent when applying rectangular perturbation estimates: the left or right singular subspace, the correct ambient squared-singular-value boundary gap, and the distinction between subspace distance and aligned-frame distance.

<!-- END SPOKEN LECTURE -->

---

## Display-only mathematical and Lean correspondence

For `A : ℝ^q → ℝ^p`, `D=Ahat-A` and `G=A* A`,

\[\widehat G-G=A^*D+D^*A+D^*D,\qquad
\|\widehat G-G\|\le(2\|A\|+\|D\|)\|D\|.\]

The source-facing right theorem gives, with the corrected **ambient** squared gap `Δ` and a selected block of size `d`,

\[\|\sin\Theta_{\mathrm{right}}\|_F\le
\frac{2(2\sigma_1(A)+\|D\|)\min(\sqrt d\,\|D\|,\|D\|_F)}{\Delta}.\]

The same module establishes the left and aligned-frame variants. The source's printed rank-boundary convention is explicitly refuted in `YuWangSamworth2015/Rectangular/RankBoundary.lean`; the corrected theorem uses the actual ambient zero singular-value continuation.

## Exact Lean declaration excerpts

**`SourceSingularGap`** — The source gap uses squared singular values of A and the AMBIENT input/output boundary convention. For a full-ambient block its first disjunct records a vacuous exterior-gap condition.

Source: `YuWangSamworth2015/YuWangSamworth2015/Rectangular/SourceTheorem3.lean`; exact declaration header (proof body omitted).

```lean
def SourceSingularGap {p q : ℕ} (n : ℕ)
    (A : EuclideanSpace ℝ (Fin q) →ₗ[ℝ] EuclideanSpace ℝ (Fin p))
    (r s : ℕ) (Delta : ℝ) : Prop :=
```

**`theorem3_rightSinTheta`** — This is the right Gram theorem. `IsRightSingularBlock` supplies orthonormal eigenframes of A* A and Ahat* Ahat, and the source rank condition restricts the selected indices to positive singular values.

Source: `YuWangSamworth2015/YuWangSamworth2015/Rectangular/SourceTheorem3.lean`; exact declaration header (proof body omitted).

```lean
theorem theorem3_rightSinTheta {p q d r s : ℕ}
    (A Ahat : EuclideanSpace ℝ (Fin q) →ₗ[ℝ] EuclideanSpace ℝ (Fin p))
    (hr : r ≤ s) (hrank : s < finrank ℝ (LinearMap.range A)) (hd : d = s - r + 1)
    (V Vhat : Fin d → EuclideanSpace ℝ (Fin q))
    (hV : IsRightSingularBlock A hr hd V)
    (hVhat : IsRightSingularBlock Ahat hr hd Vhat)
    (Delta : ℝ) (hDelta : 0 < Delta)
    (hgap : SourceSingularGap q A r s Delta) :
    Submodule.sinThetaFrobenius (Submodule.span ℝ (Set.range V))
        (Submodule.span ℝ (Set.range Vhat)) ≤
      2 * (2 * A.singularValues 0 + ‖(Ahat - A).toContinuousLinearMap‖) *
        min (Real.sqrt d * ‖(Ahat - A).toContinuousLinearMap‖)
          (UnitarilyInvariantSeminorm.frobenius ℝ
            (EuclideanSpace ℝ (Fin q)) (EuclideanSpace ℝ (Fin p)) (Ahat - A)) / Delta := by
```

**`theorem3_leftSinTheta`** — The left version uses eigenframes of A A* and Ahat Ahat*, with the ambient output boundary gap.

Source: `YuWangSamworth2015/YuWangSamworth2015/Rectangular/SourceTheorem3.lean`; exact declaration header (proof body omitted).

```lean
theorem theorem3_leftSinTheta {p q d r s : ℕ}
    (A Ahat : EuclideanSpace ℝ (Fin q) →ₗ[ℝ] EuclideanSpace ℝ (Fin p))
    (hr : r ≤ s) (hrank : s < finrank ℝ (LinearMap.range A)) (hd : d = s - r + 1)
    (U Uhat : Fin d → EuclideanSpace ℝ (Fin p))
    (hU : IsLeftSingularBlock A hr hd U)
    (hUhat : IsLeftSingularBlock Ahat hr hd Uhat)
    (Delta : ℝ) (hDelta : 0 < Delta)
    (hgap : SourceSingularGap p A r s Delta) :
    Submodule.sinThetaFrobenius (Submodule.span ℝ (Set.range U))
        (Submodule.span ℝ (Set.range Uhat)) ≤
      2 * (2 * A.singularValues 0 + ‖(Ahat - A).toContinuousLinearMap‖) *
        min (Real.sqrt d * ‖(Ahat - A).toContinuousLinearMap‖)
          (UnitarilyInvariantSeminorm.frobenius ℝ
            (EuclideanSpace ℝ (Fin q)) (EuclideanSpace ℝ (Fin p)) (Ahat - A)) / Delta := by
```


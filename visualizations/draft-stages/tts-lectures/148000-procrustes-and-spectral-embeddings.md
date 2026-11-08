# 148000 — Procrustes and spectral embeddings

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `018000`, `022000–023000`, `042000–044000`, `147000`. **Next:** `149000`.

<!-- BEGIN SPOKEN LECTURE -->

# Procrustes and spectral embeddings

Principal angles compare eigenspaces independently of any chosen orthonormal basis. A numerical algorithm instead returns a table of eigenvector coordinates, which may be fed to clustering, classification, or geometric embedding. Orthogonal Procrustes alignment converts a subspace-angle bound into a coordinate bound while accounting for arbitrary rotations within the selected frame.

## Two frames and one geometric object

Start with two real matrices U and V, each with d orthonormal columns in an ambient Euclidean space. They represent two d-dimensional subspaces. Orthonormality means U transpose U and V transpose V are both the d-by-d identity.

Here is a simple warning. Take a plane and choose the standard first and second coordinate vectors as its basis. Now exchange the two vectors and reverse the sign of one. The resulting frame V has the same span as U. Nevertheless, the two frames can have a substantial Frobenius difference. That difference reports the choice of coordinates, even though the two subspaces agree perfectly.

To remove this artificial discrepancy, allow an orthogonal d-by-d matrix O to act on the right of V. Multiplying V by O changes its coordinate basis while preserving its column span. Our problem is to minimize the Frobenius distance between V times O and U, over all such O. This is the orthogonal Procrustes problem.

Notice the direction of the action. We hold U, the reference frame, fixed. We rotate the coordinates of V to align with it. The resulting guarantee concerns the actual reference frame U, not a replacement basis chosen inside its span. This detail is important when downstream coordinates have an external meaning.

## Derive the minimizer from the cross-Gram matrix

Let M be U transpose times V. This d-by-d cross-Gram matrix contains every pairwise overlap between reference and candidate vectors. Its singular values are the cosines of the principal angles between the two subspaces.

Now expand the squared Frobenius distance. It equals the squared Frobenius norm of U, plus the squared Frobenius norm of V O, minus twice the trace of U transpose V O. Both frame norms squared equal d, because their columns are orthonormal. Therefore the objective equals two d minus twice the trace of M O.

So minimizing distance is equivalent to maximizing that trace over orthogonal O. Take a singular-value decomposition of M. Write it as L times a diagonal matrix of nonnegative singular values times R transpose. Choose O to be R times L transpose. Then M O is L times that nonnegative diagonal matrix times L transpose, and its trace equals the sum of the singular values.

Why is that the largest possible trace? For any orthogonal O, the trace of M O becomes the trace of the singular-value diagonal times an orthogonal matrix. Each diagonal entry of an orthogonal matrix is at most one. Every singular value is nonnegative. Hence the trace cannot exceed the sum of the singular values, and our choice attains that upper bound.

The minimizing squared error is thus twice the sum of one minus each singular value of M. Since the singular values are principal cosines, we have proved the exact identity: the optimal squared frame error equals twice the sum of one minus cosine theta, over the principal angles.

If some singular values are zero, the minimizing orthogonal matrix may not be unique. The singular-value decomposition can still furnish one. If all principal angles vanish, an alignment gives zero error even when the raw frames look very different.

## Compare the exact error with principal sines

Davis–Kahan estimates usually control principal sines, rather than one minus principal cosines. We therefore need a comparison.

For any angle between zero and ninety degrees, its cosine c lies between zero and one. Twice one minus c equals two times one minus c squared, divided by one plus c. That fraction is between one and two times one minus c squared. In ordinary words, twice one minus cosine lies between sine squared and twice sine squared.

Sum these inequalities over all principal angles. The optimal aligned squared Frobenius error lies between the sum of squared principal sines and twice that sum. Taking square roots, the optimal frame error is no greater than square root of two times the Frobenius norm of the principal-sine list.

The square-root-of-two factor is global. We have not assumed the principal angles are small. For very small angles, the two errors are approximately equal. For a right angle, the squared frame error is two while the squared sine is one, so the factor is attained for a one-dimensional example.

Let's test an intermediate case. Let U consist of the first two coordinate vectors in three-dimensional space. Let V consist of the first vector and a second vector tilted sixty degrees toward the third coordinate axis. The two principal angles are zero and sixty degrees. Their cosine list is one and one half. The optimal squared frame error is twice one minus one half, which is one. The squared sine error is three quarters. Therefore the optimal frame error is one, while square root of two times the sine error is the square root of one and one half. The derived bound holds, with room to spare.

## The explicit statistical theorem

Now combine this geometry with the population-gap theorem under the population spectral-gap assumptions. There, the population and sample symmetric matrices have ordered eigenvector frames U and V for the same consecutive block of d indices. The population spectral boundary gap is Delta, strictly positive. Call the sample minus population matrix E.

The population-gap theorem bounds the Frobenius sine distance by two over Delta times the smaller of square root of d times the operator norm of E, and the Frobenius norm of E.

Our Procrustes inequality multiplies that upper bound by square root of two. Consequently there exists an orthogonal matrix O for which the Frobenius norm of V O minus U is at most two square root of two over Delta times that same minimum of two error measures.

This conclusion keeps the supplied population frame fixed. It also does not require a separate hypothesis asserting a sample spectral gap. The bound may be weak when the estimation error is large compared with Delta, but it remains a deterministic consequence of the stated assumptions.

The alignment operator may be expressed as a coordinate-space isometry, or in real orthonormal coordinates as an orthogonal matrix. Equivalently, one can estimate the difference between the overlap map and its closest coordinate isometry. These are representations of the same alignment geometry.

## Gram rigidity and why the cross-Gram matters

Recall that U transpose U and V transpose V both equal the identity. So their individual Gram matrices are identical. Does that prove the subspaces coincide? Of course not. Any orthonormal frame has identity Gram matrix, regardless of where its span lies in the ambient space.

More generally, suppose two finite families of vectors have the same Gram matrix. Their linear combinations have the same squared lengths because a squared length is a quadratic form in the Gram matrix. Therefore sending one family's linear combinations to the corresponding combinations of the other family is a well-defined linear isometry between their spans. In finite-dimensional ambient spaces of equal dimension, that isometry can be extended to an orthogonal map after matching orthogonal-complement bases.

That is Gram rigidity: the internal geometry agrees up to an ambient isometry. It does not say that the two families occupy the same ambient position under the identity map. Their cross-Gram matrix supplies the missing positional information. Its singular values encode principal angles, and its polar factor selects the Procrustes alignment.

This distinction explains why looking only at a matrix of within-embedding distances cannot automatically establish closeness in a fixed coordinate system. An embedding reconstructed from those distances is determined only up to a suitable isometry, and sometimes translation too if the data consist solely of pairwise distances.

## When spectral embeddings carry weights

A spectral embedding may consist of eigenvectors alone, but often each eigenvector is scaled by a function of its eigenvalue. Classical multidimensional scaling, for example, uses square roots of positive eigenvalues as coordinate weights. Spectral clustering may apply other normalizations.

Suppose for now that a common coordinate weight matrix W is applied after alignment. The difference between V O W and U W equals V O minus U, multiplied on the right by W. Its Frobenius norm is at most the Frobenius norm of V O minus U times the operator norm of W. We therefore obtain a weighted coordinate-error bound immediately from Procrustes alignment.

Now suppose the reference and sample weights differ. Write the aligned sample embedding as V O times W hat, and the reference embedding as U times W. Add and subtract V O W. The error has two terms: one caused by the frame mismatch, and one caused by the weights changing. The Frobenius norm is at most the aligned frame error times the operator norm of W, plus the Frobenius norm of W hat minus W. This is a valid bound once both weight matrices are expressed in the same aligned coordinate convention.

There is a subtlety. In a real eigendecomposition, the sample eigenvalue weights are usually diagonal in the original sample eigenbasis. If we rotate that basis by a general Procrustes matrix, the weight operator must be conjugated into the rotated coordinates. It need not remain diagonal. We cannot simply rotate the eigenvectors, leave their weights unchanged, and claim that we have rotated the original embedding.

A weighted spectral embedding requires three estimates: the underlying subspace deviation, the optimal basis alignment, and the change in spectral weights. Combining them requires compatible coordinates.

## What you should be able to prove

You should now be able to expand a frame difference into a trace objective, solve that objective using the singular-value decomposition, and express the exact minimum using principal cosines. You should also be able to derive the square-root-of-two comparison with principal sines, and combine it with a population-gap inequality without introducing a sample-gap hypothesis.

Finally, you should be able to explain why identical Gram matrices describe identical internal geometry but do not certify identical ambient subspaces, and why weighted embeddings need more care than unweighted frames.

<!-- END SPOKEN LECTURE -->

---

## Display-only mathematics and Lean correspondence

For orthonormal frames \(U,V:\mathbb K^d\to H\) with cross-Gram matrix \(M=U^*V\) and singular values \(\sigma_i(M)=\cos\theta_i\),

\[
\min_{O^*O=I}\|VO-U\|_F^2=2d-2\sum_{i=1}^d\sigma_i(M)
=2\sum_{i=1}^d(1-\cos\theta_i).
\]

Because \(0\le c\le1\) implies \(1-c^2\le2(1-c)\le2(1-c^2)\),

\[
\|\sin\Theta\|_F\le\min_O\|VO-U\|_F
\le\sqrt2\,\|\sin\Theta\|_F.
\]

The lower and upper comparisons are exact; no small-angle hypothesis is required.

For the source's population gap \(\Delta>0\), eigenframe block size \(d\), and perturbation \(E=B-A\), the real-frame endpoint gives an explicit \(O\in O(d)\) satisfying

\[
\|\widehat VO-V\|_F\le\frac{2\sqrt2}{\Delta}
\min\{\sqrt d\,\|E\|_{\mathrm{op}},\|E\|_F\}.
\]

**Weighted embeddings:** If weights are written in common aligned coordinates, \(\|\widehat VO\widehat W-UW\|_F\le\|\widehat VO-U\|_F\|W\|_{\mathrm{op}}+\|\widehat W-W\|_F\). If the sample weights were originally diagonal in the unrotated eigenframe, convert them to the aligned basis before applying this formula.

## Exact Lean declaration excerpts

**`frameComp`** — `YuWangSamworth2015/YuWangSamworth2015/Core/Procrustes.lean` (exact declaration header; proof body omitted):

```lean
noncomputable def frameComp {v : Fin d → E} (hv : Orthonormal 𝕜 v)
    (O : EuclideanSpace 𝕜 (Fin d) ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin d)) : Fin d → E :=
```

**`sum_re_inner_u_aligned`** — `ForTauCeti/Analysis/InnerProductSpace/AlignedBasis.lean` (exact declaration header; proof body omitted):

```lean
theorem sum_re_inner_u_aligned {u v : Fin d → E} (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) :
    ∑ j, RCLike.re ⟪u j, hv.synthesisMapIsometry ((choosePolarUnitary (overlapOperator 𝕜 u v)).symm
          (EuclideanSpace.single j 1))⟫_𝕜
      = ∑ k : Fin d, (overlapOperator 𝕜 u v).singularValues (k : ℕ) := by
```

**`exists_unitary_sum_sq_norm_frameComp_sub_le`** — `YuWangSamworth2015/YuWangSamworth2015/Core/Procrustes.lean` (exact declaration header; proof body omitted):

```lean
theorem exists_unitary_sum_sq_norm_frameComp_sub_le {u v : Fin d → E}
    (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) :
    ∃ O : EuclideanSpace 𝕜 (Fin d) ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin d),
      (∀ x y, ⟪O x, O y⟫_𝕜 = ⟪x, y⟫_𝕜) ∧
        ∑ i, ‖frameComp hv O i - u i‖ ^ 2 ≤
          2 * Submodule.sinThetaFrobenius (Submodule.span 𝕜 (Set.range u))
            (Submodule.span 𝕜 (Set.range v)) ^ 2 := by
```

**`yuWangSamworth_alignmentMap_sub_overlapOp_apply_le`** — `YuWangSamworth2015/YuWangSamworth2015/Core/Procrustes.lean` (exact declaration header; proof body omitted):

```lean
theorem yuWangSamworth_alignmentMap_sub_overlapOp_apply_le
    {A B : E →ₗ[𝕜] E} {hA : A.IsSymmetric} {hB : B.IsSymmetric}
    {n : ℕ} {hn : finrank 𝕜 E = n} {e : Fin d ↪ Fin n} {u v : Fin d → E}
    (hu : IsOrderedEigenframe hA hn e u) (hv : IsOrderedEigenframe hB hn e v)
    {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : ∀ (i : Fin d) (k : Fin n), k ∉ Set.range (⇑e) →
      Δ ≤ |hA.eigenvalues hn (e i) - hA.eigenvalues hn k|) :
    ∃ W : EuclideanSpace 𝕜 (Fin d) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin d),
      (∀ x y, ⟪W x, W y⟫_𝕜 = ⟪x, y⟫_𝕜) ∧
      ∀ x, ‖(W - overlapOperator 𝕜 u v) x‖ ≤
        (2 * Real.sqrt 2 *
          min (Real.sqrt d * ‖(B - A).toContinuousLinearMap‖)
            (UnitarilyInvariantSeminorm.frobenius (𝕜 := 𝕜) (E := E) (F := E) (B - A)) / Δ) *
```

**`yuWangSamworth_alignedFrame_real_le`** — `YuWangSamworth2015/YuWangSamworth2015/Core/Procrustes.lean` (exact declaration header; proof body omitted):

```lean
theorem yuWangSamworth_alignedFrame_real_le
    {A B : F →ₗ[ℝ] F} {hA : A.IsSymmetric} {hB : B.IsSymmetric}
    {n : ℕ} {hn : finrank ℝ F = n} {e : Fin d ↪ Fin n} {u v : Fin d → F}
    (hu : IsOrderedEigenframe hA hn e u) (hv : IsOrderedEigenframe hB hn e v)
    {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : ∀ (i : Fin d) (k : Fin n), k ∉ Set.range (⇑e) →
      Δ ≤ |hA.eigenvalues hn (e i) - hA.eigenvalues hn k|) :
    ∃ O : Matrix (Fin d) (Fin d) ℝ, O ∈ Matrix.orthogonalGroup (Fin d) ℝ ∧
      Real.sqrt (∑ i, ‖(∑ j, O j i • v j) - u i‖ ^ 2) ≤
        2 * Real.sqrt 2 *
          min (Real.sqrt d * ‖(B - A).toContinuousLinearMap‖)
            (UnitarilyInvariantSeminorm.frobenius (𝕜 := ℝ) (E := F) (F := F) (B - A)) / Δ := by
```


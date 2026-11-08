# 053000 — Low-rank approximation and Eckart–Young

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `036000` singular-value decomposition; `052000` singular-value min–max principles; `020000` orthogonal embeddings; `034000` positive square roots. **Next:** Ky Fan sums and inequalities.

<!-- BEGIN SPOKEN LECTURE -->

# The best map when we keep only a few directions

Suppose A is a linear map represented by a large matrix. We would like to replace it by something simpler: a map whose outputs all lie in a space of dimension at most k.

That is what rank at most k means. It is a constraint on how many independent output directions the approximation can use. We now want to choose the replacement that minimizes error.

There are at least two reasonable ways to measure error. Operator norm asks for the worst error over all unit inputs. A second measurement adds up the squared errors over a complete orthonormal input basis. The latter is the squared Frobenius norm, or Hilbert–Schmidt norm in finite dimensions.

Eckart–Young identifies an optimal rank-k approximation for both measurements. We will prove it from the singular-value decomposition and then examine the distinctions between the two error formulas.

## Rebuild the map one singular direction at a time

Let A map a finite-dimensional inner-product space E into another space F. Let its positive singular values be sigma one, sigma two, and so on, in decreasing order. A has an orthonormal family of right singular vectors, and their images, after dividing by the corresponding positive singular values, form an orthonormal family of left singular vectors.

For an arbitrary input x, A x is the sum of its contributions along these singular directions. The first contribution is sigma one times the coefficient of x along the first right singular vector, multiplied by the first left singular vector. The second contribution is the analogous term involving sigma two. Continue until all positive singular values are used.

Because the left singular vectors are orthogonal, these terms behave independently when we measure their lengths.

Now define A sub k by keeping only the first k contributions and deleting the rest. If k is zero, the result is the zero map. If k is at least the rank of A, the result is A itself.

The image of A sub k lies in the span of the first k left singular vectors, so its rank is at most k. It is an admissible approximation.

The error A minus A sub k consists exactly of the discarded singular terms. The largest output it can produce from a unit input has length sigma k plus one, provided that singular value exists. When all nonzero terms have already been kept, the error is zero.

That proves one direction of optimality: we have constructed a rank-k approximation with operator-norm error equal to the next singular value.

## Prove that nobody can do better

Take any other map B of rank at most k. We cannot assume that B preserves the singular directions. It may choose any output subspace and may mix all the input coordinates.

But its kernel has codimension at most k. The span of the first k plus one right singular vectors has dimension k plus one. Therefore that leading span and the kernel of B share a nonzero vector.

Choose a unit vector x in their intersection. Since B x is zero, the error on x is A x. And since x is made entirely from the first k plus one right singular directions, the length of A x is at least sigma k plus one.

Thus every rank-k B has operator-norm error at least sigma k plus one. Our truncated singular-value expansion achieves that bound.

We have now proved the operator-norm Eckart–Young theorem. It does not require B to be diagonal, self-adjoint, or aligned with A. A dimension-intersection argument rules out every possible competitor at once.

Pay attention to the indexing. A rank-k approximation has error controlled by singular value k plus one, not singular value k. If k equals the dimension of the source, all singular directions can be kept and the optimal error is zero. We may express this uniformly by appending zeros after the finite singular-value list.

## Measure the total squared error

The operator norm looks at the worst unit input. The Frobenius norm instead measures the sum of squared output lengths on an orthonormal basis of the source.

Choose any orthonormal basis and apply the error map to each basis vector. Square each output length and add. A calculation with inner products shows that the sum does not depend on which orthonormal basis we chose. In matrix coordinates it is simply the sum of the squares of the absolute values of all entries.

For the truncated singular-value expansion, use the right singular basis. Each retained direction has zero error. Each discarded direction with singular value sigma j has error length sigma j. Therefore the squared Frobenius error is the sum of sigma j squared over all discarded indices.

Taking a square root gives the Frobenius error.

We have again found a candidate. Now we must prove that no other rank-k map has a smaller total squared error. The kernel argument from operator norm is not enough: one badly approximated direction gives a lower bound on the worst error, but it does not account for the sum of many errors.

## Prove the squared-error lower bound

Let B be any rank-k competitor. Call R its range, and let P be the orthogonal projection onto R. Every output of B lies in R.

For any input x, decompose the error A x minus B x into two perpendicular parts. One part is the component of A x outside R. The other part lies inside R and equals P A x minus B x.

The Pythagorean theorem says the squared error is the sum of the squared lengths of those two parts. It is therefore at least the squared length of the component of A x outside R.

Apply this to every right singular vector and add. We obtain a lower bound equal to the sum, over j, of sigma j squared times one minus the squared length of P applied to the corresponding left singular vector.

Each squared projection length lies between zero and one. The sum of these lengths over the left singular family is at most the dimension of R, which is at most k. One way to see this is to extend the singular vectors to an orthonormal basis of F and calculate the trace of P. That trace is the dimension of R.

We therefore have a simple allocation problem. There is a capacity of at most k units. How should we distribute it among numbers between zero and one to capture as much as possible of the ordered values sigma j squared?

The answer is to allocate one unit to each of the first k values. To prove this, suppose a smaller singular value has positive allocation while a larger one is not fully allocated. Move a little allocation from the smaller to the larger. The weighted sum cannot decrease. Repeating this exchange leaves the first k positions filled, with all later positions empty.

Hence the squared error of B is at least the sum of the squares of the singular values after the first k. Truncation attains equality. This proves Frobenius-norm Eckart–Young as well.

## Work an example in both norms

Take the diagonal three-by-three map with diagonal entries five, two, and one. Its singular values are five, two, and one.

If we keep only the largest singular direction, our approximation has diagonal entries five, zero, and zero. The error has diagonal entries zero, two, and one.

The operator-norm error is two, because the largest error on a unit input occurs along the second coordinate.

The squared Frobenius error is four plus one, which is five. Its Frobenius norm is the square root of five. These answers differ because the two norms ask different questions.

If we keep the two largest singular directions, the error consists only of the third diagonal entry. Both errors are one.

If we keep all three, both errors are zero. And if the smallest singular value had been zero from the beginning, keeping two directions would already reproduce the entire map.

## What happens when singular values tie?

The truncated singular-value expansion is an optimal solution, but an optimal solution need not be unique.

Consider a map whose two largest singular values are both three. Suppose we are allowed to keep only one direction. The map treats that two-dimensional leading singular subspace symmetrically. We can choose different unit directions within it and obtain different rank-one truncations with the same optimal errors.

When there is a strict gap between the k-th and k-plus-one-st singular values, the leading singular subspaces are more tightly determined. But we should distinguish the uniqueness of a selected subspace from the uniqueness of an arbitrary optimizer, especially in the operator norm. We are not proving a general uniqueness theorem here.

## What to reconstruct

First, write out the truncated expansion and show that its operator-norm error is the largest discarded singular value.

Second, repeat the kernel-intersection argument against an arbitrary rank-k map.

Third, prove the squared-error result using the projection onto the range of the competitor. Account for the fact that its rank may be smaller than k. Then derive the weighted-allocation bound instead of quoting it.

The next lecture changes the objective. Rather than measuring only the largest singular value or the sum of all squared ones, we will measure the sum of the first several. That leads to Ky Fan norms and the inequalities needed for perturbation estimates.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

For \(A:E\to F\), write the SVD \(A=\sum_{j=1}^r\sigma_j u_jv_j^*\), with \(\sigma_1\ge\cdots\ge\sigma_r>0\), extended by zeros. The **truncated SVD** is \(A_k=\sum_{j\le k}\sigma_j u_jv_j^*\). For \(0\le k\le\min(\dim E,\dim F)\),
\[
\min_{\operatorname{rank} B\le k}\|A-B\|_{\mathrm{op}}=\sigma_{k+1}(A),
\qquad
\min_{\operatorname{rank} B\le k}\|A-B\|_{F}
=\Bigl(\sum_{j>k}\sigma_j(A)^2\Bigr)^{1/2}.
\]
The first minimum follows from the SVD upper bound and \(\ker B\cap\operatorname{span}(v_1,\ldots,v_{k+1})\ne\{0\}\). For the second, project onto \(\operatorname{ran}B\), use orthogonal Pythagoras, and maximize \(\sum_j\sigma_j^2\|Pu_j\|^2\) subject to \(0\le\|Pu_j\|^2\le1\) and \(\sum_j\|Pu_j\|^2\le k\). The latter is at most \(\sum_{j\le k}\sigma_j^2\).

**Lean bridge (verbatim excerpts).** `ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/MinMax.lean` gives the spectral-band approximation upper bound:

```lean
theorem approximationNumber_le_of_spectral_band [CompleteSpace F₁]
    {T : E₁ →L[𝕜] F₁} {P : E₁ →L[𝕜] E₁} {r : ℕ} {δ : ℝ}
    (hδ : 0 ≤ δ) (hidem : IsIdempotentElem P) (hsa : IsSelfAdjoint P)
    (hrank : P.rank ≤ (r : Cardinal))
    (hband : ∀ x : E₁, ‖T (x - P x)‖ ≤ δ * ‖x - P x‖) :
    (T.singularValue r : ℝ) ≤ δ := by
```

Here `P` is the rank-bounded orthogonal projection onto retained input directions; `T ∘L P` is the low-rank competitor, and `δ` bounds the norm of the discarded tail. Lean's `singularValue r` is **zero indexed**: choosing rank at most \(k\) bounds the mathematical \(\sigma_{k+1}\). This declaration establishes the **upper** comparison from a proposed spectral cutoff, not by itself the full Eckart–Young equality. The matching lower bound comes from the min–max/approximation-number theory imported from `TauCeti.Analysis.OperatorIdeal.ApproximationNumber.EckartYoung` and the preceding lecture's dimension argument.

`DavisKahan/OperatorIdeal/ApproximationNumbers/FiniteSourceSingularSystem.lean` also makes the truncated singular-vector construction explicit:

```lean
theorem apply_finiteSourceRightSingularBasis_eq_smul_leftSingularVector
    (A : E →L[ℂ] F) (i : Fin (finrank ℂ E)) :
    A (finiteSourceRightSingularBasis A i) =
      ((finiteSourceSingularValue A i : ℝ) : ℂ) •
        finiteSourceLeftSingularVector A i := by
```

The second theorem allows finite source and general complete Hilbert codomain. The Frobenius optimality argument above is the finite-dimensional mathematical proof given in the spoken lecture; neither displayed Lean declaration is presented as a complete formalization of that specific equality.

**Reconstruction exercise:** derive both minima for the diagonal map with singular values \(5,2,1\), then explain why a double singular value at the cutoff admits different optimal truncated-SVD choices.

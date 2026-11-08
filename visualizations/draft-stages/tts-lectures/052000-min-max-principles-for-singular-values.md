# 052000 — Min–max principles for singular values

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `023000` rectangular Gram operators; `026000` finite spectral theorem; `028000` Courant–Fischer; `035000` operator modulus; `036000` singular-value decomposition. **Next:** low-rank approximation and Eckart–Young.

<!-- BEGIN SPOKEN LECTURE -->

# How large must a linear map remain?

The eigenvalue min–max theorem answers a question about a self-adjoint operator: if we are allowed to choose a subspace, how large or small can its quadratic form be on unit vectors in that subspace?

We now ask a related question for any linear map. It need not be square. It need not be self-adjoint. We might map three-dimensional vectors into a space of five dimensions, or the other way around. There may be no eigenvalues that describe the map at all.

But one measurement always makes sense. Give the map a unit input, and measure the length of its output. Which input directions produce large outputs? How many independent directions must have large outputs? Singular values answer these questions, and min–max principles make their answers independent of a chosen matrix or basis.

## Recover the geometry from the singular-value decomposition

Let A be a linear map from a finite-dimensional inner-product space E into another such space F. Let the dimension of E be n. The singular-value decomposition gives an orthonormal basis of E consisting of right singular vectors. Order their singular values from largest to smallest, including zeros if necessary.

Call these singular values sigma one through sigma n. For a right singular vector v sub j, the length of A applied to that vector is sigma j. Images of right singular vectors associated to positive singular values point along mutually perpendicular left singular vectors. A right singular vector with zero singular value lies in the kernel.

Take an arbitrary input x. Expand it in the right singular basis. The squared length of A x is the sum, over j, of sigma j squared times the squared magnitude of the corresponding coefficient.

That formula is the key. It tells us that a unit vector built only from the first j right singular directions cannot be shortened below sigma j. And a unit vector built from directions j through n cannot be stretched beyond sigma j.

We will make those two observations into two optimization theorems.

## Remove the strongest directions

Choose an integer j between one and n. Imagine that an adversary is allowed to discard a subspace of dimension j minus one. We are then allowed to choose any remaining unit direction orthogonal to that discarded subspace. We choose the one on which A has the largest output length.

The adversary wants to make that largest remaining length as small as possible.

The minimum possible answer is sigma j.

First prove that the adversary can achieve no more than sigma j. Discard the span of the first j minus one right singular vectors. Every unit vector in its orthogonal complement is a combination of right singular directions j through n. None has an output longer than sigma j. Therefore the largest remaining output length is at most sigma j.

Now prove that the adversary cannot do better. Take any discarded subspace of dimension j minus one, even one that is not aligned with the singular vectors. Consider the j-dimensional span of the first j right singular vectors. Because that span has one dimension more than the discarded space, there must be a nonzero vector in the leading span that is orthogonal to every discarded direction.

Normalize it to length one. All of its singular coordinates come from the first j positions, so its output length is at least sigma j. It survives the adversary's choice. Thus every discarded subspace leaves behind an input stretched by at least sigma j.

The upper and lower bounds agree. This proves the first min–max formula.

Notice what did the real work: the dimension count that forces an intersection, together with the singular-value expansion of output length. This is the same geometric argument we used for Courant–Fischer, applied to the positive modulus of A.

## Keep a subspace instead

There is a complementary game. We are now allowed to choose a subspace of dimension j, and an adversary chooses the unit vector in that subspace on which A has the smallest output. We want that worst-case output length to be as large as possible.

Again the answer is sigma j.

For the lower bound, select the span of the first j right singular vectors. Every unit vector there has output length at least sigma j, so our best possible value is at least sigma j.

For the upper bound, consider any j-dimensional subspace the chooser proposes. Look at the span of the right singular vectors numbered j through n. Its dimension is n minus j plus one. Those dimensions add up to n plus one. The two subspaces must intersect in a nonzero vector. Normalize that vector. It belongs to the proposed j-dimensional subspace, but it uses only singular directions j through n, so its output length is at most sigma j.

Therefore no j-dimensional subspace can guarantee more than sigma j.

These are two different quantifier orders: discard j minus one directions and inspect the largest survivor, or keep j directions and inspect the smallest survivor. Both characterize the same singular value.

## A rectangular example

Let A take a pair of real numbers, x and y, to the three-dimensional vector whose coordinates are five x, two y, and zero.

The source has dimension two. The right singular vectors are the ordinary horizontal and vertical unit vectors. Their singular values are five and two. The unused third output coordinate does not create a third right singular direction.

For the first singular value, no directions are discarded. The largest output of a unit input has length five.

For the second, discard one input direction. If we discard the horizontal direction, the surviving vertical unit vector has output length two. If instead we discard a tilted direction, the perpendicular survivor usually has components in both coordinates, and its output has length greater than two. Thus the best one-dimensional discard leaves a maximum of two.

In the complementary game, keep one input line and maximize its minimum output length. The horizontal line guarantees five. Keep the entire two-dimensional source, and the smallest output length is two.

Now replace the multiplier two by zero. The second singular value becomes zero. A whole input direction is destroyed. The theorem still works, without any assumption that A is invertible.

## Connection to the modulus

Recall that the modulus of A is the positive square root of A adjoint composed with A. It acts on the source space, and it has exactly the singular values of A as its eigenvalues.

More importantly, the length of A x equals the length of the modulus applied to x. Consequently the variational games we just played are literally the Courant–Fischer games for this positive operator, expressed through lengths instead of Rayleigh quotients.

For a unit vector, the square of the output length is the quadratic form of A adjoint A. We could first apply Courant–Fischer to the squared singular values, then take nonnegative square roots. That gives another proof of both formulas.

The advantage of our direct proof is that it remains visibly geometric. It shows where the subspaces come from and why rectangularity causes no problem.

## A first approximation consequence

Suppose someone offers a map B whose rank is at most j minus one, claiming that B approximates A very well. Because B has rank at most j minus one, its kernel has codimension at most j minus one.

Our dimension argument shows that the kernel of B meets the span of the first j right singular vectors in a nonzero direction. Choose a unit vector x in that intersection. Then B x is zero, while A x has length at least sigma j.

So A minus B has operator norm at least sigma j. Every approximation that uses fewer than j independent output directions must make an error of at least sigma j on some unit input.

This is already half of the Eckart–Young theorem.

## What to reconstruct

Try proving the two singular-value games without naming any spectral theorem. Use only the orthonormal singular bases, the formula for the squared output length, and the dimension-intersection inequality.

Then take a three-dimensional diagonal map with singular values six, three, and one. Explain why discarding two input directions can reduce the largest surviving output length to one, but cannot reduce it below one.

Finally, prove the kernel argument for a rank-one approximation. Ask yourself precisely where the dimension of the source appears, and why the dimension of the target does not enter the conclusion.


<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

Let \(A:E\to F\) between finite-dimensional real or complex inner-product spaces, \(n=\dim E\), and write \(\sigma_1\ge\cdots\ge\sigma_n\ge0\). For \(1\le j\le n\),
\[
\sigma_j(A)=\min_{\dim L=j-1}\max_{\substack{x\in L^\perp\\\|x\|=1}}\|Ax\|
=\max_{\dim W=j}\min_{\substack{x\in W\\\|x\|=1}}\|Ax\|.
\]
Proof: \(\|Ax\|^2=\sum_i\sigma_i^2|\langle v_i,x\rangle|^2\). For the first formula, choose \(L=\operatorname{span}(v_1,\ldots,v_{j-1})\); for every other \(L\), \(L^\perp\) intersects \(\operatorname{span}(v_1,\ldots,v_j)\). For the second, choose the leading \(j\)-span; every alternative \(j\)-span intersects \(\operatorname{span}(v_j,\ldots,v_n)\). The unit spheres are nonempty because \(j\le n\). The operator modulus satisfies \(\|Ax\|=\||A|x\|\), so these are equivalent to Courant–Fischer for \(|A|\).

**Lean bridge (verbatim excerpts).** `DavisKahan/OperatorIdeal/ApproximationNumbers/FiniteSourceSingularSystem.lean` identifies approximation-number singular values with the finite-source SVD, even when the target Hilbert space is not finite dimensional:

```lean
theorem approximationSingularValue_eq_finiteSourceSingularValue
    [CompleteSpace F]
    (A : E →L[ℂ] F) (i : Fin (finrank ℂ E)) :
    (A.singularValue i : ℝ) = finiteSourceSingularValue A i := by
```

Here the source type has a `FiniteDimensional ℂ E` instance, and the `Fin` index starts at zero: index \(j-1\) corresponds to spoken \(\sigma_j\). `F` is an arbitrary complete complex Hilbert space. The formal API calls these approximation-number singular values.

`ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/MinMax.lean` supplies a projection-tail identity:

```lean
theorem norm_comp_starProjection_orthogonal_eq_sSup_unitClosedBall
    (T : E₁ →L[𝕜] F₁) (V : Submodule 𝕜 E₁) [Vᗮ.HasOrthogonalProjection] :
    ‖T ∘L Vᗮ.starProjection‖ =
      sSup ((fun x : Vᗮ => ‖T (x : E₁)‖) '' Metric.closedBall 0 1) := by
```

The supremum uses the **closed unit ball**, not the unit sphere, so it handles the zero orthogonal complement correctly. The canonical coercive-subspace lower bound and orthogonal-tail min–max results are imported from `TauCeti.Analysis.OperatorIdeal.ApproximationNumber.MinMax`. The local source header records that the retired min–max work originated in DKPS and was moved upstream; the present import location does not determine its origin.

**Reconstruction exercise:** derive the rank bound \(\|A-B\|\ge\sigma_j(A)\) for every \(\operatorname{rank}B<j\) by intersecting \(\ker B\) with the leading \(j\) singular directions.

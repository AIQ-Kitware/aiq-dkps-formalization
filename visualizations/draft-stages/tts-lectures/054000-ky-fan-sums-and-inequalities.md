# 054000 — Ky Fan sums and inequalities

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `036000` SVD; `052000` singular-value min–max; `053000` Eckart–Young; `009000` orthogonality and inner products; `014000` unitary maps. **Next:** majorization and weak majorization.

<!-- BEGIN SPOKEN LECTURE -->

# What can the first several singular values tell us?

The largest singular value of a linear map is its operator norm: the greatest length its output can have on a unit input. But that single number ignores how much the map stretches its second, third, and other independent directions.

The Frobenius norm instead adds the squares of all singular values and takes a square root. It measures their combined squared stretching, while the operator norm only measures the maximum.

There is another natural family of measurements. Choose a positive integer k, and add the first k singular values without squaring them. These are the Ky Fan sums.

They let us ask how much of a map's action can be concentrated into k independent input and output directions. More importantly, each sum obeys a triangle inequality. That will eventually let us compare entire lists of singular values, even when no individual singular-value comparison is available.

Our goal is to derive these statements rather than take them as definitions with unexplained properties.

## Define the partial sums carefully

Let A be a linear map between finite-dimensional inner-product spaces. Write its singular values in decreasing order, starting with the largest. If necessary, append zeros beyond the rank.

For k equal to one, the Ky Fan sum is the largest singular value. For k equal to two, it is the sum of the two largest. Continue until k reaches the smaller of the input and output dimensions. After that point, adding more zeros changes nothing.

For a diagonal map with singular values five, two, and one, the first Ky Fan sum is five, the second is seven, and the third is eight.

Compare this with the Frobenius norm, which is the square root of twenty-five plus four plus one. The Ky Fan sums add lengths. The Frobenius norm adds squared lengths before taking a square root. We should not confuse their interpretations or their proofs.

The zero-th Ky Fan sum is zero by convention. For positive k, the sum is nonnegative, and it vanishes only when the map is zero.

Now we need a description that does not begin by computing the singular values.

## An orthonormal-frame experiment

Assume k is no larger than either the source dimension or the target dimension. Choose k mutually orthonormal input vectors. Independently, choose k mutually orthonormal output vectors.

Apply A to the first input vector and take its inner product with the first output vector. Repeat for every corresponding pair, take the real parts, and add the results.

What is the largest value this sum can have, as we vary both orthonormal families?

The answer is the sum of the first k singular values.

First prove the lower bound. Choose the input vectors to be the first k right singular vectors and the output vectors to be the corresponding left singular vectors. For positive singular values, each inner product equals that singular value. If we encounter zero singular values, complete the chosen vectors to orthonormal families; their contributions remain zero.

This experiment achieves the Ky Fan sum.

To prove the upper bound, we need to show that no other pairing does better. We will use an elementary weighted-sum argument.

## Why arbitrary pairings cannot exceed the top k sum

Expand A in its singular-value decomposition. Each term is a singular value times a rank-one map from a right singular vector to a left singular vector.

When we insert this expansion into our sum of k inner products, the contribution from singular direction j is sigma j multiplied by a sum of products of two sets of coefficients: how strongly our chosen input vectors overlap the j-th right singular vector, and how strongly the chosen output vectors overlap its left singular vector.

By Cauchy–Schwarz, the magnitude of that coefficient sum is at most the product of two square roots. Each square root measures total squared overlap with one singular vector across a chosen orthonormal k-frame.

Each overlap is at most one, by Bessel's inequality. And if we add the squared overlaps over all singular vectors, each of the input and output totals is at most k. Applying Cauchy–Schwarz once more gives nonnegative weights, at most one each, whose total is at most k.

So we have reduced the entire problem to this: maximize a weighted sum of decreasing nonnegative numbers sigma one, sigma two, and so on. Each weight lies between zero and one, and the weights together have total at most k.

The largest possible sum is obtained by putting unit weight on the first k numbers. To see why, move any weight assigned to a smaller number toward an earlier, larger number that has not yet received full weight. The sum cannot decrease. Continue until the first k positions are filled or all the weight has been used.

Therefore every orthonormal pairing has real sum at most the first k singular values added together. We already exhibited a pairing that attains equality. This proves the variational principle.

It is a rectangular theorem: the input and output families live in different spaces. We never needed to identify those spaces or assume that A has eigenvectors.

## Derive the triangle inequality

Let A and B have the same source and target. Take any two orthonormal k-frames, one in the source and one in the target.

The pairing sum for A plus B splits into the pairing sum for A and the pairing sum for B. By the variational theorem, the first is at most the k-th Ky Fan sum of A, and the second is at most the corresponding sum for B.

This bound holds for every choice of frames. Maximize the left side over the frames. We obtain the triangle inequality: the k-th Ky Fan sum of A plus B is at most the sum of the k-th Ky Fan sums of A and B.

The proof has an important shape. We used the same test frames for A and B, and only then maximized. We did not assume the maximizing singular vectors of A and B coincide.

We also have homogeneity: multiplying the map by a scalar multiplies every singular value by the scalar's absolute value. And we have invariance under unitary changes of source and target coordinates, since those changes preserve the singular values and the available orthonormal frames.

Together, these properties make the positive-index Ky Fan sums genuine norms in finite dimensions.

## Why adding singular values one at a time is wrong

Consider two diagonal two-by-two matrices. Let A have diagonal entries three and zero. Let B have diagonal entries zero and three.

Each matrix has singular values three and zero. Their sum is three times the identity, with singular values three and three.

Look at the second singular value. For A plus B it is three, while the second singular value of A plus the second singular value of B is zero. So a coordinate-by-coordinate triangle inequality for singular values is false.

But look at the Ky Fan sums. The first sum of A plus B is three, which is at most three plus three. The second is six, exactly equal to the second Ky Fan sum of A plus that of B.

The sums obey the inequality even though the individual entries do not. This distinction is one reason Ky Fan quantities are useful for operator perturbation theory.

## Pinching discards off-diagonal blocks

There is another consequence worth proving now.

Suppose A acts on one inner-product space, and P is an orthogonal projection. Relative to the decomposition into the range of P and its perpendicular complement, we can write A as a two-by-two block operator.

Pinching A means keeping its two diagonal blocks and deleting both off-diagonal blocks. In symbols expressed verbally, the result is P A P plus the complementary projection, followed by A, followed by that complementary projection.

Define a reflection J that acts as plus one on the range of P and minus one on its perpendicular complement. J is unitary. Conjugating A by J keeps the diagonal blocks unchanged and reverses the signs of the off-diagonal blocks.

The average of A and J A J is therefore exactly the pinched operator.

Apply the Ky Fan triangle inequality to that average. Homogeneity contributes the factor one half, and unitary invariance says J A J has the same Ky Fan sums as A. We conclude that pinching cannot increase any Ky Fan sum.

This argument is short because we have done the work of proving both the variational principle and the triangle inequality.

## Toward majorization

Suppose A has singular values three and three, while B has singular values five and one. The first Ky Fan sum of A is three, at most five. The second Ky Fan sums are equal at six.

So every Ky Fan sum of A is at most the corresponding sum for B. Yet the second singular value of A is three, greater than the second singular value of B, which is one.

These are comparisons of cumulative totals, not component-by-component comparisons. The name for this kind of ordering is weak majorization.

## What to reconstruct

First, start from the singular-value decomposition and derive the orthonormal-pairing upper bound. Write down the overlap weights and prove both their individual upper bounds and their total upper bound.

Second, use that variational characterization to prove the triangle inequality, carefully distinguishing the test frames from the maximizing frames.

Third, calculate the two-by-two diagonal counterexample and explain exactly which false inequality it disproves.

Finally, derive the pinching identity by multiplying the two-by-two block matrices. From that one identity, recover Ky Fan contraction under pinching.

We now have the ingredients for a theory that compares whole spectra by their partial sums.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

Let \(A:E\to F\) be finite dimensional, and let \(\sigma_1(A)\ge\sigma_2(A)\ge\cdots\ge0\). Define \(K_k(A)=\sum_{j=1}^k\sigma_j(A)\) (with zeros appended). For \(k\le\min(\dim E,\dim F)\),
\[
K_k(A)=\max_{\substack{u_1,\ldots,u_k\ \mathrm{orthonormal\ in}\ F\\v_1,\ldots,v_k\ \mathrm{orthonormal\ in}\ E}}
\operatorname{Re}\sum_{i=1}^k\langle u_i,Av_i\rangle.
\]
By SVD, the pairing is bounded by \(\sum_j\sigma_j a_jb_j\), where \(a_j^2=\sum_i|\langle u_i,u_j^{(A)}\rangle|^2\), \(b_j^2=\sum_i|\langle v_j^{(A)},v_i\rangle|^2\), and \(\sum_j a_j^2,\sum_jb_j^2\le k\); hence \(w_j=a_jb_j\in[0,1]\), \(\sum_j w_j\le k\), and the weighted decreasing-sum bound yields \(K_k(A)\). SVD witnesses attain the bound. This proves \(K_k(A+B)\le K_k(A)+K_k(B)\), together with unitary invariance and absolute homogeneity.

For square \(A\) and orthogonal \(P\), define \(\Pi_P(A)=PAP+(I-P)A(I-P)\) and \(J=2P-I\). Since \(\Pi_P(A)=\frac12(A+JAJ)\) and \(J\) is unitary, \(K_k(\Pi_P(A))\le K_k(A)\). Both examples in the narration distinguish cumulative domination from coordinatewise singular-value inequalities.

**Lean bridge (verbatim excerpts).** `ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/KyFan.lean` proves the following localization form of the Ky Fan triangle inequality, assuming the finite-restriction approximation hypothesis `hfr`:

```lean
theorem kyFanGaugeReal_add_le_of_exists_finiteRestriction {S T : E →L[𝕜] F}
    (hfr : ∀ (n : ℕ) (ε : ℝ), 0 < ε → ∃ v : Fin (n + 1) → E,
      ((S + T).singularValue n : ℝ) <
        (((S + T) ∘L (Submodule.span 𝕜 (Set.range v)).subtypeL).singularValue n : ℝ) + ε)
    (k : ℕ) :
    ((S + T).kyFanGauge k : ℝ) ≤ (S.kyFanGauge k : ℝ) + (T.kyFanGauge k : ℝ) := by
```

The type `E →L[𝕜] F` is a bounded linear map; `kyFanGauge k` is the sum of the first `k` zero-indexed approximation singular values. The general complete-source inequality is imported from TauCeti in this file; the displayed local theorem records a weaker-hypothesis localization proof, and must not be mistaken for an unconditional statement.

`DavisKahan/FiniteDimensional/DirectRotation/Majorization.lean` contains the finite two-block pinching consequence:

```lean
theorem kyFanSum_pinch_le
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (A : E →ₗ[𝕜] E) (k : ℕ) :
    (pinch U A).kyFanSum k ≤ A.kyFanSum k := by
```

Here `E →ₗ[𝕜] E` is a linear endomorphism of the finite-dimensional ambient space, and `pinch U A` removes the off-diagonal blocks relative to `U ⊕ Uᗮ`. The finite Ky Fan variational engine is imported from `TauCeti.Analysis.InnerProductSpace.KyFan`; `ForTauCeti/Analysis/InnerProductSpace/KyFan.lean` records that its original local development was upstreamed.

**Reconstruction exercise:** verify the diagonal pair \(A=\mathrm{diag}(3,0)\), \(B=\mathrm{diag}(0,3)\), then prove both the Ky Fan triangle inequality and the pinching inequality from the variational characterization.

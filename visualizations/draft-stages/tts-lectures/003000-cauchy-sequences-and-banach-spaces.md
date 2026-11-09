# Cauchy sequences and Banach spaces

<!-- BEGIN SPOKEN LECTURE -->

A norm supplies a distance between vectors: the distance from x to y is the norm of their difference. A sequence converges if its members approach a vector in the space. But this definition asks us to know that the limit already exists. A Cauchy sequence offers a way to detect convergence candidates from distances between its own terms.

Often an argument produces a sequence of increasingly accurate approximations, but the object being approximated is not yet available. We need a way to recognize a convergent process from the approximations themselves.

A Cauchy sequence is designed to do exactly that. A Banach space is a normed vector space in which every Cauchy sequence has a limit that belongs to the space. Completeness holds for many familiar normed spaces but fails for others. The distinction becomes concrete through an explicit example of a Cauchy sequence that has no limit within its space.

## Getting closer without seeing the destination

Start with a sequence of numbers: one half, three quarters, seven eighths, fifteen sixteenths, and so on. Each number is one minus an increasingly small power of one half. We know that the sequence converges to one.

But suppose we do not tell ourselves the value one. We can still observe that late terms are very close to one another. The thousandth and the two-thousandth terms differ by an extremely small amount. If we choose a sufficiently late starting point, every pair of terms beyond it will be as close as we demand.

This is the Cauchy condition. Given any positive tolerance, there is a stage beyond which the distance between every two sequence members is smaller than that tolerance.

There are two quantifiers worth hearing carefully. We can choose any tolerance, however small. And after choosing the tolerance, we must find a stage that works for all pairs of later terms. It is not enough that consecutive terms become close. They must eventually stay uniformly close to one another, even when their indices are far apart.

The classic warning example is the sequence of partial sums of the harmonic series. Start at one, then add one half, then one third, then one fourth, and continue adding reciprocals of the positive integers. The difference between consecutive partial sums is one over n, which goes to zero. Yet the sums themselves grow without bound. For example, the terms with denominators n plus one, n plus two, and so on through two n add up to at least one half. There are n such terms, and each is at least one divided by two n. So no matter how late we begin, we can find later partial sums separated by at least one half. The sequence is not Cauchy.

The Cauchy definition asks for control of the entire tail, not merely control of individual steps.

## Convergent sequences must be Cauchy

We can prove one direction immediately in any normed space. Suppose a sequence converges to a vector v.

Choose a positive tolerance epsilon. Since the sequence converges, there is a point after which every term lies within epsilon divided by two of v.

Take any two terms beyond that point. To travel from the first to the second, we can go from the first to v and then from v to the second. The triangle inequality says the direct distance is at most the sum of those two distances. Each is less than epsilon divided by two, so their sum is less than epsilon.

That proves every convergent sequence is Cauchy.

The converse is the interesting question. If a sequence is Cauchy, must its limit exist in the space we are studying? The answer depends on the space.

## A first warning from number systems

The rational numbers give a simple picture of the problem. We can build a sequence of rational decimal approximations to the square root of two. Every term is rational. The approximations become arbitrarily close to one another. But their limit, the square root of two, is not rational.

So the rational numbers, with ordinary absolute-value distance, contain a Cauchy sequence that has no rational limit.

There is a technical distinction to preserve: the rationals are not a vector space over the real numbers, because multiplying a rational number by an arbitrary real number need not give a rational number. Thus the rationals illustrate incomplete metric spaces, but they are not our example of an incomplete real normed vector space.

We will construct a genuine real vector-space example next. First we should name the property we are investigating.

A normed vector space is complete if every Cauchy sequence of its vectors converges to a vector still inside that space. A complete normed vector space is called a Banach space.

This definition links algebra to analysis. The vector-space structure lets us add and scale vectors. The norm lets us measure approximation error. Completeness guarantees that the limiting object produced by arbitrarily consistent approximations does not escape the space.

## Why ordinary finite-dimensional spaces are complete

Our first theorem is that every finite-dimensional real or complex normed vector space is complete.

We can see the proof by starting with the usual coordinate space. Suppose a sequence of vectors in a fixed n-dimensional real space is Cauchy under Euclidean distance.

Each coordinate difference is at most the Euclidean length of the entire vector difference. Therefore, for each coordinate position, the sequence of real numbers occupying that position is Cauchy. The real numbers are complete, so every coordinate sequence has a real limit.

Gather those coordinate limits into one vector. Because there are only finitely many coordinates, we can make every coordinate difference small at the same time by going far enough out in the sequence. The resulting Euclidean distance to the limit vector approaches zero.

We have constructed the vector limit using the completeness of the real numbers, one coordinate at a time. The argument works over the complex numbers as well, because complex coordinates have convergent real and imaginary parts.

What if a finite-dimensional vector space carries a norm other than the Euclidean one? Every norm in a fixed finite dimension is equivalent to the Euclidean norm: each bounds the other up to a positive constant. Consequently a sequence is Cauchy in one if and only if it is Cauchy in the other, and it converges in one if and only if it converges in the other. Completeness therefore transfers between finite-dimensional norms.

This is why completeness is usually invisible in elementary finite-dimensional linear algebra. Once the scalars are real or complex, every normed finite-dimensional space already has it. Infinite-dimensional spaces will force us to think about it much more carefully.

## An incomplete space of perfectly good functions

Now consider polynomials on the interval from zero to one. A polynomial is a function built from a finite sum of nonnegative integer powers of x with real coefficients. We can add two polynomials or multiply a polynomial by a real number and still obtain a polynomial. So these polynomials form a real vector space.

Give a polynomial a norm by looking at its largest absolute value on the interval. This is the maximum, or supremum, norm. The word supremum means the least upper bound: the smallest number that is at least as large as every value in the collection. For continuous functions on a closed interval, the largest value is actually attained, so the supremum equals a maximum.

The norm satisfies the three rules. It is nonnegative and vanishes only if the polynomial is zero everywhere on the interval, hence is the zero polynomial. Scaling behaves as expected. And the pointwise triangle inequality, followed by taking the maximum, establishes the norm triangle inequality.

The space looks mathematically well behaved. But it is not complete.

To see the problem, form a sequence of polynomials by truncating a geometric series. The first is the constant one. The next is one plus x divided by two. The next is one plus x divided by two plus x squared divided by four. Continue, adding one new power each time, with the coefficient halved at every step.

For any x between zero and one, x divided by two has absolute value at most one half. A geometric series with such a ratio converges, and its sum is one divided by the quantity one minus x divided by two.

Call that limiting function f. It is continuous on our interval because the denominator stays between one half and one. But f is not a polynomial.

Let us first prove that the polynomial sequence is Cauchy in the maximum norm. When we compare a later truncation with an earlier one, their difference is just a tail of the geometric series. The size of that tail, at every point in our interval, is at most the geometric tail we would get by substituting x equal to one. Starting after the term with exponent n, the infinite remaining tail is at most two to the power negative n. This bound is independent of x. So the maximum difference between any two sufficiently late polynomials can be made as small as we wish.

The polynomials are Cauchy.

They also approach f uniformly, meaning the maximum absolute difference between the nth polynomial and f approaches zero. But the limit function is not a polynomial.

We can prove that last statement without appealing to how the graph looks. Suppose some polynomial p agreed with f throughout the interval. Multiplying the supposed equality by one minus x divided by two would give a polynomial identity: that factor times p equals the constant one at every point between zero and one.

A polynomial that is zero at infinitely many real points must be the zero polynomial. Therefore this identity, if true throughout an interval, would be true for all real x. Substitute x equal to two. The factor one minus x divided by two becomes zero, so the left side is zero, while the right side is one. Contradiction.

Thus no polynomial is equal to f on the interval. The Cauchy sequence has no limit among the polynomials, even though it converges when we allow more general continuous functions. Our normed space of polynomials is incomplete.

This example also shows why a sequence can have a perfectly definite limit in a larger setting and still fail to converge in the space we originally chose. Completeness is a property of both the distance and the collection of allowed objects.

## Completing the picture with continuous functions

The natural larger space here consists of all continuous real-valued functions on the interval from zero to one, equipped with the same maximum norm. Call this the space of continuous functions with the uniform norm.

This space is complete. Let us prove it rather than take it on trust.

Suppose a sequence of continuous functions is Cauchy in the maximum norm. At any fixed input x, the differences between late function values are bounded by the maximum difference between those functions. Therefore the sequence of real numbers obtained by evaluating at x is Cauchy. Since the real numbers are complete, those values approach a real limit.

We can define a candidate limit function f by taking that limit separately at each x. But we must still show two things: that the convergence is uniform, and that the resulting function is continuous.

For uniform convergence, choose a small tolerance. The Cauchy condition provides an index after which the maximum difference between any pair of functions is below that tolerance. Fix one of those functions, and let the other one's index tend to infinity at each input. The value of the limiting function cannot be farther from the fixed function than the same tolerance. Because this bound holds for every input x, it is a uniform bound. The sequence therefore converges to f in the maximum norm.

Why is f continuous? Choose an input point and a positive error tolerance. Uniform convergence lets us pick one continuous function in the sequence that differs from f by less than one third of the tolerance everywhere. Because that chosen function is continuous, sufficiently nearby inputs have its values within another third of the tolerance. To compare f at the two inputs, pass from f to the chosen function at the first input, travel along the chosen continuous function to the second input, then pass back to f. The three error terms each fit within a third of the tolerance.

So f is continuous. It belongs to our space, and our original Cauchy sequence converges to it. The continuous functions with the maximum norm form a Banach space.

Notice how the proof has exposed the roles of its assumptions. The completeness of the real numbers gave us a pointwise limit. The *uniform* Cauchy condition allowed us to prove continuity of that limit. And continuity was necessary because our chosen space contains continuous functions only.

## Completeness and infinite series

There is a second way of recognizing Banach spaces that will become extremely useful for operators.

A series of vectors is an infinite sum, defined by looking at its finite partial sums. Suppose the sum of the norms of its terms is finite. We call the series absolutely convergent in norm.

In a Banach space, absolute convergence guarantees that the vector series converges. The proof is short. Compare two late partial sums. Their difference is a sum of the intervening terms. The triangle inequality bounds its norm by the sum of the norms of those terms. Because the scalar series of norms converges, every sufficiently late tail is small. Thus the partial sums are Cauchy. Completeness turns that Cauchy condition into the existence of a vector limit.

This is the mechanism behind many constructions in functional analysis. We define a candidate operator or function as an infinite series. We estimate the norms of its terms by an ordinary convergent numerical series. Then completeness provides the object whose existence we wanted.

There is even a converse theorem: a normed space is complete if every series whose term norms have finite sum actually converges in that space.

The reverse argument contains a useful idea. Start with any Cauchy sequence. Choose a subsequence whose successive terms get exceptionally close, close enough that the distance between the kth selected term and the next selected term is less than two to the power negative k. The increments between these selected terms then have summable norms. By our assumption about series, their sum converges. The selected terms are obtained by adding those increments to the first selected term, so the subsequence converges. Finally, because the original sequence is Cauchy, having one convergent subsequence forces the entire sequence to converge to the same limit.

This proves the converse and reveals an important proof technique: extract a subsequence that converges quickly enough to turn a general Cauchy problem into an absolutely convergent series.

## Reconstruction and consequences

There are two reconstructions worth trying before proceeding.

First, explain why the polynomial example fails to be Banach. The crucial ingredients are not merely that polynomials can approximate a non-polynomial. They are that we have a specific Cauchy sequence of polynomials in a specified norm, that we have identified its only possible uniform limit, and that this limit does not belong to the polynomial space. Each part matters.

Second, reconstruct the proof that a uniformly Cauchy sequence of continuous functions has a continuous limit. You need pointwise completeness to define the candidate. Then you need the uniform bound to compare the candidate with one fixed continuous function. Finally, use continuity of that fixed function and a three-part triangle inequality.

The same pattern also proves convergence in spaces of bounded operators and in operator power series: build a candidate limit using completeness, then show that it satisfies the required uniform estimate.

A Banach space is not yet a Hilbert space. A Hilbert space has an inner product, which gives notions of angle and perpendicularity, and it is complete under the norm defined by that inner product. The analytic foundation is already precise: a norm measures errors, a Cauchy condition measures internal consistency among approximations, and completeness ensures that consistent approximations have an allowed limit.

<!-- END SPOKEN LECTURE -->

---

## Companion: symbolic facts and Lean correspondence (not TTS narration)

A sequence \((x_n)\) in a normed space \(E\) is Cauchy if
\[
\forall\varepsilon>0\;\exists N\;\forall m,n\ge N:\quad \|x_m-x_n\|<\varepsilon.
\]
A Banach space is a normed space for which every Cauchy sequence converges to a point of that space. In a Banach space, \(\sum_n \|v_n\|<\infty\) implies \(\sum_n v_n\) converges. Every finite-dimensional normed space over \(\mathbb R\) or \(\mathbb C\) is complete, and a closed subspace of a Banach space is complete.

**Actual Lean source correspondence.** The following one-line use of `FiniteDimensional.complete` occurs in `ForTauCeti/Analysis/InnerProductSpace/CompactApproximationEigenvalues.lean`:

```lean
have : CompleteSpace (W : Submodule 𝕜 E) := FiniteDimensional.complete 𝕜 W
```

`CompleteSpace` is Lean's typeclass expressing completeness. This step supplies completeness for a finite-dimensional subspace `W` in the surrounding proof. The source context carries the needed scalar and dimension assumptions; the snippet is not a standalone compiled file.

A second source excerpt, from `ForTauCeti/Analysis/InnerProductSpace/ProjValMeasure/Subspace.lean`, shows another route to completeness:

```lean
noncomputable instance pvmRangeSubspace_completeSpace
    (P : TauCeti.ProjValMeasure ℝ H) (B : Set ℝ)
    (hB : MeasurableSet B) :
    CompleteSpace (pvmRangeSubspace P B hB) := by
  change CompleteSpace (P.proj B hB).range
  exact (ContinuousLinearMap.IsIdempotentElem.isClosed_range
    (P.proj_idem B hB)).completeSpace_coe
```

The advanced objects in the signature are not prerequisites for this lecture. The structural idea is: a projected range is closed, and a closed subspace of a complete space is itself complete. Later lessons explain projection-valued measures and the hypotheses behind this instance. The mathematics-to-Lean bridge records an actual source declaration without claiming we have taught PVM theory yet.

Both excerpts are present in the supplied repository snapshot; no new Lean file was compiled for this draft. Narration stops at the marker above.

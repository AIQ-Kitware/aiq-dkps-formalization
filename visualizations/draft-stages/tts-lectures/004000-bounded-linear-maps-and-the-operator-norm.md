# Bounded linear maps and the operator norm

<!-- BEGIN SPOKEN LECTURE -->

A Banach space is a normed vector space in which every Cauchy sequence converges. Continuous functions on a compact interval, measured by their maximum absolute value, form one such space. What must a linear map do to preserve the limiting behavior of its inputs?

Linearity alone says that a map respects addition and scaling. It says nothing yet about whether a tiny input produces a tiny output. That missing requirement is the subject of this lecture. We will call it boundedness, explain why it means continuity for a linear map, and turn it into a numerical measurement called the operator norm.

## An operator we can measure

Imagine a plane, equipped with its ordinary Euclidean distance. Define a linear map that triples the horizontal component of a vector and halves the vertical component. If our input is three units right and four units up, the output is nine units right and two units up.

But to understand the map's size, looking at one input is not enough. We need a bound that works for every input. Let the horizontal and vertical components be x and y. The squared output length is nine times x squared, plus one quarter times y squared. That is at most nine times the sum of x squared and y squared. Take square roots. The output length is at most three times the input length.

And this bound is exact. Feed the map a horizontal unit vector. Its output has length three. No smaller constant could work for all vectors. So we can say the map's operator norm is three.

Notice what was measured. We did not ask how large the entries of one coordinate matrix were. We asked for the greatest possible amplification of vector length, relative to norms already chosen on the input and output spaces.

## What bounded means

Now let E and F be normed vector spaces. A linear map T from E to F is called bounded if there is some finite nonnegative number M such that, for every input vector, the length of T applied to that vector is no larger than M times the length of the input.

This can be a confusing use of the word bounded. It does not mean every output fits inside one fixed ball, regardless of the input. Even the map that doubles every real number produces arbitrarily large outputs as its inputs grow. It is bounded because the output never grows faster than a fixed multiple of the input.

Why is that condition useful? Suppose a sequence of inputs approaches some vector x. The difference between each input and x becomes small. By linearity, the difference between their outputs is just T applied to that input difference. The bound on T says the output difference is at most M times the input difference. So the outputs approach T of x.

That proves every bounded linear map is continuous. In fact it gives something stronger: a single multiplier M works to control errors everywhere, not merely near one particular input.

## Why continuity gives a bound

The remarkable fact is that, for linear maps between normed spaces, the converse is true. A linear map is continuous if and only if it is bounded.

Let's prove the harder direction. Suppose T is continuous at zero. Choose an output tolerance of one. Continuity says there is some positive input radius, call it delta, such that every input shorter than delta has an output shorter than one.

Now take any nonzero input x, even a very large one. Scale x down until its length is delta divided by two. This scaled input is safely inside the small ball where we know T's output has length below one.

Because T is linear, scaling x down also scales its output by the same factor. Undo the scaling. We discover that the length of T of x is less than two divided by delta, times the length of x.

That is exactly a boundedness estimate. The zero vector satisfies it automatically. Nothing about finite dimension entered the argument.

Also notice that we needed continuity only at zero. For a linear map, controlling differences near zero already controls differences near every point: subtract the two inputs, apply T, and use linearity.

## The smallest working multiplier

Many numbers M may satisfy the boundedness estimate. Our stretching example works with three, but it also works with four, twenty, or a million. The operator norm chooses the least possible bound.

For a nonzero input, consider the ratio of output length to input length. Because a linear map respects scaling, we can always rescale the input to have length one without changing this ratio. Therefore the operator norm is the supremum of the output lengths over all unit inputs.

Supremum means the smallest number that is at least as large as every value under consideration. There need not be a single vector that achieves it. This matters in infinite dimensions. We can have a sequence of unit inputs whose output lengths approach the operator norm, without any unit input attaining it.

The operator norm itself obeys the norm rules for bounded linear maps. It is nonnegative. It vanishes only for the zero map. Scaling an operator scales its norm by the absolute value of the scalar. And the norm of a sum of operators is at most the sum of their norms, because we can apply the vector triangle inequality to their outputs.

There is another property that is especially useful: the norm of a composition is at most the product of the two operator norms. If T amplifies lengths by at most three, and S amplifies lengths by at most four, applying T and then S amplifies lengths by at most twelve. We obtain the general rule by applying the two bounds in succession.


## What happens in finite and infinite dimensions

In finite-dimensional normed spaces, every linear map is bounded. Why? Pick a basis for the input space. Any input is a finite linear combination of the basis vectors. Apply the map and use the triangle inequality. Its output length is bounded by a fixed weighted sum of the absolute coordinate values. Equivalence of finite-dimensional norms, which we developed earlier, bounds that coordinate sum by a constant times the input norm. Combining the two estimates gives boundedness.

So a linear map on an ordinary finite matrix space cannot be discontinuous. But that convenience disappears in infinite dimensions.

Consider polynomials on the interval from zero to one, equipped with the maximum norm. Define a linear map that differentiates a polynomial. Its output is another polynomial, and the map respects sums and scalar multiples.

Now feed it the polynomial x to the power n. Each such polynomial has maximum absolute value one on the interval. Its derivative is n times x to the power n minus one, whose maximum absolute value is n. The input sizes stay at one while the output sizes grow without bound.

Therefore differentiation is not bounded as a map from this polynomial space to itself under the maximum norm. It is not continuous in that norm, despite being perfectly linear and defined on every polynomial.

We will eventually study operators like differentiation on carefully chosen domains. That is why the distinction between linear and bounded is fundamental, and why an operator's domain cannot be treated as an irrelevant technicality.

## Reconstruct the argument

Try two questions before moving on.

First, why is the operator norm of our horizontal-stretching map exactly three, rather than merely at most three? The answer requires both an inequality valid for every vector and an example achieving equality.

Second, suppose you are given a linear map that is continuous at zero. Do not memorize the conclusion that it is bounded. Reconstruct the scaling argument. Take any input, shrink it into the small ball supplied by continuity, and then scale the resulting inequality back up.

The central conclusion is that boundedness, continuity, and uniform control of output errors are three faces of the same property for a linear map between normed spaces. The operator norm records the best global amplification bound.

<!-- END SPOKEN LECTURE -->

---

## Companion: symbolic facts and Lean correspondence (display only)

For normed spaces \(E,F\) and a linear map \(T:E\to F\), boundedness means \(\exists M\ge0\,\forall x\;\|Tx\|\le M\|x\|\). For a linear map this is equivalent to continuity at zero, and hence continuity everywhere. The operator norm is \(\|T\|=\sup_{\|x\|=1}\|Tx\|\) when the unit sphere is nonempty; the defining supremum over \(\|x\|\le1\) also works for the zero space. For bounded maps \(T:E\to F\), \(S:F\to G\), \(\|S\circ T\|\le\|S\|\|T\|\).

**Lean bridge.** The codebase represents bounded linear maps as `E →L[𝕜] F`, not merely `E →ₗ[𝕜] F`. In the actual DKPS module `ForTauCeti/Analysis/Normed/Operator/Restriction.lean`, the theorem `ContinuousLinearMap.opNorm_codRestrict_eq` uses the following steps:

```lean
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T) ?_
    intro x
    exact T.le_opNorm x
```

`T.le_opNorm x` is the pointwise bound \(\|Tx\|\le\|T\|\|x\|\). `opNorm_le_bound` converts a pointwise estimate into a bound for the operator norm. Here the theorem proves that restricting the codomain to a subspace containing the range preserves the norm, a use of the general result rather than a newly introduced norm axiom.

**Provenance and validation.** This snippet is present in the supplied 2026-11-07 snapshot and is authored in the DKPS `ForTauCeti` staging tree. The appendix is a source excerpt, not a standalone compiled proof. The spoken lecture ends above.

# 041000 — Operator trigonometric functions

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `032000` finite functional calculus; `034000` positive square roots; `039000` matrix exponentials; `040000` unitary flows. **Next:** cross-Gram overlap, principal angles, and operator-angle constructions.

<!-- BEGIN SPOKEN LECTURE -->

# How can we take the sine of an operator?

The cosine of an angle is a number. We learned it first from triangles and circles. But later in spectral theory we will see expressions such as the sine of an operator, or the arcsine of a positive operator.

These are not metaphors, and they are not instructions to apply sine separately to every matrix entry. They are operators defined by spectral or power-series constructions, with the usual matrix entries determined only after choosing a basis.

Our task today is to understand what those constructions mean, why they are well-defined, and what must be checked before using an inverse trigonometric function.

## Begin with diagonal matrices

Suppose A is a diagonal real matrix with diagonal entries zero and sixty degrees expressed in radians. In other words, the second entry is pi divided by three.

Because A is diagonal, it acts independently along the two coordinate axes. On the first axis its eigenvalue is zero. On the second its eigenvalue is pi over three.

What should cosine of A do? The natural answer is to multiply the first coordinate by cosine zero, which is one, and the second by cosine pi over three, which is one half.

So cosine of A is the diagonal operator with entries one and one half. Sine of A is diagonal too, with entries zero and the square root of three divided by two.

This immediately suggests a principle: when an operator has a complete orthonormal eigenbasis, apply the scalar function to each eigenvalue while keeping the eigenspaces in place.

That is finite functional calculus, which we developed earlier. The eigenvectors do not have to align with the coordinate axes we originally chose. If A is expressed in a rotated basis, its cosine is rotated back in the same way.

The operator cosine therefore depends on the transformation itself, not on the accident of its matrix representation.

## Rebuild sine and cosine from series

There is another route that doesn't begin with eigenvectors. In our study of exponentials, the even and odd terms of a power series gave ordinary cosine and sine.

We can repeat that construction for a bounded operator A.

Cosine of A is the identity minus A squared divided by two factorial, plus A to the fourth divided by four factorial, and so on with alternating signs.

Sine of A is A minus A cubed divided by three factorial, plus A to the fifth divided by five factorial, and so on.

Why do the sums converge? The operator norm of any power A to the n is bounded by the norm of A raised to the n. Each operator series is dominated by a convergent numerical factorial series. Completeness of the bounded-operator space gives the limit.

For a self-adjoint matrix, both constructions agree. Apply the series to an eigenvector. Every power of A acts by the corresponding power of its eigenvalue. The operator series therefore acts by the scalar sine or cosine of that eigenvalue, exactly as spectral calculus predicts.

And because both sine of A and cosine of A are built from powers of the same operator, they commute. This will matter when we multiply them.

## Recover a trigonometric identity

For ordinary numbers, sine squared plus cosine squared equals one. Does the same identity hold for operators?

Yes, when sine and cosine are defined by these power series for one bounded operator.

To see the idea without doing an enormous expansion, remember that the scalar power series satisfy the identity, and finite spectral calculus transfers it eigenvalue by eigenvalue for a self-adjoint matrix.

In each eigendirection of A, the square of sine of A plus the square of cosine of A multiplies by sine squared lambda plus cosine squared lambda. That equals one. Since the eigendirections form a basis, the operator sum is the identity.

This is already enough for our finite-dimensional self-adjoint applications. The identity also extends to general bounded operators through the power-series algebra, but we don't need that broader proof today.

Be careful about the meaning of the square here. Cosine squared of A means cosine of A composed with itself. It does not mean the matrix obtained by squaring each cosine entry.

An especially useful case is an orthogonal projection P. Since P squared equals P, any power of P after the first is just P. Spectral calculus separates its two eigenvalues, zero and one.

If we apply cosine to t times P, we get the identity on the orthogonal complement of the projected space, and cosine t on the projected space. Equivalently, we get the identity plus cosine t minus one times P.

For sine of t P, the complement vanishes and the projected space is multiplied by sine t. So sine of t P is simply sine t times P.

This example shows how a complicated-looking operator function can become very transparent once we know its spectral pieces.

## What about inverse trigonometric functions?

Now we come to a subtlety. To apply a function of an operator, that function must be defined at every spectral value we intend to use.

The real arcsine is defined on numbers from negative one to one. So if A is self-adjoint and all its eigenvalues lie in that interval, we may define arcsine of A by applying arcsine to each eigenvalue.

The result is self-adjoint, because its eigenvalues are real and it has the same orthogonal spectral projections.

But arcsine does not undo sine on every real angle. For instance, sine of thirty degrees equals sine of one hundred fifty degrees. The inverse sine chooses its principal output between negative ninety and positive ninety degrees.

So if we start with a large angle, apply sine, and then apply arcsine, we generally do not get the original angle back.

The same issue occurs for the operator. Arcsine of sine of A is guaranteed to recover A only when the spectrum of A lies within the principal inverse-sine interval. Without that spectral restriction, the result may fold different eigenvalues onto the same value.

This is not a minor technicality. Spectral perturbation results often measure an angle by its sine. The sine by itself cannot distinguish an angle from its supplement. We will eventually need hypotheses that determine which branch of the angle is intended.

## The angle operator will use a safe range

Consider a positive self-adjoint contraction S. Positive means its eigenvalues are nonnegative; contraction means they are no larger than one in magnitude. Consequently, every eigenvalue lies between zero and one.

We can apply arcsine to S without ambiguity about its domain. The resulting operator has eigenvalues between zero and ninety degrees, and is positive.

That construction is exactly the kind of thing we will need for principal angles between subspaces. Those angles are conventionally chosen between zero and a right angle. Their sines belong to zero through one.

Later, instead of assigning one scalar angle to an entire pair of higher-dimensional subspaces, we will assemble an angle operator that carries multiple angles at once.

It helps to see why we went through operator modulus and positivity earlier. The modulus turns an operator into a positive operator. Spectral bounds tell us its eigenvalues lie in the allowed interval. Only then does the arcsine construction produce the intended angle operator.

We do not get to write arcsine of an arbitrary operator and assume everything works. The spectrum and the chosen functional calculus are part of the definition.

## Cosine, sine, and rotations

The same construction describes a unitary flow: a continuously varying family of length-preserving operators with identity at time zero.

Take a real operator J whose square is negative the identity. Suppose J commutes with a self-adjoint operator T. Think of J as a quarter-turn on each of several perpendicular planes, and T as specifying how quickly each plane rotates.

Then the exponential of J times T splits into two pieces: cosine of T, plus J times sine of T.

The reason is the same even-and-odd power calculation that produced the ordinary rotation matrix. The even powers of J contribute alternating signs. The odd powers leave one factor of J. Commutation allows us to collect those terms without changing their order.

In a principal plane where T has eigenvalue theta, the formula becomes the ordinary rotation through theta. In another plane with a different eigenvalue, it produces a different rotation.

A single operator equation can therefore describe many planar rotations at once.

There is a boundary condition hidden in that story: J must really act as a quarter-turn on the directions being rotated. If J vanishes on a kernel or only satisfies the square-minus-one law on a support, we must state that restriction. Later direct-rotation proofs handle exactly those support and kernel issues.

## Why the spectral range controls inverse functions


If an angle operator has spectrum between zero and ninety degrees, the sine and cosine functional calculus give positive contraction operators representing complementary parts of subspace overlap. The interval matters: inverse trigonometric functions recover their arguments only on the spectral branches where those scalar inverse identities hold.

For now, try three calculations from memory. Given a diagonal self-adjoint matrix, construct its sine and cosine by changing eigenvalues. Given a projection, derive sine and cosine of t times that projection. Finally, explain why arcsine of sine of A may fail to recover A even though the ordinary sine and cosine operator identities work perfectly.

The answers all come from one principle: a function of an operator must be interpreted through the operator's algebra and spectrum, not through its printed matrix entries.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

For a finite-dimensional self-adjoint \(A=\sum_j\lambda_jP_j\),
\[
\sin A=\sum_j\sin(\lambda_j)P_j,\qquad
\cos A=\sum_j\cos(\lambda_j)P_j,\qquad
(\sin A)^2+(\cos A)^2=I.
\]
For an orthogonal projection \(P\), \(\sin(tP)=(\sin t)P\) and \(\cos(tP)=I+(\cos t-1)P\). If \(A\) is self-adjoint and \(\sigma(A)\subseteq[-1,1]\), \(\arcsin(A)\) is defined by spectral calculus; \(\arcsin(\sin A)=A\) requires the appropriate principal-branch spectral restriction.

**Lean bridge.** `ForTauCeti/Analysis/Normed/Algebra/TrigonometricSeries.lean` constructs the series in a complete normed algebra. The exact definitions are:

```lean
noncomputable def cosSeries {𝕜 : Type*} [RCLike 𝕜] {A : Type*} [NormedRing A]
    [NormedAlgebra 𝕜 A] (x : A) : A :=
  ∑' n : ℕ, cosSeriesTerm (𝕜 := 𝕜) x n
```

```lean
noncomputable def sinSeries {𝕜 : Type*} [RCLike 𝕜] {A : Type*} [NormedRing A]
    [NormedAlgebra 𝕜 A] (x : A) : A :=
  ∑' n : ℕ, sinSeriesTerm (𝕜 := 𝕜) x n
```

The theorem `exp_mul_eq_cosSeries_add_mul_sinSeries` has explicit hypotheses `Commute J T` and `J * J * T = -T`; its conclusion identifies the exponential with the cosine series plus `J` times the sine series. The support-qualified square-minus-one hypothesis is more general than requiring `J * J = -1` everywhere.

`DavisKahan/FiniteDimensional/Core/AngleOperators.lean` uses `LinearMap.IsSymmetric.cfc ... Real.arcsin` to construct `angleOperator` from the positive sine-angle operator. That file also documents the necessary care with singular tangent branches. The exact operator-calculus API is a different layer from scalar `Real.sin` and `Real.cos`.

**Reconstruction:** Prove operator trigonometric identities in an eigenbasis, derive the projection formulas, state the spectral domain of arcsine, and explain the principal branch. Then split the exponential series under a commuting quarter-turn generator.

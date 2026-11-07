# Rayleigh quotients and extrema

<!-- BEGIN SPOKEN LECTURE -->

We have just proved that a finite-dimensional self-adjoint operator has an orthonormal eigenbasis. We can split any vector into eigenvector components, act on each component separately, and put the results back together.

Today we will use that decomposition to answer a different question. Suppose I give you a self-adjoint matrix A and a nonzero vector x. Can a single number describe how strongly A acts along the direction of x?

There is a natural candidate. Take the inner product of A x with x, then divide by the squared length of x. This number is called the Rayleigh quotient. It connects eigenvectors, quadratic forms, geometric optimization, and eventually the variational formulas we will use for Davis–Kahan theory.

The important part is not merely the definition. It is why optimizing this one number recovers the extreme eigenvalues, and why the directions at which it stops changing are precisely eigenvector directions.

## What does the quotient measure?

Start with a real two-dimensional vector. A x may point in a different direction from x. If we take the dot product of A x with x, we keep only the component of A x aligned with x, weighted by the length of x.

Dividing by the squared length makes the result independent of scale. Replace x by twice x. The numerator becomes four times as large, and so does the denominator. The quotient stays the same. We are measuring a property of the *direction*, not of the particular length of the vector.

Over the complex numbers we use the complex inner product. For self-adjoint A, this quadratic form is real, as we proved in the Hermitian lecture. So we can compare Rayleigh quotients using ordinary inequalities on real numbers.

If x is an eigenvector with eigenvalue lambda, then A x equals lambda times x. Its Rayleigh quotient is exactly lambda. Every eigenvector direction therefore gives one of the operator's eigenvalues.

What about a vector that is not an eigenvector? Its quotient still exists, but it does not generally equal an eigenvalue. Let's calculate one.

## A rotating direction between two eigenvectors

Take the symmetric matrix with rows two, one and one, two. We know from the previous lecture that its eigenvalues are three and one. Its normalized eigenvectors point along one, one and one, negative one.

Any unit vector in the plane can be written as cosine theta in the horizontal direction and sine theta in the vertical direction. Apply the matrix to that vector, then take the dot product with the original vector.

The calculation gives two plus twice cosine theta times sine theta. The double-angle identity turns this into two plus sine of two theta.

So as the direction moves around the unit circle, its Rayleigh quotient varies smoothly between one and three. It reaches three along the eigenvector with equal coordinates, and one along the eigenvector with opposite coordinates. In between, most directions give numbers that are not eigenvalues.

For example, along the horizontal axis the quotient is two. But two is not an eigenvalue of this matrix. The quotient records the quadratic form on a direction, not a claim that the direction is invariant.

We can now see the first major result: the smallest and largest eigenvalues are exactly the smallest and largest possible Rayleigh quotients.

## Why the extremes equal eigenvalues

Let A have orthonormal eigenvectors e one through e n, with real eigenvalues lambda one through lambda n. We may arrange the eigenvalues from smallest to largest for this argument.

Write any vector x as a sum of coefficients times those eigenvectors. Because the basis is orthonormal, the squared length of x is the sum of the squared magnitudes of its coefficients.

Apply A to x. It multiplies each coefficient by the corresponding eigenvalue. Taking the inner product with x gives the sum of each eigenvalue times that coefficient's squared magnitude.

Now divide by the squared length of x. The result is a weighted average of the eigenvalues. Every weight is nonnegative, and all the weights add up to one.

A weighted average cannot fall below the smallest number being averaged or rise above the largest. Therefore every Rayleigh quotient lies between the smallest and largest eigenvalues.

And these bounds are attained: choose an eigenvector for the smallest eigenvalue or an eigenvector for the largest. Its quotient is that eigenvalue.

So the minimum Rayleigh quotient equals the smallest eigenvalue, and the maximum equals the largest eigenvalue.

This proof also tells us about equality. The quotient reaches the largest eigenvalue only when all of the vector's nonzero components belong to eigenspaces carrying that largest eigenvalue. If the top eigenvalue repeats, the maximum occurs on an entire eigenspace, not just along one selected line.

## Why a weighted average is not the whole story

Our weighted-average formula gives the global extremes immediately. But it also invites a sharper question. What if the Rayleigh quotient stops changing at some direction that is neither a maximum nor a minimum?

Could that direction still be an eigenvector? Yes. In a three-dimensional example with three distinct eigenvalues, a middle eigenvector produces a stationary value. Moving in some directions raises the quotient; moving in others lowers it.

So stationary does not always mean maximum or minimum. We need a separate argument connecting stationary directions with the eigenvalue equation.

## Deriving the stationary-point condition

We can investigate small changes using calculus. Let x be any nonzero vector, and choose another vector h describing a possible direction of motion. Replace x by x plus t times h, where t is a small real number.

The Rayleigh quotient has a numerator, the inner product of A x with x, and a denominator, the squared length of x. Differentiate the numerator at t equals zero. Self-adjointness makes its derivative twice the real part of the inner product of A x with h.

Differentiate the denominator. Its derivative is twice the real part of the inner product of x with h.

The quotient rule now says that the derivative is twice, divided by the squared length of x, times the real part of the inner product of A x minus the Rayleigh quotient times x, with h.

Focus on the vector inside that inner product: A x minus R of x times x. It is the failure of x to satisfy the eigenvector equation with candidate eigenvalue R of x. In other words, it is an eigenvector residual.

If x is an eigenvector, this residual is zero, so every directional derivative is zero.

Conversely, suppose the quotient is stationary under every small change of x. The derivative must be zero for every h. Choose h to be the residual itself. The derivative becomes twice the squared length of the residual, divided by the squared length of x. That can be zero only when the residual is zero.

Therefore a nonzero direction is stationary for the Rayleigh quotient exactly when it is an eigenvector direction.

This is a genuine connection between calculus and spectral theory. The eigenvalue equation emerges as the condition that a quadratic ratio has no first-order change.

## How does this relate to Rayleigh–Ritz?

Earlier we constructed the Rayleigh–Ritz compression of an operator to a trial subspace. For an orthonormal coordinate embedding V, the compressed matrix is V star A V.

If we take a coordinate vector c in that trial space, its compressed Rayleigh quotient equals the ambient Rayleigh quotient of V c. This follows because V preserves lengths and because the adjoint transfers the inner product back into trial coordinates.

Thus the Ritz values are the stationary values of the Rayleigh quotient when we restrict ourselves to directions lying inside the trial subspace.

But restricted stationarity is weaker than stationarity in the whole ambient space. A vector may be optimal within the trial space while the operator still pushes part of it outside. That outside component is exactly what the Ritz residual records.

So we now see a useful distinction. A Rayleigh quotient measures one direction's quadratic form. A Ritz value is a stationary value under directions available in a trial subspace. An actual eigenvalue comes with stationarity under all directions in the ambient space.

## Why we are not finished with variational theory

The smallest and largest eigenvalues are easy to recover by optimizing over all unit vectors. But how could we recover the second-largest eigenvalue, or the fifth? Simply searching for a second-highest value makes no sense: we can approach the largest eigenvector as closely as we like and get quotient values arbitrarily close to the maximum.

The answer will involve optimization over *subspaces*, not just individual vectors. We will ask what happens if we have to choose a whole subspace of a specified dimension, and then face the worst direction inside it. That is the idea behind the Courant–Fischer min–max theorem.

We will develop its dimension argument in the next lecture rather than smuggling it into today's result.

For now, reconstruct these three steps. First, write the Rayleigh quotient as a weighted average of eigenvalues. Second, prove why its endpoints are attained exactly on the extreme eigenspaces. Third, follow the directional derivative until the eigenvector residual appears, and explain why choosing the variation equal to that residual completes the proof.

We now have a bridge from spectral decomposition to optimization. Next time we will cross it using the geometry of intersecting subspaces.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematical facts and Lean correspondence (display only)

For nonzero \(x\) and finite-dimensional self-adjoint \(A\), define the real Rayleigh quotient
\[
R_A(x)=\frac{\langle Ax,x\rangle}{\langle x,x\rangle}.
\]
If \(x=\sum_j c_je_j\) in an orthonormal eigenbasis, then
\[
R_A(x)=\frac{\sum_j\lambda_j|c_j|^2}{\sum_j|c_j|^2}
\in[\lambda_{\min},\lambda_{\max}].
\]
For real \(t\), the directional derivative is
\[
\left.\frac{d}{dt}R_A(x+th)\right|_{t=0}
=\frac{2\operatorname{Re}\langle (A-R_A(x)I)x,h\rangle}{\|x\|^2}.
\]
Stationarity for every real direction \(h\) is equivalent to \((A-R_A(x)I)x=0\). The same conclusion applies over \(\mathbb C\) by treating directional variations as real-parameter curves.

**Lean bridge.** The pre-existing DKPS lecture companion `visualizations/lectures/002666_minmax/facts.lean` uses the accepted TauCeti Courant–Fischer API in an exact theorem example:

```lean
example : hT.eigenvalues hn k =
    ⨆ V : {V : Submodule ℝ E //
        finrank ℝ V = (k : ℕ) + 1},
      ⨅ x : {x : E //
          x ∈ (V : Submodule ℝ E) ∧ ‖x‖ = 1},
        RCLike.re ⟪T (x : E), (x : E)⟫_ℝ :=
  hT.eigenvalues_eq_iSup_iInf_re_inner hn k
```

Here `T` is a continuous self-adjoint operator over a finite-dimensional real Hilbert space, `hT` is its symmetry proof, and `hT.eigenvalues hn k` selects a sorted eigenvalue. The expression `RCLike.re ⟪T x,x⟫_ℝ` is the Rayleigh numerator; the vector hypothesis `‖x‖ = 1` makes the denominator one. The indexed supremum and infimum encode the more sophisticated subspace optimization to be proved in `028000`. This companion shows exactly where today's quotient enters the actual Lean theorem, without claiming that the displayed min–max theorem was proved in this lecture. The source lives in the DKPS lecture tree and imports the accepted TauCeti theorem; as in the provenance census, its current import location does not by itself identify the theorem's original donor history.

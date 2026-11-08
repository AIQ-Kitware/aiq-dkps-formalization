# 034000 — Positive square roots and their uniqueness

**Draft status:** audio-first mathematical lecture. **Prerequisites:** finite spectral theorem, finite functional calculus, self-adjoint operators, quadratic-form positivity. **Next:** the operator modulus.

<!-- BEGIN SPOKEN LECTURE -->

# Taking a square root of a matrix

If I tell you that a real number is nine, finding a square root is easy. Three works, and negative three works. But if I ask for the *nonnegative* square root, there is only one answer.

For matrices, there is a similar distinction. We can sometimes find many matrices whose square equals a given matrix. We want one special square root that is positive in the operator sense. The positive square root is defined through the spectral decomposition. It exists uniquely for a positive matrix, unlike an entrywise square-root construction, which does not respect changes of orthonormal basis.

Positive square roots define the operator modulus and provide the spectral ingredients for singular-value decomposition.

## Why entrywise square roots don't work

Consider a matrix with two diagonal entries, nine and one, and zeros elsewhere. Its positive square root is the diagonal matrix with entries three and one. So far, this looks like taking ordinary square roots.

But now imagine describing the very same operator using a different orthonormal basis. Its matrix might acquire nonzero off-diagonal entries. Taking an entrywise square root would not respect this change of coordinates, and there is no reason the resulting matrix should square back to the original.

This tells us what to preserve: not the table of entries, but the operator's action on its eigenspaces.

## Building the square root

Let P be a positive semidefinite, self-adjoint operator on a finite-dimensional real or complex inner-product space.

The finite spectral theorem gives an orthonormal basis of eigenvectors. For a self-adjoint positive matrix P, every eigenvalue is nonnegative, because evaluating its quadratic form on an eigenvector gives that eigenvalue times the squared norm.

Write any vector x as a sum of components along these eigenvectors. On a component corresponding to eigenvalue lambda, P multiplies by lambda.

Define a new operator S by doing the same thing, but multiplying that component by the ordinary *nonnegative square root* of lambda. This is an instance of functional calculus: S is the square-root function applied to P.

Now apply S twice. Along the lambda-eigenspace, the first application multiplies by square root of lambda, and the second does it again. Their product is lambda. So S squared equals P on every eigenvector and therefore on every vector.

S is also self-adjoint: it has a real diagonal representation in an orthonormal eigenbasis. And its eigenvalues are nonnegative, so S is positive semidefinite.

We have established existence without solving a new matrix equation entry by entry.

## A matrix we can check by hand

Consider the symmetric two-by-two matrix whose diagonal entries are five and whose off-diagonal entries are four.

The direction with equal coordinates is an eigenvector with eigenvalue nine. The direction with opposite coordinates is an eigenvector with eigenvalue one. Those two directions are perpendicular.

Our construction says that the square root must multiply the equal-coordinate direction by three and the opposite-coordinate direction by one.

When we express that operation back in ordinary coordinates, we get a matrix with two on the diagonal and one in each off-diagonal position.

Check its square. The upper-left entry is two times two plus one times one, giving five. The upper-right entry is two times one plus one times two, giving four. The other entries work the same way. So the square is exactly the original matrix.

The new matrix has eigenvalues three and one. It is positive, as required.

Notice that the entries five and four did not simply turn into their individual square roots. The eigenvectors tell us how to take the square root correctly.

## Why positivity gives uniqueness

We have found *a* positive square root. Could there be a different positive operator B whose square is also P?

Start with B, not with P. Because B is positive and self-adjoint, the finite spectral theorem gives an orthonormal eigenbasis for B. Every eigenvalue of B is a nonnegative real number.

Choose one of those eigenvectors. Suppose B multiplies it by a number called beta. Since B squared is P, applying P to this eigenvector multiplies it by beta squared.

And because beta is nonnegative, beta is precisely the nonnegative square root of beta squared.

What does the square-root construction applied directly to P do to that same eigenvector? P acts there by beta squared, so our constructed operator S acts there by beta.

Therefore B and S agree on an entire orthonormal basis of eigenvectors of B. Two linear operators that agree on a basis are equal. Thus B equals S.

That is the uniqueness proof. It does not assume in advance that B and P have conveniently chosen matching eigenbases. It derives what is needed from the equation B squared equals P.

If we remove positivity, uniqueness fails immediately: the negative of S also squares to P. In our numerical example, the matrix with ones on the diagonal and twos off the diagonal also squares to P, but it has a negative eigenvalue. Positivity rules out these alternative signs.

## What happens on zero eigenspaces?

Suppose P has a zero eigenvalue. Our positive square root uses square root of zero, which is zero. So S vanishes on exactly the same eigendirections as P.

In fact their kernels are equal. If P kills a vector, expand that vector in an eigenbasis and observe that it lies entirely in the zero-eigenspace, which S also kills. Conversely, if S kills a vector, then P, being S squared, kills it too.

If P is invertible, it has no zero eigenvalues. Then S is also invertible, with inverse formed by taking the reciprocals of its positive eigenvalues. If P is not invertible, its positive square root still exists. We have no need to divide by zero.

This matters later: we want to handle linear maps that collapse some directions, not only maps that can be inverted.

## Two rules worth remembering

First, taking the positive square root is compatible with an orthonormal change of coordinates. If we rotate or otherwise unitarily change the coordinate system, the new matrix for S is simply the transformed matrix for the original S. That follows because both matrices represent the same construction on the corresponding eigenspaces.

Second, S commutes with P. We can see this directly: both operators multiply the same eigenspace components by scalar values. The order of those multiplications does not matter. In fact, S also commutes with any polynomial in P.

But do not conclude that the square root of a product is always the product of the square roots. In general, products of positive matrices need not even be self-adjoint. That scalar-looking formula requires additional hypotheses, such as appropriate commutation.

## Why this construction matters

We have learned how to turn a positive operator P into a unique positive operator S with S squared equal to P.

Now recall a map A that is not necessarily square, self-adjoint, or invertible. Its source Gram operator, A adjoint times A, is always positive. So it always has a positive square root.

That new operator will be called the *modulus* of A. It will tell us exactly how much length A produces in each input direction, even when A also rotates, reflects, or embeds those directions somewhere else.

Three useful reconstructions are these: explain why entrywise square roots fail under a change of basis. Rebuild the two-by-two example by using the eigenvectors with equal and opposite coordinates. And prove uniqueness starting from an arbitrary positive square root B, rather than assuming that B is already diagonal in your favorite basis for P.

The spectral construction produces the unique positive square root, and its uniqueness follows by comparing any positive square root with the original positive operator through functional calculus.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematical facts and Lean correspondence (display only)

For finite-dimensional self-adjoint positive semidefinite \(P\), with distinct eigenvalues \(\lambda\ge0\) and spectral projections \(P_\lambda\), define

\[
P^{1/2}=\sum_{\lambda\in\sigma(P)}\sqrt\lambda\,P_\lambda.
\]

Then \(P^{1/2}\succeq0\), \((P^{1/2})^2=P\), and if \(B\succeq0\) and \(B^2=P\), then \(B=P^{1/2}\). Moreover \(\ker P^{1/2}=\ker P\) and \(P^{1/2}P=PP^{1/2}\).

The DKPS-staged source `ForTauCeti/Analysis/InnerProductSpace/Positive/SquareRoot/Eigenspace.lean` **imports** `TauCeti.Analysis.InnerProductSpace.Positive.SquareRoot` and proves the following additional eigenvector principle (exact signature):

```lean
theorem apply_eq_smul_of_apply_apply_eq_smul {S : E →ₗ[𝕜] E} (hS : S.IsPositive)
    {v : E} {μ : ℝ} (hμ : 0 ≤ μ)
    (hv : S (S v) = ((μ : 𝕜) * (μ : 𝕜)) • v) :
    S v = (μ : 𝕜) • v := by
```

The mathematical meaning is that a positive operator cannot act by the negative square root on a vector where its square acts by \(\mu^2\). This is a local refinement of the square-root theory now imported from TauCeti; the theorem signature is cited as a source bridge, not as a substitute for the preceding uniqueness proof.

`ForTauCeti/Analysis/InnerProductSpace/Polar/Isometry.lean` also uses the exact imported uniqueness result:

```lean
  have hmodsqrt : CFC.sqrt a = M.modulus :=
    CFC.sqrt_unique M.modulus_comp_modulus M.modulus_nonneg
```

Here `CFC.sqrt` denotes the positive square root from continuous functional calculus, and `M.modulus_nonneg` and `M.modulus_comp_modulus` supply positivity and the square equation. The current bounded-Hilbert-space API is more general than the finite-dimensional construction proved in the spoken lecture.

**Reconstruction:** Prove existence and uniqueness from the finite spectral theorem. Verify directly that \(\begin{pmatrix}2&1\\1&2\end{pmatrix}^2=\begin{pmatrix}5&4\\4&5\end{pmatrix}\), and exhibit a different, nonpositive square root.

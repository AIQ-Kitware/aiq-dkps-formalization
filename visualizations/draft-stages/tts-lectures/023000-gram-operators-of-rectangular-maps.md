# Gram operators of rectangular maps

<!-- BEGIN SPOKEN LECTURE -->

An arbitrary rectangular linear map has two associated positive operators: A adjoint A on its input space and A A adjoint on its output space. These Gram operators reveal the same positive singular-value data despite acting on spaces of potentially different dimensions.

A map from a plane into three-dimensional space is represented by a three-by-two matrix. It is not square. So we cannot even ask for its eigenvalues in the ordinary sense, because the equation A of x equals lambda times x would compare vectors living in different spaces.

But there is a way to turn that rectangular map into two square operators. The surprising fact is that both squares reveal the same positive nonzero spectral information, even though they act on different spaces.

This is the mathematical origin of the two sides of singular-value decomposition.

## A map and its adjoint

Call the starting map A. It takes vectors from a domain space E into a target space F. Both spaces have inner products, so A has an adjoint, A star, going in the reverse direction from F to E.

We now have two legitimate round trips.

Starting in E, apply A and then A star. This gives the operator A star A acting on E. We call it the right Gram operator, or the domain Gram operator.

Starting in F, apply A star and then A. This gives A A star acting on F. We call it the left Gram operator, or the target Gram operator.

The names right and left follow the order of multiplication: A star A has the adjoint on the left and A on the right. But do not let the labels obscure the important point. These operators have different domains. We cannot simply say they are equal.

Why should we care about two such products? Because they let us study a rectangular map using quadratic forms and eigenvalues, which we already know how to interpret in finite-dimensional spaces.

## Why both Gram operators are positive

Take any vector x in E. Evaluate the quadratic form of A star A at x. Moving the adjoint across the inner product gives the squared length of A of x.

Squared length is nonnegative. Therefore A star A is positive semidefinite. It is also self-adjoint, because taking its adjoint reverses the factors and returns the same product.

The same argument works for A A star: for a vector y in F, its quadratic form is the squared length of A star of y. Again, nonnegative and self-adjoint.

This is stronger than a naming convention. It means the eigenvalues of both Gram operators, in finite dimensions, are real and nonnegative. Their positive eigenvalues describe how much squared length A can create along certain preferred input directions, and how those same effects appear in the target space.

Notice how much this conclusion cost us. We did not need to assume that A was symmetric, square, invertible, or normal. Only an adjoint was required.

## A rectangular example you can calculate

Imagine E is a plane and F is three-dimensional. Define A to send the first coordinate direction to three times the first target direction, and the second coordinate direction to two times the second target direction. The third target direction never receives anything from A.

The matrix of A has three rows and two columns. Its first row is three, zero. Its second is zero, two. Its third is zero, zero.

Now calculate A star A. It acts on the two-dimensional input space. Its diagonal entries are nine and four, and its off-diagonal entries are zero.

Calculate A A star. It acts on three-dimensional target space. Its diagonal entries are nine, four, and zero.

The matrices have different sizes. Their eigenvalue lists are not identical if we include zeros: the target Gram has one additional zero. But the positive eigenvalues, nine and four, agree perfectly.

You can already guess the underlying length scales. Along the two preferred input directions, A stretches by three and two. The squares of these stretches are nine and four. Later we will call three and two the singular values of A.

That prediction is useful, but today we can prove the key spectral correspondence without relying on singular-value decomposition at all.

## Transporting an eigenvector from one side to the other

Suppose x is a nonzero eigenvector of the right Gram operator A star A, with eigenvalue lambda. So applying A star A to x gives lambda times x.

First, lambda is nonnegative, because the right Gram is positive. Now suppose lambda is *strictly positive*.

Apply A to both sides of the eigenvector equation. On the left we get A A star A of x. We can regroup this as A A star applied to A of x. On the right we get lambda times A of x.

Thus A of x is an eigenvector of the *left* Gram operator with the same eigenvalue lambda. There is one possible objection: perhaps A of x is zero, in which case it would not count as an eigenvector.

But if A of x were zero, then A star A of x would also be zero. Our original equation would say lambda times x is zero. Since lambda is positive and x is nonzero, that is impossible. So the transported vector is genuinely nonzero.

We have proved that every positive eigenvalue of the right Gram also appears on the left.

The reverse argument is symmetrical. Begin with a positive-eigenvalue eigenvector y of A A star. Apply A star. This produces a nonzero eigenvector of A star A with the same eigenvalue.

We have a correspondence in both directions. And more is true: restricted to the eigenspace of a positive lambda, A and A star become inverse transports after a suitable scaling by lambda. Therefore the corresponding positive-eigenvalue eigenspaces have the same dimension.

That dimension statement will matter when we begin distinguishing eigenvalue multiplicities.

## Why zero is different

All of that relied on lambda being positive. Zero is special, and the reason is not a technicality.

Suppose A star A of x equals zero. Take its inner product with x. The result is the squared length of A of x, so A of x must be zero. Conversely, if A of x is zero, then of course A star A of x is zero.

Therefore the kernel of A star A is exactly the kernel of A.

Likewise, the kernel of A A star is exactly the kernel of A star.

These kernels live in different spaces. Their dimensions can differ. In our three-by-two example, A has no nonzero input vector that it sends to zero, so the right Gram has no zero eigenvalue. But A star kills the third target coordinate direction, so the left Gram has a zero eigenvalue.

This explains the extra zero without any appeal to coincidence or a matrix calculation. Different ambient dimensions allow different numbers of directions that are invisible to the map or its adjoint.

In finite dimensions, the numbers of positive eigenvalues counted with multiplicity agree, and they equal the rank of A. The remaining dimensions contribute zero eigenvalues on each side.

## Connection to the Gram matrices of a vector family

We have seen this structure before. If A is the synthesis map of a family of vectors, then A star A is the Gram matrix on coefficient space. The other product, A A star, is the frame operator on ambient space.

Those were not unrelated constructions. They are the two Gram operators of the same rectangular map, viewed from opposite sides.

For an orthonormal frame, A star A is the identity on coefficient space, while A A star is the orthogonal projection onto the frame's range. The positive eigenvalues are all one; the target Gram may also have zeros corresponding to perpendicular directions.

For an arbitrary finite frame, the positive eigenvalues tell us which combinations of coefficients get amplified more or less strongly. Their square roots give the corresponding length factors.

One more consequence is worth keeping in view. The largest possible ratio of output length to input length, which is the operator norm of A, has its square equal to the largest eigenvalue of A star A in finite dimensions. The same maximum is obtained from A A star. We will prove this systematically when we study the spectral theorem and singular values.

## Reconstruct the argument

Try to prove these statements from memory: A star A is positive because its quadratic form is a squared norm. The kernels of A star A and A coincide. And a positive-eigenvalue eigenvector of A star A is sent by A to an eigenvector of A A star with the same eigenvalue.

Then test your reasoning on a one-row, two-column matrix that adds its two inputs. Work out the two Gram matrices. One is two-by-two and has eigenvalues two and zero. The other is one-by-one and has only the eigenvalue two. The common positive spectrum is exactly what the proof predicts.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematical facts and Lean correspondence (display only)

For a finite-dimensional linear map \(A:E\to F\), define
\[
G_R=A^*A:E\to E,\qquad G_L=AA^*:F\to F.
\]
Both are positive semidefinite. Their kernel identities are \(\ker G_R=\ker A\) and \(\ker G_L=\ker A^*\). For \(\lambda>0\), the maps \(x\mapsto Ax\) and \(y\mapsto \lambda^{-1}A^*y\) are inverse linear isomorphisms between the respective \(\lambda\)-eigenspaces. Consequently the positive eigenvalues have the same geometric multiplicities; after the finite self-adjoint spectral theorem this yields equality of positive algebraic multiplicities as well.

The DKPS-developed `ForTauCeti/Analysis/InnerProductSpace/Gram/Operator.lean` exposes the right and left Gram operators:

```lean
/-- Right Gram operator `A⋆A`. -/
@[expose]
noncomputable def rightGram (A : E →ₗ[𝕜] F) : E →ₗ[𝕜] E :=
  A.adjoint ∘ₗ A

/-- Left Gram operator `AA⋆`. -/
@[expose]
noncomputable def leftGram (A : E →ₗ[𝕜] F) : F →ₗ[𝕜] F :=
  A ∘ₗ A.adjoint
```

Here `E →ₗ[𝕜] F` is a linear map between two finite-dimensional inner-product spaces over real or complex scalars. `.adjoint` reverses its direction. The two output types make it impossible to confuse `rightGram A` and `leftGram A`. The same module also proves `isSymmetric_rightGram` and `isSymmetric_leftGram`. The stronger positivity conclusion follows from the squared-norm identity in the narration, not merely from symmetry.

The source header records DKPS development even though the definitions live in the `TauCeti` namespace. These declarations were checked against the supplied source snapshot; no new Lean compilation was performed.

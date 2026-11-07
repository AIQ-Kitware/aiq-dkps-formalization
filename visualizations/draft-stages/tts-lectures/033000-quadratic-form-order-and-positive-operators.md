# 033000 — Quadratic-form order and positive operators

**Draft status:** audio-first mathematical lecture. **Prerequisites:** inner products, adjoints, the finite spectral theorem, Rayleigh quotients, and finite functional calculus. **Next:** positive square roots and uniqueness.

<!-- BEGIN SPOKEN LECTURE -->

# What does it mean for a matrix to be positive?

For an ordinary number, positivity is straightforward. Three is positive, negative two is not, and zero sits at the boundary.

For a matrix, it cannot mean that all its entries are positive. A matrix can have negative entries and still be positive in the sense used in operator theory. Conversely, a matrix with all positive entries need not satisfy that operator-theoretic condition.

What we need is a definition that survives a change of orthonormal coordinates and tells us how the operator acts on *every direction*.

## A matrix as a measurement of energy

Take a real symmetric matrix A and a vector x. Form the number obtained by multiplying x by A and taking the inner product of x with the result. This number is called the quadratic form of A at x.

You have already met its normalized version: the Rayleigh quotient. Here we keep the length of x in the expression instead of dividing by it.

We call A *positive semidefinite* when its quadratic form is never negative, no matter which vector we choose. In the complex setting, we use self-adjoint operators and their real-valued quadratic forms.

Why require self-adjointness? Because we want an order on operators with the same geometric behavior as the order on real numbers. A general matrix can mix symmetric and skew effects, and the quadratic expression alone need not detect the skew part in the real case.

Consider the real ninety-degree rotation matrix: zero on the diagonal, negative one in the upper-right entry, and one in the lower-left. Its quadratic form is zero for every vector, because a vector is perpendicular to its ninety-degree rotation. Yet this matrix is not self-adjoint. So merely testing that its quadratic form is nonnegative would not give the right definition of a positive operator unless we also require self-adjointness.

## A matrix with negative entries can be positive

Look at the symmetric matrix with two on both diagonal entries and negative one in both off-diagonal positions.

Choose a vector with real coordinates x and y. Its quadratic form is two x squared, minus two x times y, plus two y squared.

Rewrite that as the square of x minus y, plus x squared, plus y squared. Each term is nonnegative. Therefore the entire expression is nonnegative for every vector. In fact, it is strictly positive for every nonzero vector.

So this matrix is positive definite, although two entries are negative.

Now take the diagonal matrix with entries negative one and two. Its entries are easy to inspect, but the important test is directional. On the first coordinate direction its quadratic form is negative one. That single vector proves it is not positive semidefinite.

There is an important lesson here: positivity is a claim about all vectors, not a visual pattern in a table of entries.

## The spectral criterion

We can test positivity using the finite spectral theorem.

Suppose A is self-adjoint, with an orthonormal basis of eigenvectors. Write a vector as a sum of components along those directions. Its quadratic form is the sum of each eigenvalue multiplied by the squared length of the corresponding component.

If every eigenvalue is nonnegative, each term in that sum is nonnegative. Therefore the operator is positive semidefinite.

Conversely, if an eigenvalue is negative, choose a unit eigenvector for it. Its quadratic form equals that negative eigenvalue. So the operator cannot be positive semidefinite.

We have proved a precise equivalence: a finite-dimensional self-adjoint operator is positive semidefinite if and only if all its eigenvalues are nonnegative.

And it is positive definite if and only if all its eigenvalues are strictly positive. In finite dimensions, that also means there is a fixed positive number c such that the quadratic form is at least c times the squared length of every vector. We can choose c to be the smallest eigenvalue.

The condition involving a *uniform* positive c becomes especially important in infinite dimensions, where positivity on every nonzero vector need not provide such a bound.

## Ordering two operators

Now we can compare matrices using an analogue of the usual number-line order.

For two self-adjoint operators A and B on the same space, say that A is less than or equal to B when B minus A is positive semidefinite.

Equivalently, for every vector x, the quadratic form of A at x is at most the quadratic form of B at x.

This is sometimes called the Loewner order, or quadratic-form order.

Notice that it is a *partial* order. Some pairs of operators cannot be compared in either direction.

For example, consider A with diagonal entries one and zero, and B with diagonal entries zero and one. On the first coordinate vector, A gives the larger quadratic form. On the second, B gives the larger one. Neither operator is below the other.

We should not expect every pair of self-adjoint matrices to line up like two real numbers.

## Order survives changes of coordinates and compression

There is a particularly useful rule. If A is less than or equal to B, and C is any linear map into their space, then C adjoint times A times C is less than or equal to C adjoint times B times C.

Let's prove it with one vector.

Choose any input vector y for C. The quadratic form of C adjoint A C at y is exactly the quadratic form of A at the vector C y. By our assumption, that is no greater than the quadratic form of B at C y. Rewrite this as the quadratic form of C adjoint B C at y. Since the inequality holds for every y, the operator inequality follows.

If C is unitary, this is simply a change of orthonormal coordinates. Positivity must survive because the geometry has not changed.

If C is an isometric embedding of a smaller coordinate space, we get the compression C adjoint A C. Positivity survives that operation too. This explains why a positive operator remains positive when we examine it on a trial subspace.

But be careful with the converse. An operator may look positive on one selected subspace while having a negative direction somewhere else. Testing a compression does not necessarily test the entire operator.

## Gram operators are automatically positive

We already constructed Gram operators from linear maps. For any linear map S between finite-dimensional inner-product spaces, its source Gram operator is S adjoint times S.

Evaluate its quadratic form at x. The result is the inner product of S x with itself: the squared norm of S x. Squared lengths are nonnegative. Therefore S adjoint S is positive semidefinite.

This is not merely an example. It is the reason the Gram construction can encode lengths, inner products, and singular values in a self-adjoint operator.

The kernel also has a simple interpretation. The quadratic form of S adjoint S vanishes at x exactly when S x is zero. So its zero directions are precisely the kernel of S.

Later we will prove a converse in finite dimensions: every positive semidefinite operator can be factored as S adjoint S. The finite spectral theorem and nonnegative square roots make that possible.

## Why products require care

It is tempting to say that the product of two positive operators is always positive, just as the product of two nonnegative numbers is nonnegative. That is false unless we impose additional structure.

Take the projection A onto the first coordinate axis. Take B to be the matrix with every entry equal to one. Both are positive semidefinite. But the product A B has first row one, one and second row zero, zero. It is not symmetric, so it is not a positive operator in our sense.

When positive operators commute, they can be diagonalized together in finite dimensions, and their product is again positive. Without commutation, even self-adjointness of the product can fail.

This is one reason the order theory of operators is richer than ordinary scalar arithmetic. We must prove the rules we use, not assume every scalar rule automatically transfers to matrices.

## Toward positive square roots

We have learned to detect positivity through quadratic forms and through eigenvalues. We have also learned how to apply functions to self-adjoint operators.

Combine those ideas. If A is positive, all its eigenvalues are nonnegative. We can take the ordinary nonnegative square root of each eigenvalue, then reassemble an operator using the same spectral projections.

The result will be positive, and squaring it will recover A.

But is it the *only* positive operator whose square is A? And can we characterize it without choosing coordinates? Those are the questions of the next lecture.

To test your understanding, explain why the quadratic form of a Gram operator is a squared length, why a negative eigenvalue rules out positivity, and why comparing A with B requires checking every vector. Then prove that compression preserves positivity using only the adjoint identity.

That reconstruction gives us the tools we will need for positive square roots, the operator modulus, and eventually polar decomposition.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematical facts and Lean correspondence (display only)

For finite-dimensional self-adjoint \(A,B\) on a real or complex inner-product space,

\[
A\succeq0\iff \langle Ax,x\rangle\ge0\quad\forall x
\iff \sigma(A)\subseteq[0,\infty),
\]

and \(A\preceq B\iff B-A\succeq0\). For any linear \(C:F\to E\),

\[
A\preceq B\implies C^*AC\preceq C^*BC.
\]

In particular \(S^*S\succeq0\), because \(\langle S^*Sx,x\rangle=\|Sx\|^2\). The strict condition \(\langle Ax,x\rangle>0\) for all \(x\ne0\) implies a uniform positive lower bound in finite dimensions; this implication must **not** be silently extended to all infinite-dimensional operators.

**Lean bridge.** A source-level representation of a two-block quadratic-form hypothesis occurs in `ForTauCeti/Analysis/InnerProductSpace/Spectral/Gap.lean`:

```lean
def TwoBlockFormGap (A : E →ₗ[𝕜] E) (U : Submodule 𝕜 E)
    (a b : ℝ) : Prop :=
  (∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜) ∧
    (∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2)
```

This is the quadratic-form version of an ordered spectral gap on the selected block and its perpendicular complement. `RCLike.re` extracts the real part so the order relation makes sense for real and complex scalars. The declared predicate packages inequalities; it does not itself prove that they follow from a spectrum hypothesis.

The companion `ForTauCeti/Analysis/InnerProductSpace/SpectralOrder.lean` has the following exact theorem signature (proof body omitted for display):

```lean
theorem lowerFormBoundOn_top_of_spectrum_subset_Ici
    (T : H →L[𝕜] H) (hT : IsSelfAdjoint T) {c : ℝ}
    (hσ : spectrum ℝ T ⊆ Set.Ici c) :
    T.LowerFormBoundOn ⊤ c := by
```

Here `Set.Ici c` denotes the closed set of numbers at least \(c\), `⊤` is the whole Hilbert space as a subspace, and `LowerFormBoundOn` records the lower quadratic-form inequality. This bridge connects the finite eigenvalue argument in the spoken lecture to a bounded Hilbert-space version that will receive its own analytic proof development later.

**Reconstruction:** Derive \(A\succeq0\iff\lambda_{\min}(A)\ge0\) from spectral expansion. Prove congruence preserves order. Give an explicit pair of positive semidefinite matrices whose product is not self-adjoint.

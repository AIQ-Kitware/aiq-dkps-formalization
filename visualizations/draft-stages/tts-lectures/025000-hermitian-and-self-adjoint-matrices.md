# Hermitian and self-adjoint matrices

<!-- BEGIN SPOKEN LECTURE -->

Two matrices can have eigenvalue two with algebraic multiplicity two, yet have different eigenspaces. The diagonal matrix with both diagonal entries two has a whole plane of eigenvectors. The matrix whose rows are two, one and zero, two has only the horizontal eigenvector line. A repeated eigenvalue alone does not guarantee enough eigenvectors to diagonalize a matrix.

Self-adjoint matrices cannot have that defect. Their eigenvalues are real, and eigenvectors associated with different eigenvalues are perpendicular. In finite dimensions they admit a complete orthonormal eigenbasis. The inner product explains these properties.

The class is called self-adjoint, or, when we are speaking specifically about matrices, Hermitian. Let's find out why the inner product is doing the work.

## What an adjoint does

Recall that the adjoint of an operator A is the unique operator A star for which the inner product of A x with y agrees with the inner product of x with A star y. We constructed adjoints using the Riesz representation theorem, so this is not just a formal rearrangement of symbols. It expresses a relationship between how A acts on one vector and how its adjoint acts on another.

In orthonormal coordinates over the real numbers, the adjoint matrix is the transpose. Rows and columns swap positions. Over the complex numbers, we must also conjugate the entries. The matrix of the adjoint is the conjugate transpose.

A matrix is self-adjoint when A equals A star. A real self-adjoint matrix is therefore symmetric across its main diagonal. A complex self-adjoint matrix is Hermitian: the entry below the diagonal must be the complex conjugate of the entry above it.

Why conjugate? A complex inner product already conjugates one of its arguments. The adjoint must respect that convention. If we used only the transpose for complex matrices, many of the geometric conclusions we want would fail.

Every diagonal entry of a Hermitian matrix is real, because a diagonal entry has to equal its own complex conjugate. But the off-diagonal entries can still be complex.

## Two small examples

First take the real two-by-two matrix whose first row is two, one, and whose second row is one, two. It is symmetric. Apply it to the vector with coordinates one, one. The result is three, three, so that vector has eigenvalue three. Apply it instead to one, negative one. The result is one, negative one, so that vector has eigenvalue one.

Notice two things. Both eigenvalues are real. And those two eigenvectors are perpendicular: their dot product is one minus one, which is zero.

Now take a genuinely complex example. Put two on both diagonal entries, put i in the upper-right corner, and negative i in the lower-left corner. Here i is the complex number whose square is negative one. This matrix is Hermitian because the lower-left entry is the conjugate of the upper-right entry.

Its vector with coordinates i, one is an eigenvector with eigenvalue three. You can verify this by multiplying. The first output is three i; the second is three. Its vector with coordinates negative i, one has eigenvalue one. These two vectors are orthogonal under the complex inner product, even though ordinary multiplication without conjugation would be misleading.

These examples illustrate the claims. Now let's prove the reasons.

## Why the eigenvalues must be real

Suppose A is self-adjoint, and a nonzero vector v satisfies A v equals lambda times v. We know lambda might initially be a complex number. We want to prove that it is real.

Look at the inner product of A v with v. Because A is self-adjoint, that number equals the inner product of v with A v. The two quantities are complex conjugates of each other, since swapping the arguments of an inner product conjugates its value. Therefore the inner product of A v with v equals its own conjugate. It is real.

But the eigenvector equation lets us evaluate the same number another way. It is lambda times the squared length of v, with the possible placement of the conjugation determined by which argument we chose to make linear. In the convention we are using, the coefficient appears as lambda in the inner product of A v with v.

The squared length of v is positive and real because v is not zero. If lambda times a positive real number is real, lambda itself must be real.

The proof is that short. The conclusion follows not from the size of the matrix or a characteristic-polynomial trick, but from how self-adjointness interacts with the inner product.

## Why different eigenspaces are perpendicular

Take two eigenvectors, v and w, with eigenvalues lambda and mu. Suppose the eigenvalues are different. We already know both numbers are real.

Compute the inner product of A v with w. The eigenvector equation says that this is lambda times the inner product of v with w.

Self-adjointness lets us move A to the other argument. The same expression becomes the inner product of v with A w. The second eigenvector equation makes this mu times the inner product of v with w.

So lambda times their inner product equals mu times their inner product. Subtract. The difference between lambda and mu, multiplied by their inner product, is zero.

Since the eigenvalues are different, that difference is nonzero. Therefore the inner product is zero. The eigenvectors are orthogonal.

This statement concerns *different* eigenvalues. Two arbitrary eigenvectors with the same eigenvalue need not be perpendicular. But within an eigenspace, we can use Gram–Schmidt to choose an orthonormal basis without changing the eigenvalue. Every linear combination of vectors in that eigenspace is still an eigenvector with that eigenvalue.

This is exactly what we need to combine different eigenspaces into one orthonormal collection.

## Why Jordan chains disappear

Consider the defective real matrix with first row two, one and second row zero, two. Let v be the horizontal unit vector and w the vertical unit vector. For eigenvalue lambda equal two, A minus lambda times the identity sends w to v and sends v to zero. Thus v is an eigenvector and w is a generalized eigenvector, forming a length-two Jordan chain.

Could such a chain exist for a self-adjoint matrix? No. Here is a short argument.

Write B for A minus lambda times the identity. Since lambda is real and A is self-adjoint, B is self-adjoint too. Assume B v equals zero and B w equals v.

Take the inner product of B w with v. Because B w equals v, this is the squared length of v, which is positive.

But self-adjointness lets us move B onto v. The same inner product is the inner product of w with B v. And B v is zero. So the result is zero.

That is a contradiction. The same number cannot be both positive and zero. Therefore the defective chain cannot exist.

This does not yet prove the entire spectral theorem, but it removes the phenomenon that made the previous example fail.

## A caution about the word symmetric

There are several meanings of symmetric in operator theory. For a finite-dimensional real matrix, being symmetric means being self-adjoint. For complex matrices, we say Hermitian or self-adjoint and use conjugate transpose.

Later, when we study unbounded operators on Hilbert spaces, we must distinguish a symmetric operator from a self-adjoint one. There, the domain on which an operator is defined matters, and symmetry alone may not give equality with the adjoint. That is a real mathematical distinction, not a terminological preference. We will develop it when we have the necessary domain theory.

For today's finite-dimensional matrices, no such domain difficulty arises. Every matrix acts on the entire coordinate space.

## What this gives us, and what remains

We have proved three important facts. A Hermitian matrix has real eigenvalues. Eigenvectors with distinct eigenvalues are orthogonal. And a nontrivial Jordan chain attached to an eigenvalue is impossible.

What have we *not* proved? We have not yet shown that there are enough eigenvectors to span the entire space. That is the missing step between these structural facts and a complete spectral decomposition.

Three useful reconstructions are these. Show why the conjugate transpose, not the plain transpose, is the complex adjoint. Reproduce the proof that distinct eigenspaces are perpendicular. And explain exactly where the attempted Jordan chain contradicts self-adjointness.

These facts provide the ingredients for the finite spectral theorem: a self-adjoint matrix admits an orthonormal eigenbasis, so the operator is reconstructed from its eigenvalues and orthogonal spectral projections.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematical facts and Lean correspondence (display only)

For a matrix over \(\mathbb C\), Hermitian means \(A=A^*\), where \(A^*=\overline A^{\mathsf T}\). If \(Av=\lambda v\) with \(v\ne0\), then
\[
\langle Av,v\rangle=\lambda\|v\|^2\in\mathbb R
\quad\Longrightarrow\quad\lambda\in\mathbb R.
\]
If \(Av=\lambda v\) and \(Aw=\mu w\), with \(\lambda\ne\mu\), then \((\lambda-\mu)\langle v,w\rangle=0\). The nonzero Jordan-chain contradiction is \(\|v\|^2=\langle (A-\lambda I)w,v\rangle=\langle w,(A-\lambda I)v\rangle=0\).

**Lean bridge.** The project uses both `Matrix.IsHermitian` for finite matrices and `IsSelfAdjoint` for bounded or domain-aware operators. This is an exact excerpt from `ForTauCeti/Analysis/InnerProductSpace/CompactApproximationEigenvalues.lean`:

```lean
theorem eq_ofReal_re_of_eigenspace_ne_bot (hAs : IsSelfAdjoint A)
    (hApos : ∀ x, 0 ≤ RCLike.re ⟪A x, x⟫_𝕜) {μ : 𝕜}
    (h : eigenspace A.toLinearMap μ ≠ ⊥) :
    μ = ((RCLike.re μ : ℝ) : 𝕜) ∧ 0 ≤ RCLike.re μ := by
```

The theorem's conclusion says an eigenvalue of a **positive** self-adjoint operator is real and nonnegative. `hAs` encodes self-adjointness; `hApos` supplies positivity; `eigenspace ... ≠ ⊥` asserts a nonzero eigenspace. The displayed source continues by using `conj_eigenvalue_eq_self` for reality and a separate positivity argument for nonnegativity. This is stronger than the reality fact taught today, and its nonnegativity portion will be developed in the positive-operator unit. The excerpt is an exact declaration prefix, not a standalone proof. The mathematical result belongs to the DKPS development regardless of later upstream location.

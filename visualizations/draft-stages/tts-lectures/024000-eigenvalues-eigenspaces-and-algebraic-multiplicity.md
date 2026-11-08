# Eigenvalues, eigenspaces, and algebraic multiplicity

<!-- BEGIN SPOKEN LECTURE -->

An eigenvalue of a square linear map A is a scalar lambda for which there is a nonzero vector v satisfying A v equals lambda v. For diagonal or symmetric matrices, eigenvectors can give useful coordinates. A rectangular map instead produces two positive Gram operators whose nonzero eigenvalues are squared singular values. The goal here is to distinguish the eigenspace dimension from the multiplicity of a root of the characteristic polynomial.

Here is the issue. Two matrices can have exactly the same eigenvalues, with exactly the same repetition in their characteristic polynomials, while having very different collections of eigenvectors. One can have a full basis of eigenvectors. The other can have too few.

Why? To answer, we need to distinguish an eigenvalue, its eigenspace, its algebraic multiplicity, and its geometric multiplicity. That distinction will make the finite spectral theorem much easier to understand when we reach it.

## The eigenvector equation

Let A be a linear operator on a finite-dimensional vector space. Unlike a map between two different vector spaces, A goes from the space back to itself.

A nonzero vector v is an eigenvector with eigenvalue lambda when A of v equals lambda times v. The number lambda is an eigenvalue, and the equation says something geometric: A sends the line through v into itself. It may stretch it, shrink it, reverse its direction, or annihilate it if lambda is zero.

Why insist that v be nonzero? Because the zero vector satisfies A of zero equals lambda times zero for every lambda. If we allowed it as an eigenvector, the definition would convey no information at all.

Once lambda is fixed, all vectors satisfying the eigenvector equation form a subspace. This is the eigenspace for lambda. In symbols, it is the kernel of A minus lambda times the identity.

A kernel is closed under adding vectors and multiplying by scalars. So if two independent vectors share an eigenvalue, every linear combination of them shares that eigenvalue too. That eigenspace can have dimension greater than one.

## From the kernel to a determinant

In finite dimensions, choose a basis and write A as a square matrix. We can restate the eigenvector equation: A minus lambda times the identity sends some nonzero vector to zero.

A square matrix has a nonzero vector in its kernel exactly when it is not invertible. And a square matrix is not invertible exactly when its determinant is zero.

Thus lambda is an eigenvalue exactly when the determinant of A minus lambda times the identity is zero. Equivalently, it is a root of the characteristic polynomial, often written as the determinant of t times the identity minus A.

Those two determinant conventions have the same roots. They may differ by an overall sign depending on the dimension. When we speak of the characteristic polynomial, we will use the convention with t times the identity minus A, which gives a monic polynomial.

The characteristic polynomial does not depend on which basis we choose. If we change coordinates by an invertible matrix S, the new matrix is S inverse times A times S. The determinant of t times the identity minus that new matrix equals the old determinant, because the outer S and S inverse factors cancel inside the determinant.

That is an important point. The matrix entries change with a basis. The characteristic polynomial does not. It describes the operator rather than a particular coordinate chart.

## One eigenvalue can occur more than once

Let's start with the simplest repeated eigenvalue. Take the two-by-two matrix that multiplies every vector by two. Its matrix is two times the identity. Every nonzero vector is an eigenvector with eigenvalue two.

The characteristic polynomial is t minus two, squared. So the eigenvalue two is a repeated root, occurring twice. We call that repetition its algebraic multiplicity: two.

Its eigenspace is the entire two-dimensional plane. We call the dimension of the eigenspace its geometric multiplicity: also two.

So here the two multiplicities agree. The matrix has two independent eigenvectors, indeed infinitely many choices of eigenvector basis. We can diagonalize it using any basis we like.

Now I want to change just one entry of the matrix. Keep the two diagonal entries equal to two, but put a one in the upper-right corner. Leave the lower-left entry zero. In row form, our matrix is two, one on the first row, and zero, two on the second.

The characteristic polynomial is still t minus two, squared, because this is an upper triangular matrix. Its determinant after subtracting t along the diagonal is the product of the two diagonal factors. Algebraic multiplicity is still two.

But solve the eigenvector equation. Subtract two times the identity, and the remaining matrix sends a vector with coordinates x and y to the vector with coordinates y and zero. To land in the kernel, y must be zero. The first coordinate x can be anything.

Therefore the eigenspace consists only of horizontal vectors. Its geometric multiplicity is one.

Same eigenvalue. Same characteristic polynomial. Different number of independent eigenvectors.

## What the missing direction does

Consider the vertical unit vector under our second matrix. The operator sends it to the vertical vector multiplied by two, plus a horizontal vector. So the vertical direction is not an eigenvector. It leaks into the horizontal direction.

There is a useful way to describe that leakage. Subtract two times the identity, and call the resulting operator N. It sends the vertical unit vector to the horizontal unit vector, and sends the horizontal unit vector to zero.

Apply N twice to any vector and you get zero. So N is not zero, but N squared is zero. Such an operator is called nilpotent.

The vertical unit vector is an example of a generalized eigenvector for eigenvalue two. It is not killed by A minus two times the identity in one step, but it is killed after two steps. Together with the horizontal eigenvector, it forms what is called a Jordan chain.

We will not need the full Jordan normal form today. The point is that the repeated root of the characteristic polynomial can represent either several honest eigenvector directions or a more entangled action with generalized eigenvectors.

Our two examples make that distinction visible without any new machinery.

## Geometric multiplicity cannot exceed algebraic multiplicity

There is a general inequality here, and we can prove it with a smart choice of basis.

Fix an eigenvalue lambda whose eigenspace has dimension k. Choose a basis of that eigenspace and extend it to a basis of the entire space.

Because each of the first k basis vectors is an eigenvector, the first k columns of A have lambda in the corresponding diagonal position and zeros everywhere else. In this basis, A has an upper block-triangular shape. Its upper-left block is lambda times a k-by-k identity matrix, and its lower-left block is zero.

When we form t times the identity minus A and take its determinant, the determinant of a block-triangular matrix is the product of the determinants of its diagonal blocks. One factor is therefore t minus lambda, raised to the k-th power.

That means the characteristic polynomial has lambda as a root at least k times. So geometric multiplicity, which is k, can never exceed algebraic multiplicity.

The first of our two-by-two examples has equality. The second has strict inequality.

This proof is worth remembering. It turns the geometry of the eigenspace into a factor of the characteristic polynomial by choosing coordinates adapted to an invariant subspace.

## What diagonalization asks for

A matrix is diagonalizable when there is a basis made entirely of eigenvectors. In that basis, the matrix is diagonal: each basis vector is merely scaled.

Having eigenvalues is not enough. Having the right total number of roots counted with algebraic multiplicity is not enough either. We need enough *independent eigenvectors* to fill the space.

For the second two-by-two matrix, every genuine eigenvector lies on the horizontal axis. No collection of them can form a basis for the plane. So the matrix cannot be diagonalized.

Why do we care? Because a diagonal operator is much easier to understand. Its powers, exponentials, and many functions act separately on the eigenvector coordinates. If we can diagonalize an operator, we can often reduce a complicated equation to independent scalar calculations.

Their eigenspaces at distinct eigenvalues are orthogonal, and they admit an orthonormal eigenbasis. That is a theorem we will prove, not an assumption about every matrix.

## Real matrices may need complex scalars

There is one last qualification. A real matrix can have no real eigenvectors even though it has complex eigenvalues. For example, the real quarter-turn rotation has no real eigenvectors: it rotates every nonzero real vector by ninety degrees, so no real line is preserved. Over the complex numbers, however, it has two eigenvalues, i and negative i.

Over the complex numbers, every nonconstant polynomial has a root. Therefore every finite-dimensional complex matrix has at least one eigenvalue. Over the real numbers, that statement fails, as the quarter-turn example shows.

This is part of why spectral theory often uses complex scalars even when the motivating problem is real. We will keep track of which field we are working over rather than silently moving between them.

## What to take forward

Here is the hierarchy. An eigenvalue is a scalar for which A minus lambda I has a nonzero kernel. The eigenspace is that kernel. Geometric multiplicity counts independent eigenvectors for lambda. Algebraic multiplicity counts the root's repetition in the characteristic polynomial. The latter can be larger than the former, because a general matrix may contain nontrivial Jordan chains.

Try to reconstruct both two-by-two examples without notes. Compute their characteristic polynomials. Compute their eigenspaces. Explain why they have equal algebraic multiplicities but different geometric multiplicities. Then reproduce the block-triangular argument showing that geometric multiplicity cannot exceed algebraic multiplicity.

Their additional inner-product structure will rule out the kind of defect we just saw and set the stage for a spectral decomposition into orthogonal subspaces.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematical facts and Lean correspondence (display only)

For \(A:\mathbb K^n\to\mathbb K^n\), \(\lambda\) is an eigenvalue iff \(\ker(A-\lambda I)\ne\{0\}\), equivalently \(\det(\lambda I-A)=0\). The algebraic multiplicity of \(\lambda\) is its multiplicity as a root of \(\chi_A(t)=\det(tI-A)\); its geometric multiplicity is \(\dim\ker(A-\lambda I)\). An adapted basis gives \(\chi_A(t)=(t-\lambda)^k q(t)\) where \(k\) is geometric multiplicity, hence \(k\) does not exceed algebraic multiplicity.

For example, \(A=\begin{pmatrix}2&1\\0&2\end{pmatrix}\) has \(\chi_A(t)=(t-2)^2\), but \(\ker(A-2I)=\operatorname{span}\{(1,0)\}\). The generalized vector \((0,1)\) satisfies \((A-2I)^2(0,1)=0\) but \((A-2I)(0,1)\ne0\).

**Lean bridge.** A later DKPS theorem uses Mathlib's characteristic-polynomial API to compare the polynomial under an equivalence of coordinate order. The following is an exact excerpt from `DavisKahan/FiniteDimensional/DirectRotation/RealFourSpectrum.lean`:

```lean
theorem charpoly_fourTransport (t u a b e f : ℝ) :
    (fourTransport ![t, u] a b e f).charpoly =
      (fourTransportMatrix t u a b e f).charpoly := by
  rw [← fourTransportMatrix_submatrix]
  exact Matrix.charpoly_reindex finSumFinEquiv.symm _
```

`Matrix.charpoly` is the characteristic polynomial of a square matrix. `Matrix.charpoly_reindex` expresses its invariance under reindexing rows and columns by the same equivalence. The displayed theorem concerns a later four-dimensional rotation construction; the present lecture teaches the linear-algebra principle that makes such a step valid. `finSumFinEquiv` reorganizes two pairs of coordinates into four coordinates. This is not offered as a Lean proof of the general geometric/algebraic multiplicity inequality; that theorem's companion will be identified when its exact source declaration is audited. The excerpt was verified against the supplied source snapshot; no new Lean code was compiled.

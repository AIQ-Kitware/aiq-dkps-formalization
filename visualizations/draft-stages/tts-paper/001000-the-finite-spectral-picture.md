# 001000 — The finite spectral picture

**Track:** G3 audio paper track. **Draft:** adapted from G2 lecture 026000. **Section:** foundation. **Audience:** prior linear algebra and basic analysis.

<!-- BEGIN SPOKEN LECTURE -->

A finite-dimensional self-adjoint matrix has real eigenvalues, and eigenvectors belonging to different eigenvalues are orthogonal. But are there enough eigenvectors to span the entire space? The finite spectral theorem answers yes, and its proof constructs an orthonormal eigenbasis.

Today we answer yes. We will prove the finite-dimensional spectral theorem. And then we will take an additional step: instead of describing an operator with a particular collection of eigenvectors, we will describe it using projections onto entire eigenspaces.

That second description will matter later. Choosing an eigenvector can be arbitrary when an eigenvalue repeats. Choosing its whole eigenspace is not.

## First, what would a spectral decomposition accomplish?

Imagine a room in which a transformation stretches one direction by three and a perpendicular direction by one. If you express a vector in those directions, the transformation is easy: multiply the first coordinate by three and leave the second alone.

An arbitrary matrix may mix coordinates. A self-adjoint matrix, we hope, has some orthonormal coordinates in which it stops mixing them.

An orthonormal basis of eigenvectors would do exactly that. Every vector x could be written as a sum of components along eigenvectors. The operator would act on each component by multiplying by that component's eigenvalue. Adding those scaled components would recover A x.

That is the spectral theorem in its most useful finite-dimensional form. Let's prove the existence of the basis rather than assuming it.

## Finding one eigenvector

We'll work first over the complex numbers. Let A be a self-adjoint operator on a nonzero finite-dimensional complex inner-product space.

The characteristic polynomial has positive degree. The fundamental theorem of algebra says that it has at least one complex root. If lambda is a root of the characteristic polynomial of a finite matrix A, then A minus lambda times the identity is singular. Its kernel therefore contains a nonzero eigenvector. So choose an eigenvalue lambda and a unit eigenvector v.

Since A is self-adjoint, lambda is real. This matters because the restriction of A to the directions perpendicular to v will remain self-adjoint.

We know one good direction. How can we find the rest without interfering with it?

## The perpendicular complement stays closed under A

Consider the subspace of all vectors perpendicular to v. Take any vector w in that subspace. Its inner product with v is zero.

We want to show that A w is also perpendicular to v. Move A across the inner product using self-adjointness. The inner product of A w with v equals the inner product of w with A v. Because v is an eigenvector, A v is lambda times v. The result is therefore lambda times the inner product of w with v, which is zero.

So A sends every vector perpendicular to v back into the same perpendicular subspace.

This is the reducing-subspace idea, now doing concrete proof work. We have split the space into the line along v and its orthogonal complement. And A respects both pieces.

The orthogonal complement has dimension one less than the original space. The restriction of A to that complement is still self-adjoint, because its inner products are computed using the same rule as before.

We have therefore reduced our problem to a smaller problem of the same kind.

## Induction gives an orthonormal eigenbasis

In a one-dimensional space, the theorem is immediate. Every linear operator is multiplication by one scalar in the sole unit direction, and self-adjointness makes that scalar real.

Assume the theorem works in dimension one less than our current space. We already chose one unit eigenvector v, and we just proved that its perpendicular complement is invariant and carries a self-adjoint restriction.

By the inductive hypothesis, the complement has an orthonormal eigenbasis for that restriction. Put v together with that basis. Because every vector in the complement is perpendicular to v, the combined list is orthonormal. Because the line along v and its complement fill the space, the list is a basis. And every vector on the list is an eigenvector of A.

We have proved the theorem for the next dimension, and therefore for every finite dimension.

The proof proceeds by induction: existence of an eigenvalue gives an eigenvector; self-adjointness makes its perpendicular complement invariant; and the argument repeats in smaller dimension. This is why self-adjointness gives more than merely real eigenvalues: it permits the reduction that makes the induction work.

## What about real symmetric matrices?

We used the fundamental theorem of algebra over the complex numbers, but a real symmetric matrix should have a real orthonormal eigenbasis too.

View a real symmetric matrix as a complex Hermitian matrix. The complex proof gives an eigenvalue. Because a Hermitian operator satisfies the identity that the inner product of A v with v is real, any eigenvalue at a nonzero eigenvector must be real.

Write a corresponding complex eigenvector as its real part plus i times its imaginary part. Because the matrix and eigenvalue are real, comparing real and imaginary parts shows that each part separately satisfies the same eigenvector equation. At least one part is nonzero, since the complex eigenvector is nonzero.

Thus a real symmetric matrix has a nonzero real eigenvector. Repeat the perpendicular-complement induction entirely over the real numbers. That proves the real theorem without secretly treating complex vectors as a real orthonormal basis.

## From eigenvectors to projections

Let's make the result independent of a particular choice of basis.

For each *distinct* eigenvalue lambda, gather all eigenvectors with that eigenvalue, along with zero, into its eigenspace. Let P lambda mean orthogonal projection onto that eigenspace.

Distinct eigenspaces are orthogonal: self-adjointness equates lambda times the inner product of two eigenvectors with mu times that inner product, forcing it to vanish when lambda and mu differ. Their direct sum is the entire space, by the spectral theorem we just proved.

That gives three properties. First, each P lambda is an orthogonal projection, so applying it twice is the same as applying it once. Second, projections for distinct eigenvalues annihilate one another: a vector lying in one eigenspace has no component in a different one. Third, adding all these spectral projections gives the identity operator, because every vector is the sum of its spectral components.

The operator A itself is the sum of lambda times P lambda over the distinct eigenvalues. To see why, apply both sides to an arbitrary vector. Every projection extracts one eigenspace component, and multiplying it by lambda is exactly how A acts on that component.

That is the spectral decomposition.

## A two-dimensional calculation

Let's use our real symmetric example: the matrix with rows two, one and one, two.

The line along the vector one, one has eigenvalue three. The line along one, negative one has eigenvalue one. Normalize each vector by dividing by the square root of two.

Projection onto the first line takes a vector, measures its component along that normalized direction, and returns exactly that component. Its matrix has one half in every entry.

Projection onto the second line has one half on the diagonal and negative one half off the diagonal.

Add the two projection matrices. Their off-diagonal entries cancel and the diagonal entries add to one. We get the identity.

Now multiply the first projection by three and add the second projection once. The diagonal entries become two; the off-diagonal entries become one. We recover the original matrix exactly.

There is no approximation here. The projections split the operator into separate pieces, each carrying one eigenvalue.

## What happens when an eigenvalue repeats?

Suppose an eigenvalue occurs twice. Its eigenspace may be a plane. We could choose one pair of perpendicular unit vectors in that plane, or rotate that pair and choose another. Both give valid eigenbases.

But the plane itself has not changed. Its orthogonal projection has not changed either.

This is why it is often more informative to speak of a spectral subspace and its projection than to insist on a particular eigenvector. The projection records the whole component associated with the eigenvalue, without making an arbitrary coordinate choice inside it.

For any selected cluster of eigenvalues, the projection onto the sum of their eigenspaces captures the geometry of the cluster.

## What the theorem does not say

Today's theorem is finite-dimensional and assumes self-adjointness. General matrices may fail to have a basis of eigenvectors. General bounded self-adjoint operators on infinite-dimensional spaces need not have an eigenbasis either, because the spectrum may contain values that are not eigenvalues.

We will eventually replace finite sums over eigenvalues by integration with respect to projection-valued measures. That is not a minor change of notation; it requires new mathematics, which we will build later.

For now, the finite theorem is a complete result in its setting.

## Reconstructing the theorem

Try to reproduce the induction without looking back. Where does the first eigenvector come from? Why does the perpendicular complement stay invariant? What makes the restricted operator self-adjoint? And how do we know the pieces span the original space?

Then reconstruct the two-by-two example from its two spectral projections. Explain why changing the eigenbasis within a repeated eigenspace does not change its projection.

That question leads to Rayleigh quotients, and eventually to the variational theory of eigenvalues.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematical facts and Lean correspondence (display only)

For a finite-dimensional real or complex inner-product space and self-adjoint \(A\), there is an orthonormal eigenbasis. Let \(\Lambda\) be the set of **distinct** eigenvalues and \(P_\lambda\) the orthogonal projector onto the corresponding eigenspace. Then
\[
P_\lambda^*=P_\lambda=P_\lambda^2,\quad
P_\lambda P_\mu=0\ (\lambda\neq\mu),\quad
\sum_{\lambda\in\Lambda}P_\lambda=I,\quad
A=\sum_{\lambda\in\Lambda}\lambda P_\lambda.
\]

**Lean bridge.** The DKPS-developed `ForTauCeti/LinearAlgebra/Matrix/PosDef.lean` proves an entrywise form of `Matrix.IsHermitian.spectral_theorem`:

```lean
theorem isHermitian_entry_eq_sum_eigenvalues
    (B : Matrix (Fin n) (Fin n) 𝕜) (hB : B.IsHermitian) (i j : Fin n) :
    B i j = ∑ k : Fin n,
      (hB.eigenvalues k : 𝕜) * (hB.eigenvectorUnitary i k) *
        conj (hB.eigenvectorUnitary j k) := by
  have hspec := hB.spectral_theorem
```

`hB` is the Hermitian hypothesis; `eigenvectorUnitary` supplies orthonormal eigenvector coordinates and `eigenvalues` lists eigenvalues **with multiplicity**, unlike the distinct-eigenvalue indexing of the projector formula above. The sum is the entrywise expansion of \(B=UDU^*\). The source then expands this matrix product into the displayed sum. Our spoken proof constructs the basis inductively; the Lean development reuses Mathlib's spectral theorem and proves a useful representation of its conclusion. The quoted lines are an exact source prefix, not a new independent Lean proof.

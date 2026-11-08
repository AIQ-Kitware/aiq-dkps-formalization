# The projection theorem

<!-- BEGIN SPOKEN LECTURE -->

Suppose you stand above a flat floor and want the point on the floor closest to you. You drop a perpendicular. The nearest point is where that perpendicular meets the floor.

In a Hilbert space, our floor may be an infinite-dimensional subspace, and a vector might be a function or an infinite sequence. We can still ask for the closest point in that subspace. Today we will prove that it exists when the subspace is closed, prove that it is unique, and discover that nearest-point approximation and orthogonality are two descriptions of exactly the same thing.

This is the projection theorem. We will not treat the result as obvious from the picture, because a picture cannot prove that an infinite-dimensional minimizer exists.

## A small example first

In the ordinary plane, let M be the horizontal axis. If x has horizontal coordinate three and vertical coordinate four, the closest point in M is the point with horizontal coordinate three and vertical coordinate zero.

Why? Any other point on the axis differs from x by a horizontal displacement as well as the unavoidable vertical displacement of four. Pythagoras says that its squared distance is sixteen plus a nonnegative horizontal square. The smallest value occurs when that extra term is zero.

The leftover vector, from the closest point to x, is vertical. It is perpendicular to the whole horizontal axis. This is not a coincidence. It is the essential optimality condition.

## Why the word closed matters

Before we prove the theorem, remember the finitely supported sequences inside ell two. This is a subspace, but it is not closed. Take the vector whose coordinates are one, one half, one third, and so on. It lies in ell two but not in that subspace.

By keeping longer and longer initial segments, we can find finitely supported vectors arbitrarily close to it. So the greatest lower bound on its distance to the subspace is zero. But there is no finitely supported vector at distance zero from it, because that would have to be the vector itself.

In other words, the best possible error exists as a number, but no allowed approximant attains that error. This is why our theorem needs a closed subspace. A geometric drawing of a line or plane can hide the issue, because finite-dimensional subspaces are automatically closed.

## Finding a candidate without guessing it

Let H be a Hilbert space and M a closed linear subspace. Choose any vector x in H. We want to minimize the distance from x to points in M.

Call the infimum of these distances d. We use infimum rather than minimum because we have not yet proved that an actual closest point exists. Because distances are nonnegative and M contains zero, d is a finite nonnegative number.

By the definition of infimum, we can choose a sequence of points in M whose distances to x approach d. Call the points p one, p two, and so on. They are increasingly good approximations. But being good approximations does not automatically mean the points themselves converge. We must establish that.

Here the parallelogram identity from the inner-product lecture becomes decisive.

Take two of our approximants, p and q. Look at the vectors from each approximant toward x. Their difference is q minus p. Their average is the vector from the midpoint of p and q toward x.

The parallelogram identity tells us that the squared distance between p and q equals twice the squared distance from p to x, plus twice the squared distance from q to x, minus four times the squared distance from their midpoint to x.

Because M is a linear subspace, the midpoint of p and q still belongs to M. Its distance to x is therefore at least d. Substitute that lower bound into the identity.

We learn that the squared distance between p and q is no greater than twice the squared distance from p to x, plus twice the squared distance from q to x, minus four times d squared.

Now let p and q come from sufficiently late positions in our minimizing sequence. Each of their squared distances to x approaches d squared. The right-hand side approaches zero. So the distance between any two late approximants approaches zero. The minimizing sequence is Cauchy.

Completeness of H now supplies a limit point p. Since M is closed and every approximant lies in M, their limit also lies in M. Continuity of the norm says that the distance from x to p is exactly d. We have constructed a nearest point.

Notice the roles of the ingredients. The parallelogram identity made the approximants Cauchy. Hilbert-space completeness provided a limit. Closedness of M kept that limit inside the permitted subspace. Closedness cannot be dropped. For example, the finitely supported sequences form a dense, nonclosed subspace of ell two. A square-summable sequence with infinitely many nonzero coordinates has distance zero to that subspace but has no nearest point within it.

## Why the nearest point is unique

Suppose both p and q were nearest points. Their distances to x would both equal d. Apply the same parallelogram identity. The midpoint belongs to M and cannot be closer than d. Therefore the squared distance between p and q is at most zero. Since squared distances are nonnegative, p and q must be equal.

So the closest point is not merely guaranteed to exist. It is uniquely determined by x.

This matters because it lets us define a function: send each x to its unique closest point in M. We call that function the orthogonal projection onto M.

## Why nearest-point error is perpendicular

Let p be the nearest point, and let r be the error vector x minus p. We claim r is perpendicular to every vector v in M.

Imagine moving the candidate point p a little in the direction v. Since M is a subspace, p plus any scalar multiple of v is still in M. The closest-point property says that none of those moves can decrease the distance to x.

If v is nonzero, use the scalar that would remove the component of r along v. In the real case, it is the inner product of v with r divided by the squared length of v. In the complex case, use exactly the same expression with the complex inner product linear in its second argument.

By expanding the squared distance after that move, we find the original squared error minus the squared magnitude of the inner product of v with r, divided by the squared length of v. If the inner product were nonzero, this move would give a strictly smaller error. That contradicts nearest-point optimality.

Therefore the inner product must be zero. The error r belongs to the orthogonal complement of M.

Now prove the reverse direction. Suppose p belongs to M and x minus p is perpendicular to M. For any other point q in M, write x minus q as x minus p plus p minus q. The first part is perpendicular to the second, because p minus q lies in M. Pythagoras says the squared distance to q is the squared distance to p plus the squared norm of p minus q. It cannot be smaller. Thus p is the unique nearest point.

We have proved an equivalence: a point in a closed subspace is the closest point to x exactly when the residual from that point to x is perpendicular to the subspace.

## The operator hidden in the geometry

Call the projection operator P. Every vector x now has a unique decomposition: x equals P of x, which lies in M, plus x minus P of x, which lies in M perp.

This decomposition lets us prove P is linear. Take two vectors and decompose each into its M part and perpendicular part. Add the decompositions. The sum of the M parts remains in M, and the sum of the perpendicular parts remains in M perp. By uniqueness of the decomposition, the M part of the sum is the sum of their projections. The same reasoning works for scalar multiplication, including complex scalars.

Pythagoras gives another important fact. The squared norm of x is the squared norm of P of x plus the squared norm of the perpendicular remainder. Therefore P of x can never be longer than x. The projection is bounded, with operator norm at most one.

If x already lies in M, its nearest point is itself. Projecting twice changes nothing. This is the idempotence identity: P composed with P equals P.

And the complementary piece, x minus P of x, is exactly the orthogonal projection onto M perp. Every vector belongs to the sum of M and M perp, and that sum is orthogonal.

We can now close a loop. Take the orthogonal complement of M perp. Because every vector splits into an M part and an M-perp part, a vector perpendicular to M perp must have zero M-perp component. It therefore belongs to M. Thus, for a closed subspace, taking the orthogonal complement twice returns the subspace. For any possibly nonclosed subspace, it returns the closure.

## Reconstructing the proof

Reconstruct the argument in four steps.

First, choose a sequence whose errors approach the best possible error. Second, use the parallelogram identity and the midpoint to prove that sequence is Cauchy. Third, apply completeness and closedness to get an actual nearest point. Fourth, vary that point along directions in the subspace to prove its residual is perpendicular.

The final consequences—linearity, boundedness, and projection squared equals projection—follow from that geometry.

<!-- END SPOKEN LECTURE -->

---

## Companion: symbolic facts and Lean correspondence (display only)

For a closed subspace \(M\le H\), every \(x\in H\) has a unique decomposition
\[
x=p+r,\qquad p\in M,\quad r\in M^\perp,
\]
with \(\|x-p\|=\inf_{m\in M}\|x-m\|\). The projection \(P_Mx=p\) satisfies
\[
P_M^2=P_M,\quad \mathrm{ran}(P_M)=M,\quad \ker(P_M)=M^\perp,
\quad \|P_Mx\|\le\|x\|.
\]
For two candidate approximants \(p,q\in M\), the minimizer Cauchy estimate is
\[
\|p-q\|^2
=2\|x-p\|^2+2\|x-q\|^2
-4\left\|x-\frac{p+q}{2}\right\|^2.
\]

**Lean bridge.** The existing lecture companion `visualizations/lectures/001000_projections/facts.lean` uses the actual Mathlib/TauCeti orthogonal projection interfaces:

```lean
variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
variable (K : Submodule ℝ E) [K.HasOrthogonalProjection]

example (x : E) :
    K.starProjection x +
      Kᗮ.starProjection x = x :=
  K.starProjection_add_starProjection_orthogonal x
```

`K` is the chosen subspace; `Kᗮ` is its orthogonal complement; `K.starProjection` is the ambient orthogonal projection, and `HasOrthogonalProjection` supplies the existence of an orthogonal decomposition. The original example uses real scalars; the geometry also holds for complex Hilbert spaces.

The local DKPS contribution `ForTauCeti/Analysis/InnerProductSpace/Projection/Blocks.lean` contains this companion identity:

```lean
@[simp]
theorem starProjection_orthogonal_apply (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (x : E) :
    Uᗮ.starProjection x = x - U.starProjection x := by
  rw [Submodule.starProjection_orthogonal]
  simp
```

This is exactly the residual formula from the narration. Here `𝕜` is an `RCLike` scalar field and `E` has an inner product. The module's own provenance comments record that some underlying projection-block infrastructure was developed in DKPS and upstreamed to TauCeti. These snippets were verified in the supplied source snapshot; no new Lean compilation was performed.

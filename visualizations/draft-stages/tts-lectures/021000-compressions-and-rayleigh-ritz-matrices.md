# Compressions and Rayleigh–Ritz matrices

<!-- BEGIN SPOKEN LECTURE -->

Let V be an isometric embedding from a coefficient Hilbert space into an ambient Hilbert space. The adjoint V star measures the coordinates along the selected subspace. We have V star V equal to the coefficient identity, while V V star is the orthogonal projection onto the closed range of V. These identities let us compress an ambient operator to the smaller coordinate space.

Today we will put a third operator between those two maps. Given an operator A on ambient space, we will study V star A V.

This construction is called compression. It turns a large operator into a smaller one that describes how A looks from inside our selected subspace. It is the basis of the Rayleigh–Ritz method, a standard route to approximate eigenvalues and eigenvectors.

But we need to be precise about the word approximate. The compressed operator does not necessarily contain an exact piece of the original operator. It can forget an important part of what A does.

## Start with a line in the plane

Take the plane and let A act by stretching the horizontal direction by a factor of one and the vertical direction by a factor of three. Its matrix in the standard basis has one and three on the diagonal and zero elsewhere.

We know exactly what this operator does to the horizontal and vertical unit vectors. They remain in their own directions, so those directions are eigenvectors, with eigenvalues one and three.

Now suppose we decide to examine only the diagonal line, the line where both coordinates are equal. Choose its unit vector v. Each coordinate of v is one over the square root of two.

Our coefficient space is one-dimensional. The embedding V takes a number c and produces c times v. Its adjoint measures how much an ambient vector points along v.

What happens if we start with a coefficient c, embed it, apply A, and then measure along v again?

The answer is two times c. So the compressed operator V star A V is multiplication by two.

That makes intuitive sense. The diagonal line samples the direction with stretch one and the direction with stretch three equally. From the viewpoint of this selected line, the average quadratic stretch is two.

But notice the tension: two is not an eigenvalue of our original matrix. Its eigenvalues are one and three.

Compression has produced a perfectly well-defined number that is not an exact ambient eigenvalue. That is not a mistake. It is telling us something different.

## What the compression actually measures

Call the compressed operator B. We define B as V star A V.

For any coefficient vector c, the inner product of c with B of c equals the inner product of V of c with A applied to V of c. We get this identity simply by moving the adjoint across the inner product.

Thus the quadratic form of B is the quadratic form of A, restricted to vectors in the selected subspace and rewritten in its own coordinates.

This explains why compression is so useful. We can study a large operator using a much smaller matrix, without changing the quadratic measurements made on the chosen subspace.

It also tells us what the construction does *not* promise. It does not say that applying A stays inside that subspace. To obtain B we apply A first, then throw away whatever component points outside, because V star measures only the part visible inside the selected subspace.

Our diagonal-line example exhibits exactly that loss.

## The missing part is a residual

Let's compute the part that was discarded.

A applied to v has first coordinate one over the square root of two and second coordinate three over the square root of two.

The compressed operator says the best represented action on our line is two times v, which has both coordinates equal to two over the square root of two.

Subtract two times v from A of v. The difference has first coordinate negative one over the square root of two and second coordinate positive one over the square root of two.

That difference is perpendicular to v. Its inner product with v is negative one half plus one half, which equals zero.

This difference is called the residual. More generally, for an embedding V and the canonical compression B, the residual is A V minus V B. It is a map from coefficient space into ambient space.

Think carefully about the two pieces. V B stays in the selected subspace. The residual records what A does that our selected subspace cannot represent.

The residual is not an arbitrary numerical error. It is an exact algebraic quantity defined from A and V. A small residual can become evidence that our selected space is close to an invariant subspace, but that conclusion will later need additional spectral assumptions.

## Why every Ritz residual is perpendicular

We can prove a striking identity without using the spectral theorem.

Apply V star to the residual. We get V star A V minus V star V B. The first term is B by definition. In the second term, V star V is the identity because V is an isometry. So the second term is also B.

The difference is zero.

Thus every residual vector is orthogonal to every vector in the range of V. It is not merely that the error happens to point away from our diagonal line. The canonical choice of compression forces it to lie in the perpendicular complement of the trial subspace.

This is called the Galerkin orthogonality condition. Its name is less important than its content: when we compress A to a trial subspace, we have accounted for all of the component of A V that lies *within* that subspace. Only the perpendicular component remains.

That is why the residual is so informative. It isolates the precise defect of invariance.

## When is compression exact?

Suppose now that the selected subspace is invariant under A. That means applying A to any vector in the subspace leaves the result inside it.

If A V of c always remains in the range of V, then the projection V V star does nothing to it. So V B of c, which is V V star A V of c, is exactly A V of c. The residual is zero.

Conversely, if the residual is zero, A V equals V B. Every output of A V therefore lies in the range of V. The selected subspace is invariant.

We have proved an equivalence: the canonical Ritz residual vanishes exactly when the trial subspace is invariant under A.

For a self-adjoint operator, invariance of a closed subspace also implies that its orthogonal complement is invariant. In that case the subspace is reducing, and we can decompose A into separate diagonal blocks. We established that on invariant and reducing subspaces.

As a simple exact example, take the horizontal axis under our diagonal matrix. A sends horizontal vectors back to the horizontal axis. Compression gives multiplication by one, and the residual is exactly zero. This time the compressed eigenvalue is a genuine ambient eigenvalue.

## An approximate eigenpair and a Ritz value

Now imagine we have a trial subspace with several orthonormal coordinate columns, not just one. Compression produces a small square matrix B. If we find an eigenvector c of B with eigenvalue mu, we can lift c into ambient space by forming V of c.

The compression equation says that the part of A V of c visible in the trial subspace behaves like mu times V of c. The residual measures the remaining part, perpendicular to that subspace.

The pair consisting of mu and V of c is called a Ritz pair. Mu is a Ritz value. It need not be an exact eigenvalue of A, and V of c need not be an exact eigenvector.

If the corresponding residual vanishes, the Ritz pair is exact. If it does not vanish, the residual tells us how far the proposed eigenvector equation fails, before we make any claim about the distance to a true eigenspace.

Our diagonal-line example was the simplest Ritz pair. Its Ritz value was two. Its candidate vector was v. Its residual had length one. We can compute all of those numbers directly, even without knowing a general perturbation theorem.

Later, when we prove spectral separation estimates, we will investigate when small residual length controls the angle to an exact subspace. For now, there is no reason to assume the relationship is always favorable.

## Which properties survive compression?

Compression preserves several important structures. If A is self-adjoint, then B is self-adjoint: taking the adjoint of V star A V reverses the product and replaces A by A star, which is still A. If A is positive, B is positive, because its quadratic form is the same nonnegative form evaluated on vectors of the kind V of c.

But compression is not an algebra homomorphism. In general, compressing A squared does not give the square of the compression of A.

Here is a tiny example. Let A swap horizontal and vertical coordinates, and choose the horizontal line as the trial subspace. Applying A to a horizontal vector sends it vertically, so its compression is zero. But A squared is the identity. Compressing A squared therefore gives the identity on our one-dimensional coordinate space, whereas squaring the zero compression still gives zero.

The missing contribution went out of the subspace during the first application of A, then came back during the second. Compressing after the first step threw it away.

This is why one must never silently transfer an identity involving products, inverses, or exact eigenvalues from A to its compression. We have to check which structures the compression really preserves.

## Where this leaves us

We can now distinguish three objects. V represents the chosen subspace. B equals V star A V and records the part of A visible within that subspace. The residual A V minus V B records the part escaping it.

The compression, the off-diagonal residual, and the exact invariant-subspace condition describe three different aspects of an approximate eigenspace. Keeping them distinct prevents coordinate information from being mistaken for invariance.

Try to reconstruct the proof that V star applied to the residual is zero. Then explain why zero residual is equivalent to invariance. Finally, return to the diagonal-line example: why does a Ritz value of two fail to be an eigenvalue even though it is obtained from an exact calculation?


<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

Let \(V:F\to E\) be a linear isometric embedding and \(A:E\to E\) a linear operator. Define the Rayleigh–Ritz compression and its canonical residual by

\[
B=V^*AV:F\to F,\qquad R=AV-VB:F\to E.
\]

By \(V^*V=I_F\), we have \(V^*R=0\), so \(\operatorname{ran}R\subseteq(\operatorname{ran}V)^\perp\). The residual vanishes exactly when \(\operatorname{ran}V\) is invariant under `A`. For self-adjoint `A`, `B` is self-adjoint. An eigenpair \(Bc=\mu c\) produces a Ritz pair \((\mu,Vc)\) with defect \(AVc-\mu Vc=Rc\).

**Lean bridge.** The DKPS-developed module `ForTauCeti/Analysis/InnerProductSpace/Residual/Ritz.lean` (moved from `DavisKahan/FiniteDimensional/Residual/Ritz.lean` during the upstream staging work) uses `F →ₗᵢ[𝕜] E` for the isometric embedding:

```lean
/-- Compression of `A` to the isometric coordinate space of `X`. -/
@[expose]
noncomputable def compression (A : E →ₗ[𝕜] E) (X : F →ₗᵢ[𝕜] E) :
    F →ₗ[𝕜] F :=
  X.toLinearMap.adjoint ∘ₗ A ∘ₗ X.toLinearMap
```

```lean
/-- Residual of an approximate invariant pair represented by an isometric
embedding. -/
@[expose]
noncomputable def residual (A : E →ₗ[𝕜] E) (X : F →ₗᵢ[𝕜] E)
    (M : F →ₗ[𝕜] F) : F →ₗ[𝕜] E :=
  A ∘ₗ X.toLinearMap - X.toLinearMap ∘ₗ M
```

```lean
/-- Galerkin/Ritz residual. -/
@[expose]
noncomputable def ritzResidual (A : E →ₗ[𝕜] E) (X : F →ₗᵢ[𝕜] E) :
    F →ₗ[𝕜] E :=
  residual A X (compression A X)
```

The module proves `isSymmetric_compression` and `ritzResidual_eq_zero_iff_reduces`. Despite the latter declaration's name, its statement uses membership in `Module.End.invtSubmodule A`, i.e. **invariance**, not necessarily reduction for an arbitrary operator. The spoken lecture's reduction conclusion is restricted to self-adjoint `A`.

`→ₗ` is an algebraic linear map, `→ₗᵢ` a linear isometry, `.adjoint` the adjoint map, and `∘ₗ` linear-map composition. This finite-dimensional interface is distinct from the domain-aware unbounded Rayleigh–Ritz constructions, which the course will teach later. The mathematical development should be credited to DKPS even where its current code is staged under a `TauCeti` namespace.

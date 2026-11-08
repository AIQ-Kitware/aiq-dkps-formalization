# 048000 — The Sz.-Nagy–Kato intertwiner

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `005000` Banach algebra of bounded operators; `011000` projections; `015000` reducing subspaces; `034000` positive square roots; `037000` polar decomposition; `046000` positive cosine/sine operators; `047000` uniform acuteness. **Next:** canonical direct rotation.

<!-- BEGIN SPOKEN LECTURE -->

# How do we build a rotation from two projections?

We know how to calculate angles between two subspaces. We know how to build their sine and cosine operators. And we know that when their projection gap is strictly below one, the cosine operator has a bounded inverse.

But an angle is a measurement, not a motion. If we want to carry the first subspace onto the second, we need an operator that actually moves vectors.

There are many possible unitary maps that can do that, even in a small Euclidean space. We want one determined by the pair of projections themselves, without choosing a basis or arbitrarily twisting the complementary directions.

Today's construction, often called the Sz.-Nagy–Kato intertwiner, provides the missing bridge. It first builds an operator that sends the two pieces of one orthogonal decomposition into the corresponding pieces of another. Then polar decomposition removes its unwanted stretching. In the uniformly acute case, the result is a unitary motion.

## Assemble the map one piece at a time

Let P be projection onto U and Q projection onto V. We can split any vector x into its U component, P x, and its component perpendicular to U, identity minus P applied to x.

We want the first piece to land in V. So we apply Q to P x.

We want the perpendicular piece to land in V perpendicular. So we apply identity minus Q to identity minus P applied to x.

Add the two outputs. Call the resulting operator K.

In words, K of x equals the projection onto V of the U part of x, plus the projection onto V perpendicular of the U-perpendicular part of x.

In symbols, if we are writing rather than speaking, K is Q P plus the product of identity minus Q and identity minus P.

This is not yet a rotation. Its outputs may be shorter than its inputs. But it has an essential property: it respects the way we have split the space.

## The intertwining identity

Let us test K on a vector from U. Its U-perpendicular component is zero, so K sends it into V. That says K after P equals Q after K.

Let us verify the algebra. Multiply K by P on the right. The second term disappears, because P followed by identity minus P is zero. The first term becomes Q P. Now multiply K by Q on the left. The first term becomes Q P again, because Q squared is Q. The second term disappears, because Q followed by identity minus Q is zero.

Both products are the same.

This equation is called an intertwining identity. K need not commute with P, because P and Q are not necessarily equal. Instead, it converts the action of P before transport into the action of Q after transport.

The analogous identity holds for the complementary projections. Thus K sends the U component into V, and the U-perpendicular component into V perpendicular.

Intertwining is the property we want to preserve when we remove K's stretching.

## A surprising norm identity

We can determine exactly how K changes lengths. Its two output pieces lie in orthogonal subspaces: V and V perpendicular. So their squared lengths add.

Take a vector x. The squared norm of Q P x is the squared norm of P x minus the squared norm of its part perpendicular to V. Similarly, the squared norm of the complementary output is the squared norm of the U-perpendicular part of x minus the squared norm of its part inside V.

Adding the two expressions, the first two original squared norms add to the squared norm of x.

What did we subtract? Exactly the squared norm of P minus Q applied to x. To check that, split that difference into two perpendicular terms: the U part lost outside V, and the U-perpendicular part that enters V.

Therefore K preserves the squared length of x, except for the squared length removed by P minus Q.

Equivalently, K adjoint times K is the identity minus the square of P minus Q.

That is the cosine-squared operator defined by the overlap of the two projections.

This is a satisfying connection. The operator assembled from projections automatically stretches each principal plane by its cosine. It has the right directions, but the wrong lengths.

## The planar calculation

Return to two lines in the plane meeting at angle theta. U is horizontal and V is tilted counterclockwise.

On the horizontal axis, K sends the unit vector to its projection onto V. That vector has length cosine theta and points along V.

On the vertical axis, K sends the unit vector to its projection onto the line perpendicular to V. That vector also has length cosine theta. In the acute range, both outputs are the ordinary rotated basis vectors, multiplied by cosine theta.

Thus K equals cosine theta times the rotation through theta.

What would we do to recover the rotation? Divide by cosine theta.

For a general Hilbert space, division by a scalar cosine becomes multiplication by the inverse of a positive cosine operator. This is exactly what polar decomposition is designed to do.

## Why a gap below one makes K invertible

There is a second quick identity. Expand K minus the identity. After simplifying with P squared equal to P, the result is P replaced by Q, multiplied by the reflection through U.

More precisely, K minus the identity equals Q minus P, followed by the reflection that acts as plus one on U and minus one on U perpendicular.

That reflection is unitary. So the norm of K minus the identity equals the norm of Q minus P.

If that norm is strictly below one, K is within distance one of the identity in the Banach algebra of bounded operators. Our Neumann-series theorem now applies: K is invertible.

This is not just an analogy to the planar case. The operator-algebra estimate gives a genuine bounded inverse in any Hilbert space, without selecting individual principal vectors.

## Remove the stretching by polar decomposition

Write the polar decomposition of K. Its positive modulus is the square root of K adjoint times K. We have just shown that this equals the positive square root of the identity minus the square of the difference between P and Q. In other words, it is exactly the cosine operator constructed earlier.

Call this positive modulus C. In the uniformly acute case C is invertible. Define W by K followed by the inverse of C.

Now calculate W adjoint times W. Since C is the positive square root of K adjoint times K, the factors cancel to the identity. So W is an isometry.

Because K and C are invertible, W is invertible as well. An invertible isometry is unitary. We have obtained a unitary operator entirely from P and Q.

We still must prove that it actually sends U onto V.

## The intertwining identity survives

We already know K P equals Q K. We also know K adjoint times K commutes with P. To see this, take the adjoint of the intertwining identity and combine it with the original equation. The middle Q factors simplify because Q is a projection.

Since K adjoint times K commutes with P, so does its positive square root C, and so does C inverse.

Now take W P. Replace W by K C inverse, commute C inverse past P, and then use K P equals Q K. We obtain W P equals Q W.

That is the desired intertwining identity for the unitary operator itself.

If x belongs to U, P x equals x, so Q W x equals W x. Therefore W x belongs to V. Because W is unitary and the identity also holds for the orthogonal complements, the map carries U onto V, not just into it.

We have reached the goal: the first subspace, its orthogonal complement, and their entire ambient geometry have been transported together.

## What is special about this transport?

The construction was canonical in the sense that we made no basis choices. Given P and Q, it specified K, took its positive modulus, and used the polar factor.

But the word canonical does not mean that no other unitary can send U onto V. We can compose a transporter with additional motions internal to the subspaces and still carry U onto V.


There is also an important boundary. If the projection gap reaches one, C may no longer have a bounded inverse. The formula using C inverse may then fail, even when a polar factor still exists. Nonacute pairs require a more careful analysis of kernels, crossed defects, and possible unitary completions.

## Reconstruction

First, derive K P equals Q K directly from the projection identities.

Second, use orthogonality of the two output pieces to prove that K adjoint K equals identity minus the square of P minus Q.

Third, derive K minus identity as Q minus P followed by reflection through U. Explain why a projection gap below one permits the Neumann series.

Finally, show that the modulus C commutes with P, and use that fact to prove that the polar factor W still intertwines P with Q.

When you can reconstruct those four steps, you have built a unitary transport from first principles.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

Let \(P=P_U\) and \(Q=P_V\). The Sz.-Nagy–Kato **pre-polar intertwiner** is
\[
K=QP+(I-Q)(I-P).
\]
Elementary projection algebra gives
\[
KP=QK,\quad K(I-P)=(I-Q)K,\quad
K^*K=I-(P-Q)^2,\quad K-I=(Q-P)(2P-I).
\]
The reflection \(2P-I\) is unitary, so \(\|K-I\|=\|P-Q\|\). If \(d=\|P-Q\|<1\), the Neumann series makes \(K\) invertible. Its modulus is the invertible positive cosine \(C=(I-(P-Q)^2)^{1/2}\), and
\[
W=KC^{-1},\qquad W^*W=WW^*=I,\qquad WP=QW.
\]
On a principal plane at angle \(\theta<\pi/2\), \(K=\cos\theta\,R_\theta\) and \(W=R_\theta\).

**Lean bridge.** `DavisKahan/Geometry/Polar/DirectRotation.lean` defines exactly the pre-polar operator:

```lean
@[expose]
noncomputable def spectraCanonicalIntertwiner
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : H →L[𝕜] H :=
  V.starProjection * U.starProjection +
    (Vᗮ).starProjection * (Uᗮ).starProjection
```

The same file proves its projection intertwining property:

```lean
theorem spectraCanonicalIntertwiner_mul_projection
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    spectraCanonicalIntertwiner U V * U.starProjection =
      V.starProjection * spectraCanonicalIntertwiner U V := by
```

The excerpt above stops at the proof introducer; the full proof appears in the source file. `spectraCanonicalIntertwiner_sub_one` proves the reflection factorization, `norm_one_sub_spectraCanonicalIntertwiner_lt_one` obtains the strict unit-ball bound, and `spectraCanonicalIntertwinerUnit` constructs its inverse-bearing unit. The positive polar part and its unitary factor are represented by `spectraCanonicalPolarFactor`, `spectraCanonicalPolarFactor_mem_unitary_of_uniformlyAcute`, and `spectraCanonicalPolarFactor_decomposition`.

`DavisKahan/Geometry/Polar/PolarIntertwining.lean` proves `canonicalPolarFactor_intertwines_from_polar`, including a statement that holds without uniform acuteness, although that general polar factor need not itself be unitary. This is why the proof structure separates intertwining from invertibility.

**Reconstruction exercise:** derive all four projection identities above, verify \(K=\cos\theta\,R_\theta\) for two lines, and show \(WP=QW\) without introducing a principal-vector basis.

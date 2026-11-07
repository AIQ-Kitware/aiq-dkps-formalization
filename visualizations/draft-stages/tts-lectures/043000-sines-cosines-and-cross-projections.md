# 043000 — Sines, cosines, and cross projections

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `011000` projection theorem; `015000` invariant/reducing subspaces; `020000` orthogonal coordinate embeddings; `030000` spectral projections; `035000` modulus; `042000` principal angles. **Next:** cosine–sine decomposition.

<!-- BEGIN SPOKEN LECTURE -->

# How can a projection measure an angle?

Imagine two lines in the plane. The first is horizontal. The second tilts upward at an angle theta. A unit arrow along the first line has two parts relative to the second: a part that lands on the second line when projected, and a part that remains perpendicular to it.

The lengths of those parts are cosine theta and sine theta. We know this from ordinary right triangles. What matters today is that this is also a statement about linear operators. If we can express those two parts using projections, we will have a way to measure angles between entire subspaces, even when there are several different principal angles.

Last time we found principal angles from singular values of an overlap map. Today we will express their cosines and sines directly through orthogonal projections. Then we will relate those operators to the difference between two projections. That last comparison is one of the geometric ingredients behind Davis–Kahan theory, although we are still studying geometry rather than perturbations.

## Two ways to split one vector

Call our subspaces U and V, and call their orthogonal projections P and Q. The letter P always projects onto U; Q always projects onto V.

Take a vector x that already belongs to U. Then P of x is just x. Now decompose it relative to V. The component inside V is Q of x. The component perpendicular to V is x minus Q of x, or equivalently, identity minus Q applied to x.

Those two pieces are perpendicular. Therefore the square of the length of x equals the square of the length of Q x plus the square of the length of identity minus Q applied to x.

This is Pythagoras, but it is also an operator identity. When we begin with an arbitrary ambient vector and project it into U first, the two maps become Q P and identity minus Q followed by P.

Think of Q P as a cosine-type overlap map. It reports the portion of a source direction that survives inside the target. Think of identity minus Q followed by P as a sine-type error map. It reports what escapes the target.

The words cosine and sine are earned by the right-triangle identity. They are not decorative names.

## A one-line calculation that matters

Work with the unit horizontal vector in the plane. Let the target line make an angle theta with it. The target unit direction has horizontal component cosine theta and vertical component sine theta.

Projecting the horizontal vector onto the target multiplies that target direction by cosine theta. Its resulting length is cosine theta.

Subtract that projection from the original vector. The remaining component has length sine theta. So, on this particular source direction, the two operators reproduce exactly the two sides of the right triangle.

Notice a subtlety. The output of the cosine map lies in V, not in U. The sine map's output lies in V perpendicular. Neither map is necessarily a positive operator acting within U. The quantities called the positive cosine and sine operators will come later, by taking moduli or positive square roots of compressions. For now, we are measuring lengths of rectangular maps.

## From one angle to many

Let us return to two higher-dimensional subspaces. Choose an orthonormal coordinate embedding for U; call it E. It sends a short coordinate vector into the ambient space without changing its length.

The target projection Q composed with E tells us how a source coordinate vector overlaps V. Its singular values are the cosines of the directed principal angles, when counted on the source coordinate space.

Now consider identity minus Q composed with E. This is the complementary, or sine, map. Its singular values are the sines of those same directed angles, with the correct ordering matched through a common orthonormal source basis.

Why should they have matching directions? Take the adjoint of each map and compose it with the map itself. The cosine Gram operator is E adjoint Q E. The sine Gram operator is E adjoint times identity minus Q times E.

Add them. Q and identity minus Q add to identity, and E adjoint E is identity because E is isometric. Thus the two Gram operators add to identity.

This is stronger than saying that the two operators happen to have complementary singular-value lists. Each Gram operator is identity minus the other. They commute, and an eigenvector of either is an eigenvector of both. On a common eigenvector, if the cosine Gram eigenvalue is cosine squared theta, the sine Gram eigenvalue must be sine squared theta.

So one orthonormal set of source directions explains the entire pattern of overlap and escape.

## What changes when dimensions differ?

Suppose U is a plane but V is a line inside that plane. One direction of U is perfectly aligned with V. The other direction of U is perpendicular to V.

From the perspective of U, the directed angles are zero and ninety degrees. From the shorter, paired principal-angle convention, there is only one angle, which is zero. Both descriptions are valid, but they answer different questions.

The rectangular sine map keeps track of the unpaired source direction. If our goal is to measure everything that escapes from U, dropping that direction would lose essential information.

This is why we must always ask what space a principal-angle operator acts on, and which direction the comparison goes. The maps from U to V and from V to U can have different numbers of singular values and different kernels.

## The difference between two projections

There is another natural geometric quantity: the operator P minus Q. It takes any ambient vector and compares its two projected versions.

At first it may seem that the difference should be identical to the sine map. But they have different domains and outputs. The sine map, identity minus Q followed by P, measures the escape of U into V perpendicular. The difference P minus Q also sees directions starting outside U, including how much V escapes U.

We can relate them exactly.

Square P minus Q. Expand as though these were matrices, but do not interchange P and Q. The result is P plus Q minus P Q minus Q P.

Now reorganize that expression into two pieces. One is P times identity minus Q times P. The other is identity minus P times Q times identity minus P.

Check by expansion: the first contributes P minus P Q P. The second contributes Q minus P Q minus Q P plus P Q P. The middle terms cancel in the sum, leaving exactly the square of P minus Q.

Why is this regrouping useful? The first piece acts only inside U and vanishes on U perpendicular. The second acts only inside U perpendicular and vanishes on U. The square is therefore block diagonal with respect to U and U perpendicular.

The norm of a block-diagonal positive operator is the larger norm of its two blocks. And each block is the Gram operator of a cross projection. The first is the Gram operator of identity minus Q followed by P. The second is the Gram operator of identity minus P followed by Q.

Taking positive square roots of those norm relationships gives a precise formula: the operator norm of P minus Q equals the larger of the two cross-projection norms.

So the difference of projections measures the worse of two directional errors: how much of U misses V, and how much of V misses U.

## A forty-five-degree check

Take U as the horizontal line in the plane, and V as the line tilted by forty-five degrees.

The projection P sends a vector to its horizontal part. The projection Q sends it to its component along the tilted line.

For the horizontal unit vector, identity minus Q leaves a perpendicular component of length one over the square root of two. The reverse cross projection has the same norm. Our formula predicts that P minus Q has operator norm one over the square root of two as well.

You can verify this directly from the two-by-two projection matrices. In this equal-dimensional line example, the two directional errors are balanced.

But do not conclude that the two directional errors are always equal. If U is a proper subspace of V, every vector in U lies in V, so identity minus Q followed by P is zero. Yet V has directions perpendicular to U, so identity minus P followed by Q has norm one. The difference of the projections has norm one. The maximum in our formula is essential.

## What we have built

We now have three complementary measurements. A cosine map tells us what remains inside a target subspace. A sine map tells us what escapes it. The difference of projections measures the larger of the two directional escapes.

All three are constructed using operators we already know. None requires us to invent coordinates beyond those needed for a worked example. And the Gram identity tells us why the cosine and sine measurements come from the same principal directions.

Here is your reconstruction exercise. Starting only from the identities P squared equals P, Q squared equals Q, and the fact that both projections equal their adjoints, derive the formula for the square of P minus Q. Identify its two orthogonal blocks and explain why its norm is the maximum of the two directional projection errors.

Then revisit a plane containing a line. Explain why one directional error vanishes while the reverse error does not.

Next time we will use principal directions to build actual two-dimensional blocks. Inside each block, both projections will have simple two-by-two matrices, and sine and cosine will become visible together.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

For orthogonal projections \(P=P_U\), \(Q=P_V\) on a Hilbert space and an isometry \(E:K\to H\) with range \(U\),
\[
C=QE,\quad S=(I-Q)E,\quad C^*C=E^*QE,\quad S^*S=E^*(I-Q)E=I-C^*C.
\]
For **directed source-indexed** principal angles, eigenvalues of \(C^*C\) and \(S^*S\) are paired \(\cos^2\theta_i\) and \(\sin^2\theta_i\), including padded right angles as appropriate. Distinguish these rectangular maps from the later *positive cosine and sine operators* on the source space.

Also,
\[
(P-Q)^2=P(I-Q)P+(I-P)Q(I-P),
\quad \|P-Q\|=\max\{\|(I-Q)P\|,\|(I-P)Q\|\}.
\]
This identity holds for two orthogonal projections, including unequal ranks.

**Lean bridge.** `ForTauCeti/Analysis/InnerProductSpace/AngleGeometry.lean` supplies explicit links between source-restricted cross projections and directed principal-angle sequences:

```lean
theorem singularValues_cosThetaMap_comp_subtype (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ((U.cosThetaMap V).toLinearMap ∘ₗ U.subtype).singularValues =
      Submodule.principalCosines U V := by

theorem singularValues_sinThetaMap_comp_subtype (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ((U.sinThetaMap V).toLinearMap ∘ₗ U.subtype).singularValues = Submodule.principalSines U V := by
```

The source is the first argument `U` and the target is `V`. `U.subtype` is the inclusion of source vectors into the ambient space; the singular values are attached to that source-indexed map. The accompanying reflection formula in `ForTauCeti/Analysis/InnerProductSpace/Projection/Blocks.lean` gives another way to express projection geometry:

```lean
theorem reflectionOperator_eq_two_smul_sub_id (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] :
    U.reflectionOperator =
      (2 : 𝕜) • U.starProjection - ContinuousLinearMap.id 𝕜 E := by
```

Here `U.starProjection` is the orthogonal projector \(P_U\), and `U.reflectionOperator` acts as \(2P_U-I\). The norm formula for \(P-Q\) is derived in the spoken lecture; the excerpts show the formal objects that support this operator language.

**Reconstruction:** Derive the two Gram identities; verify the squared-projection-difference identity without assuming \(PQ=QP\); check the line-versus-plane counterexample.

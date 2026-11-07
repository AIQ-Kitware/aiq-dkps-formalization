# Overlaps, alignment, and Gram rigidity

<!-- BEGIN SPOKEN LECTURE -->

In our last few lectures we built a family of vectors from a coefficient space, measured the inner products between those vectors, and compressed an operator to a selected subspace. Today we want to compare two such families.

Here is the question. If two lists of vectors look different, are they describing different geometry? Or have we merely chosen different coordinates for the same geometry?

There are really two questions hiding here. One is whether each list has the same *internal* geometry: the same lengths and the same angles among its own vectors. The other is how the two lists are situated *relative to each other* inside a shared ambient space. The Gram matrix answers the first question. An overlap matrix helps answer the second.

## Internal geometry is not position

Think of a single unit arrow in ordinary three-dimensional space. Point it east, and then point a second unit arrow straight upward. Both one-element families have the same Gram matrix: a one-by-one matrix containing the number one. That matrix records the arrow's length squared. It says nothing about which direction the arrow points in the room.

Now take a pair of perpendicular unit arrows. Rotate the whole pair through any rigid rotation. Their Gram matrix remains the identity matrix. Every length and every pairwise angle is unchanged, but the pair can occupy a different plane.

This is our first distinction. Equal Gram matrices describe congruent vector configurations, not necessarily identical vectors and not necessarily identical embedded subspaces.

In fact, if the families have equal Gram matrices, we can construct an inner-product-preserving map between their spans. We proved the essential argument in the Gram lecture, but it is worth connecting it to today's problem.

Suppose the first family synthesizes a coefficient list into a vector, and the second family does the same. Define a map by using the same coefficient list in both families. Why is this well-defined? Because any coefficient list that synthesizes to zero in the first family has zero squared length as computed from its Gram matrix. Equal Gram matrices give zero squared length in the second family too. So no ambiguity arises from two coefficient lists representing the same vector.

This map preserves inner products for the same reason: the two Gram quadratic forms agree. Thus we obtain an isometry between the spans. Whether it extends to a unitary map of the entire ambient spaces is a separate question about their orthogonal complements.

## Comparing two frames in one space

Now assume both families live in the same Hilbert space. Call their coordinate embeddings V and W. Each takes a coefficient vector and produces an ambient vector, and each preserves lengths. So V star V and W star W are both the identity on coefficient space.

We define their *cross-Gram*, or overlap, operator to be V star W.

Read the order slowly. First, W synthesizes a coordinate vector into the ambient space. Then V star asks how much of that ambient vector lies along the coordinate directions of V. The result is a matrix whose entries are the inner products between a vector from the V frame and a vector from the W frame.

If the two frames each have two vectors, the overlap matrix has four entries. The entry in row one, column two tells us how the first V vector overlaps with the second W vector. Unlike each frame's own Gram matrix, this cross-Gram changes when the two frames move relative to each other.

Go back to our two unit arrows, one east and one upward. Their individual Gram matrices are both one. Their cross-Gram is zero, because the arrows are perpendicular. If they point in the same direction instead, their cross-Gram is one. The two questions give different answers, exactly as they should.

## What if the two frames span the same subspace?

Suppose V and W have the same number of coordinate directions, and their ranges are exactly the same subspace. Then the overlap matrix Q, meaning V star W, describes a pure change of orthonormal coordinates.

We can prove this. V V star is the orthogonal projection onto V's range. Since W lands entirely inside that range, applying V V star to W does nothing. So V V star W equals W.

But V star W is Q. Therefore V Q equals W. Every W coordinate vector is obtained as a combination of the V coordinate vectors with coefficients given by Q.

Now take Q star Q. Expanding it gives W star V V star W. We just said V V star W equals W, so this becomes W star W, which is the identity. Because the two coordinate spaces have the same finite dimension, Q is an orthogonal or unitary matrix.

Thus changing orthonormal coordinates *inside one fixed subspace* creates a unitary overlap. Its columns are themselves an orthonormal coordinate system.

Notice the assumptions. If one frame has fewer vectors, or if their ranges are different, this exact conclusion need not hold.

## When the subspaces differ

For different subspaces, the same expression Q star Q becomes W star P W, where P is projection onto V's range. It is no longer necessarily the identity. It measures how much of each W vector survives projection onto V's subspace.

Let's compute a small example. Work in three-dimensional space. Let V use the first and second coordinate axes. Let W use the second coordinate axis and a unit arrow halfway between the first and third axes.

Both V and W are orthonormal frames with two columns, so both internal Gram matrices are the two-by-two identity. But the subspaces are not the same. The W frame contains one direction fully inside V's plane, and another direction leaning out of it.

If we order the frames so corresponding directions line up, the overlap matrix has one on one diagonal entry and one over the square root of two on the other. The off-diagonal entries are zero.

That tells us something concrete. One W direction is perfectly represented by V's subspace. The other loses half its squared length when projected onto it. The overlap distinguishes those directions even though the two families each look internally orthonormal.

In general, projection cannot increase length. Therefore Q cannot increase coefficient-vector length either: first W preserves length, then V star measures projected coordinates. So the operator norm of Q is at most one. Its singular values, which we will construct later, lie between zero and one. Those numbers will lead us to principal angles between subspaces.

## Alignment is a third question

We can also ask: if the two frames represent approximately the same subspace, which coordinate change best aligns one frame with the other?

For a single unit arrow, the answer is simple. If the second arrow points opposite the first, changing the sign of its coordinate makes them match. But if they point in perpendicular directions, changing that sign cannot make them coincide. The first discrepancy was a coordinate choice. The second is geometric.

For several columns, we may multiply the second frame by an orthogonal or unitary coordinate matrix. This changes the basis chosen *within* its subspace, but not the subspace itself. We can try to choose that matrix to make corresponding frame vectors as close as possible.

There is a useful way to measure total discrepancy: add the squared lengths of all columnwise differences. Expanding the squares gives a constant part, because both frames have unit orthonormal columns, minus a term involving the real part of the trace of the overlap matrix times the coordinate change.

So minimizing squared alignment error amounts to maximizing an overlap trace. Later, singular-value decomposition and polar decomposition will let us solve this optimization systematically. For today, the lesson is what we are and are not allowed to change. A coordinate alignment may improve the comparison, but it never moves the underlying subspace.

## The distinction to retain

We have three different mathematical objects, each answering a different question.

The Gram matrix of V describes how the V vectors relate to each other. The Gram matrix of W describes how the W vectors relate to each other. Their cross-Gram V star W describes how the two families overlap in a shared ambient space.

Equal internal Gram matrices give an abstract isometry of spans. A unitary cross-Gram, under the equal-dimension orthonormal-frame assumptions, tells us that the two frames span the same subspace. A cross-Gram whose singular values are smaller than one records directions that lean away from the other subspace.

To check your understanding, try to answer three questions without looking back. Can two orthonormal frames have identical internal Gram matrices but orthogonal ranges? Why does V V star W equal W when W's range lies inside V's range? And why does that identity imply that V star W is unitary when the frames have the same finite number of columns?

The next lecture will develop another pair of Gram operators, formed from an arbitrary rectangular map rather than from two orthonormal frames. That pair will explain why singular values are shared between two different coordinate spaces.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematical facts and Lean correspondence (display only)

For isometric embeddings \(V,W:\mathbb K^r\to H\), let \(Q=V^*W\), \(P_V=VV^*\). Then
\[
Q^*Q=W^*P_VW\le I,\qquad \|Q\|\le 1.
\]
If \(\operatorname{ran}V=\operatorname{ran}W\), then \(VQ=W\) and \(Q^*Q=I\); because the coefficient space is finite-dimensional and square, \(Q\) is unitary. Conversely, if \(Q\) is unitary then \(W\)'s columns lose no length under \(P_V\), hence \(\operatorname{ran}W=\operatorname{ran}V\). Equal internal Grams alone do not imply equal ambient ranges.

The exact equal-Gram span-isometry result appears as a DKPS-local wrapper in `Acharyya2025/GramRigidity.lean`, delegating to the accepted upstream development:

```lean
theorem exists_linearIsometryEquiv_of_inner_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {ι : Type*} (φ ψ : ι → E)
    (h : ∀ i j, ⟪φ i, φ j⟫ = ⟪ψ i, ψ j⟫) :
    ∃ W : E ≃ₗᵢ[ℝ] E, ∀ i, W (φ i) = ψ i :=
  TauCeti.exists_linearIsometryEquiv_of_inner_eq h
```

Here `E ≃ₗᵢ[ℝ] E` is an invertible real-linear isometry of the *whole* finite-dimensional ambient space. That stronger conclusion uses equal ambient spaces and finite dimensionality; our general span argument does not require such an extension. `Acharyya2025/Overlap.lean` defines the overlap matrix concretely for two ordered spectral frames:

```lean
@[expose]
noncomputable def overlap (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : finrank ℝ E = n) (hd : d ≤ n) : Matrix (Fin d) (Fin d) ℝ :=
  fun k l => ⟪hS.eigenvectorBasis hn (Fin.castLE hd k),
              hT.eigenvectorBasis hn (Fin.castLE hd l)⟫_ℝ
```

The notation `⟪u,v⟫_ℝ` is the real inner product. The `overlap` declaration specializes the abstract cross-Gram to top eigenvector families; it will become relevant when we later compare spectral subspaces. These excerpts were checked against the supplied source snapshot, not compiled anew. Credit upstream results by their recorded donor lineage rather than assuming that their current TauCeti location identifies their origin.

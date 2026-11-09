# Orthogonal coordinate embeddings

<!-- BEGIN SPOKEN LECTURE -->

An orthonormal family can be packaged as an isometric embedding V of a smaller coefficient space into an ambient Hilbert space. Its adjoint V star measures coordinates. Composing V and V star in the two possible orders produces an identity on coefficient space and a projection on ambient space.

The two compositions look nearly identical on the page. But they describe different operations on different spaces. Distinguishing them is one of the most useful habits you can develop for reading the operator expressions in the Davis–Kahan angle estimates.

## A smaller coordinate space inside a larger space

Imagine ordinary three-dimensional space. We want to describe only the horizontal plane. We can choose a coordinate pair, a and b, and turn it into the three-dimensional vector with coordinates a, b, and zero.

Call this map V. It takes a pair of coordinates and puts the represented vector into the ambient three-dimensional space.

V is an *embedding*: it remembers its input without collapsing two different inputs into the same output. More specifically, it preserves the length of every vector. The length of the pair a, b is the square root of a squared plus b squared. The length of the three-dimensional vector a, b, zero is exactly the same.

A linear map that preserves lengths is an isometry. It is unitary only when it is also surjective. The horizontal plane is only part of three-dimensional space, so V is not onto.

Notice also that V is not a change of basis for the entire ambient space. It describes a smaller space *inside* the ambient space. We will frequently use this setup when an approximate eigenspace is represented by a small collection of columns.

## The adjoint is coordinate measurement

What does V star do? The adjoint reverses the direction of the map in the inner-product identity.

Our V goes from pairs of numbers into triples. V star goes from triples into pairs. In this example, it simply takes a three-dimensional vector and returns its first two coordinates.

The third coordinate is not an input to the coefficient space, so it disappears under V star.

Now compare V star with a genuine inverse of V. On a vector that lies in the horizontal plane, V star recovers the unique pair of coordinates that produced it. But on a general three-dimensional vector, it discards the vertical part. So V star is a left inverse of V, not a two-sided inverse on the whole ambient space.

This distinction is not a technicality. It determines which projection appears when we compose the maps.

## First composition: measure after embedding

Start with a coordinate pair, apply V, and then apply V star. You first make a horizontal vector and then read its horizontal coordinates back out.

Nothing changes. The resulting map on coordinate pairs is the identity.

In operator notation, the Gram identity is V star V equals I, the identity on coefficient space.

Why does it hold for *every* linear isometry, rather than just our simple coordinate inclusion?

Take any two coefficient vectors, c and d. The inner product of c with V star V of d equals the inner product of V of c with V of d, by the definition of adjoint. A linear isometry preserves inner products; we can derive that from its length preservation by polarization. Therefore this is the same as the inner product of c with d.

Because these two outputs have identical inner products with every test vector c, they must be equal. So V star V acts as the identity on every d.

We did not need the isometry to fill all of ambient space. The argument used only the fact that no length or angle changes when we embed coefficient vectors.

## Second composition: embed after measuring

Now reverse the order. Start with a three-dimensional vector, apply V star, and then apply V.

We measure the two horizontal coordinates and rebuild the horizontal vector from them. The vertical coordinate is removed.

The resulting map is the orthogonal projection onto the horizontal plane.

This composition is V V star, not V star V. And it acts on ambient space rather than on coefficient space.

Let us prove the general claim from the algebra. Write P for V V star. Its adjoint is itself: taking the adjoint reverses the product, and taking two adjoints returns the original map.

Next square P. We get V V star V V star. Group the middle two factors. Because V is an isometry, V star V is the identity, so the product simplifies to V V star again. Hence P squared equals P.

A self-adjoint operator that equals its own square is an orthogonal projection. Indeed, its range and kernel are orthogonal complements: if P squared equals P, then any vector splits as P x plus x minus P x; self-adjointness makes these two pieces perpendicular.

Which subspace does it project onto? Every output of P is in the range of V, because V is its final step. Conversely, if a vector already lies in the range of V, say it equals V of c, then P sends it to V V star V of c, which equals V of c. So P fixes every vector in the range and has no outputs outside it.

Therefore P is exactly the orthogonal projection onto the range of V.

Here is the pair of identities to remember. V star V is the identity on coefficient space. V V star is the projection onto the represented subspace of ambient space.

## A different orthonormal frame for the same plane

There is no unique way to choose orthonormal coordinates inside our horizontal plane.

Instead of the horizontal unit vectors pointing along the usual coordinate axes, rotate those two axes by forty-five degrees, keeping them orthonormal. The new map W sends coefficient pairs into the same horizontal plane, but a given pair now describes a different ambient vector.

So V and W are different embeddings. Nevertheless, V V star and W W star are the same ambient projection, because they represent the same subspace.

How can their coordinate descriptions differ? There is a two-dimensional orthogonal transformation Q that changes from one pair of coordinates to the other. Then W is V followed by Q. On the complex side, the corresponding change is unitary rather than merely real orthogonal.

When we later represent an eigenspace numerically, its orthonormal columns will not be uniquely determined. We can rotate those columns within their span, especially when eigenvalues are repeated. The subspace projection is insensitive to that choice.

This is one reason spectral-subspace theory often measures differences between projections or subspaces, not differences between arbitrarily chosen columns.

## Why the range is closed

There is another detail worth proving. In an infinite-dimensional Hilbert space, not every linear subspace is closed. But the range of an isometric embedding from a complete Hilbert space is closed.

Here is the argument. Suppose a sequence of vectors in the range approaches some ambient vector y. Each vector in the sequence is V of some coefficient vector. Because V preserves distances, the coefficient vectors form a Cauchy sequence whenever their images do.

The coefficient space is complete, so those coefficients converge to some c. Continuity of V tells us that their images converge to V of c. But we already said those same images converge to y. Limits are unique. Therefore y is V of c and belongs to the range.

We have now justified the existence of the range's orthogonal projection without smuggling in a closed-range assumption. This becomes important when the coordinate space is infinite-dimensional.

## How this differs from a redundant Parseval frame

For comparison, consider a redundant Parseval frame in the real plane: the three vectors are the horizontal unit vector divided by square root of two, a second copy of that same shortened horizontal vector, and the vertical unit vector. For a vector with coordinates p and q, their analysis coefficients are p over square root of two, p over square root of two, and q. Their squared magnitudes add to p squared plus q squared, so synthesis after analysis is the identity on the ambient plane. But synthesis maps three coefficients into a two-dimensional space and cannot be injective.

Analysis after synthesis is therefore an orthogonal projection on three-dimensional coefficient space, not its identity. This is the reverse of the map V: V embeds a smaller coordinate space isometrically into the larger ambient space.

For V, analysis after synthesis is the coordinate identity, while synthesis after analysis is the ambient projection. The domains and codomains of the two composites explain the difference.

Both pictures are useful. The important question is not whether a map is called analysis, synthesis, or frame. The important question is where it starts, where it ends, and which composition equals the identity.

## The connection to upcoming spectral geometry

Suppose later we select an approximate eigenspace of dimension two inside a very large matrix problem. We can use an isometric embedding V to represent that candidate subspace. Then V star V is the identity on two-dimensional coefficient space, and V V star is the ambient orthogonal projection onto the candidate subspace.

This notation lets us move between small matrices, which are easy to compute with, and ambient operators, which carry the full geometry. The two identities follow from length preservation, the adjoint identity, and the characterization of orthogonal projection.

Try to reproduce the proof that V V star is self-adjoint and idempotent, and explain why it has precisely the range of V. Then ask yourself: if two embeddings have the same range, what can change about their coordinate descriptions, and what remains invariant?

For any ambient operator A, the compression V star A V acts on the smaller coordinate space. Its entries describe A as seen from the selected subspace, but do not by themselves describe how A sends that subspace into its orthogonal complement.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

For an isometric linear embedding \(V:F\to E\) between Hilbert spaces, with adjoint \(V^*:E\to F\),

\[
V^*V=I_F,\qquad VV^*=P_{\operatorname{ran}V}.
\]

The first identity acts on `F`; the second on `E`. In particular `P` is self-adjoint and idempotent. If `F` is complete, an isometric embedding has closed range. Two isometric frames with the same range can differ by a unitary change of coefficient coordinates, without changing the ambient range projection.

**Lean bridge.** `DavisKahan/BoundedOperator/IsometricRangeProjection.lean`, a DKPS module using the `TauCeti.DavisKahan.BoundedOperator` namespace, proves both identities for continuous linear maps:

```lean
/-- The Gram operator of an isometric bounded embedding is the identity. -/
theorem adjoint_comp_isometry_eq_id
    (X : F →L[𝕜] E) (hX : IsometricEmbedding X) :
    X.adjoint ∘L X = ContinuousLinearMap.id 𝕜 F :=
  ExactSinTheta.adjoint_comp_self_eq_id_of_isometry hX
```

The companion theorem `starProjection_range_eq_comp_adjoint` identifies the orthogonal projection onto the range with `X ∘L X.adjoint`. The same module proves `isClosed_range_of_isometric` and `adjoint_apply_isometry_apply`.

`→L[𝕜]` denotes a bounded linear map, `IsometricEmbedding X` asserts norm/distance preservation, and `∘L` denotes composition of bounded linear maps. The theorem assumes complete Hilbert spaces for the range-projection construction. In the finite-dimensional Ritz companion `ForTauCeti/Analysis/InnerProductSpace/Residual/Ritz.lean`, the analogous embedding is represented as a `F →ₗᵢ[𝕜] E` linear isometry, rather than a continuous-linear-map plus a separate predicate. Both interfaces represent the same geometry at different levels of generality.

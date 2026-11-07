# 045000 — Halmos two-projection decomposition

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `010000` Hilbert spaces; `011000` projection theorem; `015000` reducing subspaces; `042000` principal angles; `043000` cross projections; `044000` cosine–sine decomposition. **Next:** positive cosine and sine operators.

<!-- BEGIN SPOKEN LECTURE -->

# What can two projections tell us about a whole space?

We have learned to compare subspaces by their principal angles. In the last lecture, we discovered that genuine intermediate angles live in two-dimensional planes, where both orthogonal projections become simple cosine–sine matrices.

But imagine a pair of subspaces with different dimensions. Some directions might belong to both. Some might belong to the first and be perpendicular to the second. Others might do the reverse. And the ambient space might contain directions belonging to neither subspace.

Those pieces are not captured by a list of strictly intermediate angles. We need a way to account for all of them without making arbitrary coordinate choices.

Halmos's two-projection decomposition gives us that organization. It separates the parts where the projections behave in the simplest possible way from the part where there is genuine, nontrivial geometry.

Today we will derive this structure in finite dimensions, describe its operator meaning, and identify the new issues that appear in a general Hilbert space.

## Four places a vector can live

Call the subspaces U and V, with projections P and Q.

The first distinguished part is their intersection: vectors lying in both U and V. For such a vector, P does nothing and Q does nothing. Both projections return the original vector. We call this the common part.

The second part consists of vectors in U but perpendicular to V. P returns the vector, while Q sends it to zero. This is the source defect. It records directions present in U that have no overlap with V.

The third part reverses the roles. These vectors lie in V but are perpendicular to U. P sends them to zero and Q returns them. This is the target defect.

The fourth part consists of vectors perpendicular to both U and V. Both projections send these vectors to zero. We can call this the exterior part.

Let us write their projection behaviors in words. On the common part, the pair of projection values is one and one. On the source defect, it is one and zero. On the target defect, zero and one. On the exterior part, zero and zero.

Those four possibilities exhaust all pairs of zero-or-one values. This is why we call them the elementary pieces.

## Why we may add these parts orthogonally

The four parts are mutually orthogonal. Let us prove one instance rather than take it on faith.

Take x in the common part and y in the source defect. Both lie in U, but x lies in V while y lies in V perpendicular. Their inner product must be zero.

For another instance, take x in the source defect and y in the target defect. The first lies in U, the second in U perpendicular. Again their inner product is zero.

The remaining pairs work the same way: for every pair of distinct elementary parts, one membership condition places the first vector in a subspace and the other in its perpendicular complement.

Thus their sum is an orthogonal direct sum. In finite dimensions, it is automatically closed, so we can take its orthogonal complement inside the whole ambient space.

Call that complement the generic part.

The word generic here does not mean random or typical. It means the part left after removing all four elementary intersection configurations. It is the space where the two projections have no shared eigenvector with both eigenvalues in the set zero and one.

## A six-dimensional example

To see every piece at once, imagine six mutually perpendicular coordinate directions, named first through sixth.

Let U be spanned by the first, second, and fifth directions.

Let V be spanned by the first direction, the third direction, and a tilted direction made from cosine theta times the fifth plus sine theta times the sixth. Take theta strictly between zero and ninety degrees.

Now inspect the four elementary pieces.

The first coordinate direction belongs to both subspaces, so it forms the common part.

The second belongs to U and is perpendicular to V, so it forms the source defect.

The third belongs to V and is perpendicular to U, so it forms the target defect.

The fourth is perpendicular to both, so it forms the exterior part.

What remains? The plane spanned by the fifth and sixth directions. In that plane, U follows the fifth axis, and V follows a line tilted through theta. That is precisely our cosine–sine principal plane.

So the entire six-dimensional geometry breaks into four easy one-dimensional pieces and one genuinely tilted two-dimensional piece.

We could change theta without changing the dimensions of the elementary pieces. We could also change the elementary dimensions without altering the angle in the tilted plane. Both kinds of information matter.

## Why the generic part is preserved

We need to justify why the remaining part can be studied independently. It is not enough simply to name an orthogonal complement.

Each elementary part is invariant under P and under Q. In fact, both act there as either identity or zero. Therefore their orthogonal sum is invariant under both projections.

Projections are self-adjoint. From our earlier lecture, an invariant subspace for a self-adjoint operator is automatically reducing: its orthogonal complement is invariant as well.

Consequently, the generic part is invariant under P and Q. Both projections split into blocks relative to the elementary part and generic part. There is no mixing between them.

That proof is short, but notice its dependencies. We used the definition of the four parts, their orthogonality, their projection behavior, and the fact that self-adjoint invariance implies reduction. We did not simply assert that a decomposition exists.

## Why all four intersections disappear on the generic part

Suppose a nonzero vector in the generic part lay in both U and V. It would belong to the common part as well. But the generic part is perpendicular to the common part. A nonzero vector cannot lie in a subspace and in its orthogonal complement simultaneously.

The same reasoning applies to the other three intersections. Inside the generic part, there are no nonzero common vectors, no source-only perpendicular vectors, no target-only perpendicular vectors, and no vectors perpendicular to both.

This is sometimes called generic position for the restricted pair of subspaces.

In finite dimensions, that means all the principal angles in the generic part lie strictly between zero and ninety degrees. As a result, the generic part splits into the principal planes we constructed in the previous lecture.

Each plane can have its own angle. The complete finite-dimensional picture is therefore: four orthogonal elementary summands, plus a family of orthogonal two-dimensional cosine–sine planes.

## A deeper operator description

What if the ambient space is an infinite-dimensional Hilbert space? The four elementary pieces can still be defined using intersections and orthogonal complements, provided the projections are onto closed subspaces.

Their sum is an orthogonal sum of closed subspaces, and its orthogonal complement gives a generic remainder. Both projections still reduce this remainder.

But here an important finite-dimensional shortcut can fail. We cannot always choose an orthonormal basis of individual principal-angle eigenvectors. An operator may have continuous spectrum rather than a complete eigenvector list.

To generalize the two-by-two picture, use an operator in place of each scalar cosine. On an appropriate copy of a Hilbert space, a positive cosine operator C and a positive sine operator S commute and satisfy C squared plus S squared equals identity.

Then the two projection blocks have the same algebraic pattern as before: one projection is identity on the first half and zero on the second; the other has C squared and S squared on the diagonal, and C times S in the off-diagonal positions.

In finite dimensions, simultaneous diagonalization of C and S recovers the individual principal planes. In infinite dimensions, their spectral calculus plays the role that a list of angles played before.

We are not proving that full infinite-dimensional representation today. It requires additional functional calculus, polar decomposition, and domain or closure arguments that will be developed in later foundations. Today we have proved the elementary splitting and explained what the remaining theorem must achieve.

## Why injective does not mean uniformly separated

There is a final distinction worth keeping in mind.

On the generic part, no nonzero direction lies in any of the four elementary intersections. In particular, the cosine and sine operators do not have actual zero eigenvectors caused by the removed endpoint pieces.

In finite dimensions, that often lets us bound both cosine and sine away from zero, because finitely many positive eigenvalues have a positive minimum.

In infinite dimensions, injectivity does not imply a positive lower bound. A sequence of directions can have principal angles approaching zero or ninety degrees even when neither endpoint angle has an eigenvector.

This distinction will matter when we study acute and uniformly acute pairs, bounded inverses, and the precise hypotheses of rotation theorems. Removing the defect spaces is not the same thing as establishing a uniform angle gap.

## What the classification buys us

Consider two projection pairs. If one has a source defect and the other does not, no unitary change of ambient coordinates can transform one pair into the other while respecting which projection is which. The dimensions of the defect spaces cannot be erased by a change of basis.

Likewise, if their generic angles differ, their geometry differs even if the elementary dimensions match.

So a classification needs both pieces of information: the sizes of the four elementary parts, and the operator describing the generic cosine–sine geometry. In finite dimensions, the latter reduces to the multiset of intermediate principal angles.

This is a much more precise way to say that two subspaces are close or far apart. We know which directions are shared, which are unmatched, which are outside both, and how the remaining directions tilt in independent planes.

## Reconstruction

Return to our six-dimensional example. Identify all four elementary parts and write down the projection values on each. Then prove that the plane spanned by the fifth and sixth coordinate directions is reducing for both projections.

Next, prove in general that the four elementary parts are mutually orthogonal and that their orthogonal complement is invariant under both projections. Finally, explain why the absence of a ninety-degree eigenvector in infinite dimensions does not by itself produce a uniform bound away from ninety degrees.

The next lecture will construct positive cosine and sine operators explicitly. That will put the geometry into a form that continues to make sense even when we cannot list every angle with an eigenvector.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

For closed subspaces \(U,V\) of a Hilbert space \(H\), the four elementary Halmos summands are
\[
H_{11}=U\cap V,\quad H_{10}=U\cap V^\perp,\quad
H_{01}=U^\perp\cap V,\quad H_{00}=U^\perp\cap V^\perp.
\]
They are mutually orthogonal and reduce both projections. Their direct sum is the *elementary part*. Its orthogonal complement \(H_g\) is the *generic part*; the pair restricted to \(H_g\) has all four crossed intersections equal to zero. In finite dimensions, \(H_g\) is an orthogonal sum of principal planes with strictly intermediate angles. In general Hilbert spaces, an operator-valued cosine–sine model replaces the finite list of angle blocks.

**Lean bridge.** `DavisKahan/Geometry/Halmos/TwoProjections.lean` defines the four summands and the generic remainder:

```lean
noncomputable abbrev halmosCommonPart (U V : Submodule 𝕜 H) : Submodule 𝕜 H :=
  U ⊓ V

noncomputable abbrev halmosSourceDefect (U V : Submodule 𝕜 H) : Submodule 𝕜 H :=
  U ⊓ Vᗮ

noncomputable abbrev halmosTargetDefect (U V : Submodule 𝕜 H) : Submodule 𝕜 H :=
  Uᗮ ⊓ V

noncomputable abbrev halmosExteriorPart (U V : Submodule 𝕜 H) : Submodule 𝕜 H :=
  Uᗮ ⊓ Vᗮ
```

And, later in the same file:

```lean
noncomputable abbrev halmosGenericPart (U V : Submodule 𝕜 H) : Submodule 𝕜 H :=
  (halmosTrivialPart U V)ᗮ
```

The theorems `projections_apply_of_mem_halmosCommonPart`, `projections_apply_of_mem_halmosSourceDefect`, `projections_apply_of_mem_halmosTargetDefect`, and `projections_apply_of_mem_halmosExteriorPart` prove the four zero/identity action patterns. The theorems `projection_left_reduces_halmosGenericPart` and `projection_right_reduces_halmosGenericPart` establish reduction. In `DavisKahan/Geometry/Halmos/GenericPosition.lean`, `genericCosineBlock` introduces the compressed positive cosine-square operator used in the operator-valued extension.

These excerpts preserve the current local declarations. The project's DKPS-to-TauCeti lineage should be tracked separately from the current import locations; file placement is not a mathematical priority claim.

**Reconstruction:** Decompose the six-dimensional example; verify mutual orthogonality and reduction; explain why finite-dimensional generic blocks have angles in \((0,\pi/2)\) and why an infinite-dimensional generic cosine need not be boundedly invertible.

# 050000 — Nonacute angles and defect matching

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `037000` polar decomposition; `044000` cosine–sine decomposition; `045000` Halmos two-projection decomposition; `047000` acuteness; `048000` canonical intertwiner; `049000` canonical direct rotation. **Next:** compact angle spectra and classification.

<!-- BEGIN SPOKEN LECTURE -->

# What happens at a right angle?

To construct the direct rotation, begin with the operator K, which combines the two orthogonal projections. When the subspaces had no crossed right-angle directions, the polar factor was unitary and determined by positivity.

Now allow an exact right angle. The cosine of ninety degrees is zero, so K sends the corresponding directions to zero. Its polar factor can no longer transport those directions: it simply annihilates them.

That failure poses two questions. Can we supply the missing motion using the right-angle pieces? And if we can, is there still one preferred answer?

The answers depend on the dimensions of two specific subspaces. We will derive them from the geometry before stating the general existence criterion.

## The two crossed defects

Let U and V be closed subspaces, with projections P and Q. Recall the four elementary parts of their Halmos decomposition.

The common part lies in both U and V. The exterior part lies perpendicular to both. Neither causes a problem for transport: on those spaces the direct rotation can act as the identity.

The source defect consists of vectors in U that are perpendicular to V. The target defect consists of vectors in V that are perpendicular to U.

These are the crossed right-angle directions. Call them D source and D target.

They are orthogonal to one another. Indeed, every source-defect vector belongs to U, while every target-defect vector belongs to U perpendicular. So their sum is an orthogonal direct sum.

These are also exactly the vectors killed by the cosine operator associated with K. On either defect, the difference between the two projections has length one, and its squared norm is unchanged. Consequently identity minus the squared projection difference vanishes.

The kernel of K is precisely the direct sum of these two defects. Outside them, the polar factor still works.

## A right-angle plane

Take the horizontal line U and vertical line V in the ordinary plane.

Here P projects onto the horizontal direction, Q onto the vertical direction, and K is zero. You can check it immediately: projecting a horizontal vector into V gives zero, and projecting a vertical vector into V perpendicular also gives zero.

So the polar factor of K is the zero operator. But the geometry obviously admits rotations from U to V. Rotate counterclockwise by ninety degrees, or clockwise by ninety degrees. Both work.

The choice is a choice of how to match the horizontal source-defect line with the vertical target-defect line. A unit horizontal vector may be sent to either unit vertical vector. Having made that choice, the map must send the vertical direction back to the corresponding negative horizontal direction, to form a quarter-turn rather than a reflection.

Both choices are unitary, and both have zero diagonal blocks. Neither violates the positivity rule, because zero is positive. So the uniqueness we proved for acute pairs has genuinely disappeared.

## Build a quarter-turn from a matching

Now suppose the two defect spaces have the same Hilbert-space dimension. That means we can choose a linear isometric equivalence J from D source onto D target.

Use J to define the missing motion. On a source-defect vector x, send x to J x. On a target-defect vector y, send y to the negative of J inverse applied to y.

What does this do to lengths? J preserves lengths, and J inverse does too. The two output spaces are orthogonal, so the map preserves the sum of squared lengths. It is unitary on the direct sum of the two defects.

Apply the map twice. Starting in D source, the first step applies J and the second applies negative J inverse. The result is negative x. Starting in D target gives the same result. Therefore its square is minus the identity on this block.

That is exactly the algebra of a ninety-degree rotation. The map is also skew-adjoint: its adjoint is its negative. As a result, the sum of the map and its adjoint vanishes on the crossed-defect block.

The only arbitrary ingredient is J. In a one-dimensional real example it has two choices, giving the two quarter-turns. In higher-dimensional spaces there are many possible isometric matchings.

## Complete the regular polar factor

Let R be the orthogonal complement of the sum of the two crossed defects. Call it the regular part.

On R, the polar factor of K preserves lengths. To understand why, recall that the polar factor is a partial isometry: it is an isometry on the orthogonal complement of K's kernel. The kernel is precisely the crossed-defect sum, so R is the initial space of the polar factor.

For this particular K, the final space of the polar factor is also R. One way to see it is to study K adjoint, which interchanges the source and target projections but has the same crossed-defect kernel. The closures of the ranges of K and K adjoint are therefore both R.

Thus the canonical polar factor is unitary on R and zero on the defects.

We can now add the two maps. Take the polar factor on R, and add the quarter-turn on the crossed-defect space. Their domains and ranges are orthogonal, so no interference occurs.

The resulting operator T is unitary on the whole Hilbert space. On the regular part it performs the canonical polar rotation. On the defect part it performs the quarter-turn determined by J.

Because each piece exchanges the correct projection spaces, T intertwines P and Q. The positive diagonal blocks come from the regular part, while the quarter-turn contributes zero to them. The required skew relation of the crossed blocks holds as well.

That proves sufficiency: an isometric matching of the crossed defects lets us construct a direct rotation.

## Why matching is necessary

Could some clever unitary avoid the matching requirement by mixing a defect direction with the regular part?

No, not if it satisfies the direct-rotation conditions. Those conditions constrain the positive diagonal blocks and the relation between the crossed blocks. The operator then has a Hermitian part determined by the positive cosine. On a crossed defect, that Hermitian part vanishes.

Let x lie in the source defect. Because the direct rotation intertwines the projections, T x lies in V. Positivity of the diagonal compression, together with its zero quadratic form on this defect, forces the source component of T x to vanish. Hence T x lies in U perpendicular as well. So T sends the source defect into the target defect.

The corresponding argument for T adjoint sends the target defect into the source defect. Unitarity supplies inverse isometries. Therefore the two crossed defect spaces must be isometrically equivalent.

The matching condition is necessary as well as sufficient.

## An infinite-dimensional obstruction

It is worth seeing why counting the ordinary dimensions of U and V is not enough.

Take a Hilbert space with an orthonormal basis indexed by all integers, positive and negative. Let U be the closed span of the basis vectors with indices zero, one, two, and so on. Let V be the closed span of those with indices one, two, three, and so on.

Both U and V are infinite-dimensional, and their orthogonal complements are infinite-dimensional too. A bilateral shift is a unitary map carrying U onto V.

But the source defect is the line spanned by the basis vector with index zero. The target defect is zero, because V is contained in U. Those two spaces cannot be isometrically equivalent.

Therefore no direct rotation satisfying our positivity and crossed-block conditions exists for this pair, despite the existence of an ordinary unitary transporter. This example separates three questions: whether the subspaces are abstractly isomorphic, whether some ambient unitary exchanges them, and whether a direct rotation exists.

## What if the defects are finite?

For finite-dimensional defect spaces, isometric equivalence reduces to equality of dimensions. Pick orthonormal bases of both defects. If their basis lengths agree, mapping one basis to the other defines J. If their dimensions disagree, no isometry onto can exist.

A useful application occurs when the difference between P and Q is compact. The crossed defects are then eigenspaces of the compact self-adjoint difference, with eigenvalues plus one and minus one. Nonzero eigenspaces of a compact operator are finite-dimensional. So both defect dimensions are finite, even if U and V are infinite-dimensional.

In that setting, numerical dimension equality really is enough to build the matching. Without a finite-dimensional or separability framework, the correct general statement is the existence of the isometric equivalence itself.

## Reconstruction

First, show that K kills both crossed defects, and explain why its kernel contains nothing else.

Second, write down a two-by-two ninety-degree rotation and identify the source-to-target map J and the negative reverse map.

Third, prove that this quarter-turn is unitary on the defect sum, while the polar factor is unitary on its orthogonal complement. Combine them.

Fourth, examine the integer-indexed basis example. Why does an ambient unitary exist while a direct rotation fails?

The conclusion is precise. A nonacute direct rotation exists exactly when the two crossed right-angle spaces admit an isometric matching. The choice of matching controls the nonuniqueness.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

For \(P=P_U\), \(Q=P_V\), define the crossed defects
\[
D_s=U\cap V^\perp,\qquad D_t=U^\perp\cap V,
\qquad D=D_s\oplus D_t,
\qquad R=D^\perp.
\]
The canonical intertwiner \(K=QP+(I-Q)(I-P)\) has \(\ker K=\ker K^*=D\). Its polar factor \(W_0\) is a partial isometry with \(W_0^*W_0=W_0W_0^*=P_R\). Given an isometric equivalence \(J:D_s\to D_t\), define the quarter-turn on \(D\) by
\[
T_J(x,y)=(-J^*y,Jx),\quad
T_J^*=-T_J,\quad T_J^2=-I_D.
\]
Extending \(T_J\) by zero on \(R\), the completed rotation is \(W_J=W_0+T_J\). It is unitary, intertwines \(P\) and \(Q\), and has positive diagonal blocks. Conversely, a direct rotation restricts to an isometric equivalence of the defects. Therefore
\[
\exists\text{ direct rotation }U\to V
\iff D_s\cong_{\mathrm{isom}}D_t.
\]
In finite dimensions, this is equivalent to \(\dim D_s=\dim D_t\). The equivalence class of \(J\) is additional choice data at right-angle blocks; it cannot be inferred from the other principal angles.

**Lean bridge (source excerpts).** `DavisKahan/Geometry/Polar/Section3Nonacute.lean` exposes the construction:

```lean
noncomputable def nonacuteDirectRotation
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    H →L[𝕜] H :=
  spectraCanonicalPolarFactor U V + crossedDefectQuarterTurn U V J
```

Here `≃ₗᵢ[𝕜]` is a linear isometric equivalence, not just an equality of abstract dimensions. The same module proves the exact existence criterion using the project's `IsDirectRotation` predicate:

```lean
theorem proposition3_2_completed :
    (∃ T : H →L[𝕜] H, IsDirectRotation U V T) ↔
      CrossedDefectsEquivalent U V := by
```

`DavisKahan/Geometry/Halmos/CrossedDefectGap.lean` handles the finite-dimensional specialization:

```lean
theorem crossedDefectsEquivalent_iff_finrank_eq
    (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    [FiniteDimensional 𝕜 (halmosSourceDefect U V)]
    [FiniteDimensional 𝕜 (halmosTargetDefect U V)] :
    CrossedDefectsEquivalent U V ↔
      Module.finrank 𝕜 (halmosSourceDefect U V)
        = Module.finrank 𝕜 (halmosTargetDefect U V) := by
```

The proof constructs the equivalence from orthonormal bases when ranks agree. `DavisKahan/Geometry/Halmos/CompactDefects.lean` proves both crossed defects are finite-dimensional if `P_U - P_V` is compact. This is a statement about compactness of the **difference** of projections; it should not be confused with the different compact cosine hypothesis used in the next lecture.

**Reconstruction exercise:** verify \(T_J^2=-I\), prove \(W_J^*W_J=I\), then use the integer-indexed basis example to show that an ordinary unitary transporter need not be a direct rotation.

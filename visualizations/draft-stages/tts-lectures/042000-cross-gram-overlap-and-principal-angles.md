# 042000 — Cross-Gram overlap and principal angles

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `017000` analysis and synthesis; `018000` Gram operators; `020000` orthonormal coordinate embeddings; `022000` overlap and Gram rigidity; `023000` rectangular Gram operators; `036000` singular-value decomposition. **Next:** sines, cosines, and cross projections.

<!-- BEGIN SPOKEN LECTURE -->

# How do we measure the angle between two subspaces?

You already know how to measure the angle between two nonzero vectors. Normalize them, take their inner product, and use the cosine to recover an angle.

But what if the objects we want to compare are entire subspaces? A plane contains infinitely many directions. In a higher-dimensional space, two planes can share one direction, disagree in another, and be perpendicular in yet another. One scalar angle cannot describe all of that.

Principal angles measure the relative geometry of two subspaces. Orthonormal frames, adjoints, Gram operators, and singular values make the construction explicit.

We will not start by assuming these angles exist. We will derive them.

## A vector's angle is a measurement of overlap

Begin with two unit vectors u and v in a real inner-product space. Their inner product is cosine of the angle between their oriented directions.

For lines rather than oriented vectors, flipping either vector changes the sign of the inner product but not the line. So the acute angle between the lines is determined by the absolute value of the inner product.

That distinction already hints at a general rule. When comparing subspaces, we should be measuring geometry that does not change just because we picked different orthonormal bases.

Suppose U and S are two subspaces of the same ambient Euclidean space. Choose an orthonormal basis for U and another for S.

Collect the first basis into a coordinate embedding V, and the second into a coordinate embedding W. The letters may sound abstract, but their roles are concrete: V takes a coordinate vector into U, and W takes a coordinate vector into the other subspace.

Each embedding preserves inner products, so V adjoint V and W adjoint W are identity operators on their respective coordinate spaces.

Now compose V adjoint with W. This gives a rectangular matrix C. Its entries are precisely the inner products between one basis vector of U and one basis vector of W. This is called the cross-Gram matrix, or the overlap matrix.

It is important not to confuse it with the ordinary Gram matrix of one frame. The ordinary Gram matrix of either orthonormal frame is the identity, regardless of where the subspace lies. The cross-Gram matrix records how the two frames sit relative to each other.

## The one-dimensional case

Let U be the horizontal axis in the plane. Let the second subspace be the line at forty-five degrees above the horizontal axis.

Choose a unit vector along each line. Their cross-Gram matrix has only one entry: cosine of forty-five degrees, which is one divided by the square root of two.

The singular value of a one-by-one matrix is the absolute value of its entry. So its singular value is also one divided by the square root of two.

Taking arccosine gives forty-five degrees. In this simplest case, the singular-value construction reproduces exactly the line angle we wanted.

But singular values are more general than absolute values of individual entries. They tell us how a rectangular map stretches carefully chosen orthogonal directions. That is why the same idea scales up to planes and higher-dimensional subspaces.

## Why singular values give basis-independent answers

Suppose we replace the orthonormal basis of U by a different orthonormal basis of the same subspace. This multiplies V on the right by an orthogonal matrix. Do the same for W, using another orthogonal matrix.

The overlap matrix changes, but only by multiplication on the left and right by orthogonal matrices.

Multiplication on the left or right by a unitary leaves the singular values unchanged, since it preserves the spectrum of the corresponding positive Gram operator. The singular values are intrinsic to the pair of subspaces, even though the entries of the overlap matrix are not.

Now we have a candidate definition. Take the singular values of the cross-Gram matrix, arranged from largest to smallest. For each one, apply arccosine. These are the principal angles, usually arranged from smallest to largest.

Why are we allowed to apply arccosine? Every singular value must lie between zero and one.

To prove that, start with a coordinate vector y for the second subspace. W preserves its length. V adjoint takes an ambient vector and reports its coordinates in U, which cannot increase its length because orthogonal projection cannot increase length.

Therefore the overlap map V adjoint W cannot increase length. Its operator norm is at most one, so none of its singular values exceeds one. Singular values are nonnegative by definition. The required range is proved.

Arccosine therefore produces numbers between zero and a right angle. No arbitrary orientation choices are left.

## A pair of planes in three dimensions

Consider the plane spanned by the first and second coordinate axes in three-dimensional space. Call it U.

Now consider a second plane containing the first coordinate axis, but tilted around that axis. We can describe it using the first axis together with a unit direction formed from cosine phi times the second axis plus sine phi times the third axis. Take phi between zero and ninety degrees.

Choose the natural orthonormal frames for these planes. The cross-Gram matrix is diagonal. Its first diagonal entry is one, because the planes share the first coordinate axis. Its second diagonal entry is cosine phi, because the remaining frame directions meet at angle phi.

The singular values are one and cosine phi. Their principal angles are therefore zero and phi.

Both pieces of information matter. The zero angle tells us the planes share a line. The other angle measures how much they tilt away from one another in the perpendicular directions.

This also explains a dimension-counting fact. Two two-dimensional planes in three-dimensional space must intersect in at least a line. Therefore at least one principal angle must be zero. Our construction discovers that geometric constraint automatically.

## Principal vectors and the singular-value decomposition

The singular values are only the beginning. The singular-value decomposition of the cross-Gram matrix gives two orthonormal coordinate bases, one on each side.

Use the coordinate embeddings to move those singular vectors back into the ambient space. We obtain pairs of unit vectors, one in the first subspace and one in the second.

Each matched pair has inner product equal to its singular value. Distinct matched pairs have zero cross-inner-product. In other words, after choosing the right orthonormal directions, the pattern of overlap becomes diagonal.

These matched directions are called principal vectors.

For the two tilted planes, the first pair can be the shared axis. The second pair consists of the remaining direction in each plane. Their angle is phi. There is no need to search among infinitely many possible coordinate choices once the singular-value decomposition has supplied the appropriate bases.

This gives a useful reconstruction strategy. First build the overlap matrix. Next take its singular-value decomposition. Finally interpret its left and right singular vectors as directions inside the two subspaces.

## Where the projection operator reappears

We can express the same construction without displaying both coordinate bases.

Let Q be orthogonal projection onto the second subspace. Because W has orthonormal columns, Q is W times W adjoint.

Take the cross-Gram matrix C, multiply it by its adjoint, and regroup the factors. We get V adjoint Q V.

This is a positive operator on the coordinate space of the first subspace. Its eigenvalues are the squares of the singular values of C. Therefore they are the squared cosines of the principal angles, together with any required zero padding on the first coordinate space.

That identity is important because it connects principal angles to projections, not to a particular pair of coordinate frames.

We can also replace Q with the projection onto the perpendicular complement of the second subspace. The corresponding Gram operator is identity minus V adjoint Q V. Its eigenvalues are one minus squared cosine, which equals squared sine.

So the overlap in the target subspace and the amount escaping into its perpendicular complement satisfy a Pythagorean relation, direction by direction.

Later the Davis–Kahan angle theorems will measure these sine quantities. For now, we are constructing them without discussing perturbations at all.

## What if the dimensions differ?

Suppose the first subspace has three dimensions and the second only two. The cross-Gram matrix is rectangular. Its usual principal-angle list has the smaller dimension's number of entries, which is two.

But there is another legitimate, directed convention. We can measure how each direction in the three-dimensional source projects into the two-dimensional target. Since that projection has a nontrivial kernel, at least one direction is perpendicular to the target. In an extended, source-indexed angle list, this appears as an additional ninety-degree angle.

The two conventions answer related but different questions. The shorter list pairs as many directions as the smaller subspace allows. The directed list also records unmatched source directions, which become important when the dimensions differ.

Principal-angle lists may use different conventions for unequal-dimensional subspaces. The number of recorded angles and the treatment of right-angle defects must be specified before comparing formulas.

## A final distinction

An angle of zero tells us that some direction lies in both subspaces. An angle of ninety degrees tells us that a direction of one subspace is perpendicular to the other. Angles strictly between those values describe genuine tilted pairs.

The list of principal angles tells us much more than a single worst-case angle. It can distinguish one badly aligned direction from many mildly misaligned directions. That difference will eventually matter when we use operator norms, Frobenius norms, and more general singular-value-based norms.

For your reconstruction exercise, take two planes in three dimensions that share an axis and meet at angle phi. Write down orthonormal frames, calculate their cross-Gram matrix, take its singular values, and recover zero and phi. Then multiply the overlap matrix by its adjoint and show that the resulting operator is the compression of the second plane's projection to the first plane.

The principal sines are the singular values of the complementary overlap. They turn subspace misalignment into a quantitative operator, rather than a choice of coordinate drawings.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

Let \(V:\mathbb K^p\to E\) and \(W:\mathbb K^q\to E\) be isometric embeddings with images \(U\) and \(S\). With \(C=V^*W\) and \(Q=WW^*=P_S\),
\[
0\le\sigma_i(C)\le1,\quad \theta_i=\arccos\sigma_i(C)\in[0,\pi/2],
\quad CC^*=V^*QV,
\quad V^*(I-Q)V=I-CC^*.
\]
For the ordinary min-dimension convention, there are \(\min(p,q)\) principal angles. A directed source-indexed convention can include extra right angles when \(p>q\); spell out the indexing convention before comparing angle lists. Under orthonormal frame changes \(V\mapsto VR\), \(W\mapsto WS\), \(C\mapsto R^*CS\); singular values are unchanged.

**Lean bridge.** In `ForTauCeti/Analysis/InnerProductSpace/AngleGeometry.lean`, the directed cosine map is tied explicitly to singular values of the projection map restricted to its source subspace:

```lean
theorem singularValues_cosThetaMap_comp_subtype (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ((U.cosThetaMap V).toLinearMap ∘ₗ U.subtype).singularValues =
      Submodule.principalCosines U V := by
  rw [singularValues_comp_subtype, cosThetaMap_comp_projection,
    Submodule.principalCosines_def, Submodule.cosThetaMap_def]
```

The companion theorem `singularValues_sinThetaMap_comp_subtype` identifies the source-restricted complementary projection with `Submodule.principalSines U V`. This is a *directed* operator representation; it need not package angles in the same way as the ordinary min-dimension cross-Gram list when subspace dimensions differ.

In `DavisKahan/FiniteDimensional/DirectRotation/PrincipalPlanes/Basic.lean`, the corresponding geometry is used to select concrete principal vectors:

```lean
noncomputable def principalSourceVector (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (i : Fin (nontrivialAngleCount U V)) : E :=
  LinearMap.rightSingularBasis ((U.sinThetaMap V).toLinearMap) (nontrivialAngleIndex U V i)
```

The mathematical bridge is: isometric frames give overlap matrices; singular values determine basis-independent angles; projection maps and their singular vectors give an intrinsic representation that the formalization can reuse. These declarations are copied from the available repository snapshot, not newly compiled code.

**Reconstruction:** Prove \(\|V^*W\|\le1\), derive \(CC^*=V^*P_SV\), construct principal vector pairs from an SVD, compute the two-plane example, and explain the difference between min-dimension and directed indexing.

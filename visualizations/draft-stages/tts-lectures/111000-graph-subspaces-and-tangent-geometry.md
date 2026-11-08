# 111000 — Graph subspaces and tangent geometry

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `043000–047000` sine/cosine geometry and acute pairs; `110000` the sine theorem. **Next:** `112000` the single-angle tangent theorem.

<!-- BEGIN SPOKEN LECTURE -->

# Graph subspaces and tangent geometry

The sine theorem controls how far trial vectors escape an exact subspace. The tangent theorem asks a more demanding question. Can we describe the entire trial subspace as a graph over the exact subspace, and control the slope of that graph?

The slope is an operator. Its singular values are tangents of principal angles. This viewpoint explains both the strength of tangent bounds and their breakdown as angles approach ninety degrees.

## Start with the geometry of a sloping line

In the plane, take the exact target subspace U to be the horizontal axis. A different line V through the origin is spanned by a vector with coordinates one and t, for some real number t.

Every vector in V has the form x in the horizontal direction plus t x in the vertical direction. We say V is the graph of the scalar map x goes to t x.

The angle theta between V and the horizontal axis has tangent equal to the absolute value of t. The cosine of theta is one divided by the square root of one plus t squared. The sine is the absolute value of t divided by that same square root.

If t equals one, the angle is forty-five degrees. If t is the square root of three, the angle is sixty degrees. As t becomes large, the line approaches vertical and theta approaches ninety degrees.

The graph representation fails exactly at the vertical line. No finite number t makes x equal to zero while leaving a nonzero vertical output. We can see geometrically why a tangent estimate needs a transversality assumption.

## Graphs over a Hilbert subspace

Now let H split orthogonally as U plus U perpendicular. Take a bounded linear map T from U into U perpendicular. Its graph is the collection of vectors x plus T x, for x in U.

The graph is a linear subspace. It is closed because T is bounded: if graph vectors converge, their U components converge, and continuity of T carries those components to the limiting complementary components.

The map that sends x to x plus T x is an injective coordinate map for the graph. It is generally not isometric. Its squared output length is the squared length of x plus the squared length of T x, by orthogonality.

In operator notation the Gram operator of the graph map is the identity plus T adjoint T. Its positive square root normalizes the graph coordinates.

Define an isometric graph frame E by first applying the inverse square root of the identity plus T adjoint T, and then sending x to x plus T x. The inverse square root exists because the positive operator identity plus T adjoint T is bounded below by the identity.

## Compute the graph sine and cosine

Project E onto U. Its horizontal component is the inverse square root of the identity plus T adjoint T. This is the cosine coordinate map C.

Project E onto U perpendicular. Its vertical component is T composed with that same inverse square root. This is the sine coordinate map S.

The positive cosine magnitude equals the inverse square root of the identity plus T adjoint T. The positive sine magnitude is the square root of T adjoint T times the inverse square root of the identity plus T adjoint T.

Why can the factors be rearranged in the sine formula? Both are functions of the same positive operator T adjoint T. Functional calculus makes them commute.

Let absolute value of T be the positive square root of T adjoint T. Then the formulas read: cosine magnitude equals one over the square root of one plus absolute value of T squared, and sine magnitude equals absolute value of T over that same denominator.

Divide the sine magnitude by the cosine magnitude. The denominator cancels, leaving absolute value of T. Thus the positive tangent operator of the graph is precisely the modulus of the graph slope.

For finite-dimensional U, the singular values of T are the tangents of the principal angles. In infinite dimensions we can formulate the same relation by functional calculus, without assuming the modulus has an eigenbasis.

## Recover the graph slope from a trial frame

Suppose instead we are given an isometric trial map E and want to know whether its range V is a graph over U.

Split E into C equals P_U E and S equals P_{U perpendicular} E. If C is invertible as a map from the trial-coordinate space onto U, then every trial vector has a unique horizontal component. Starting from a horizontal vector x, use C inverse to recover its trial coordinates, and then apply S to find the complementary component.

Therefore the graph slope is T equals S C inverse, with the natural identification of C as a map into U.

This formula looks like sine divided by cosine, and it is. But there is a qualification: if C is not onto U, V need not be a graph defined on all of U. And if its inverse is unbounded, the slope may not be a bounded operator.

For equal-dimensional finite-dimensional spaces, transversality with U perpendicular makes C injective and hence bijective. In infinite dimensions, injectivity alone need not imply a uniformly bounded inverse or surjectivity. A uniform acute-pair hypothesis such as a projection gap strictly below one supplies the stronger condition used in bounded graph theorems.

## Why right-angle directions obstruct a tangent

If V contains a nonzero vector lying in U perpendicular, its projection onto U is zero. Then C has a nontrivial kernel and cannot be inverted.

In terms of principal angles, there is a ninety-degree direction, with cosine zero. The corresponding tangent would require division by zero. A Moore–Penrose inverse can be used to define a totalized algebraic expression, but the resulting map should not be called an ordinary finite tangent on that direction.

This is why the source's finite-dimensional tangent theorem carries a transversality proof. The theorem first establishes that the cosine magnitude is injective. Only then may we identify the singular values of the coordinate tangent with the principal tangents.

The distinction also matters near, rather than exactly at, ninety degrees. Even when C is invertible, its inverse can be very large. Sine remains at most one, while tangent becomes arbitrarily large. A tangent theorem therefore yields more detailed graph control but is sensitive to the acute-pair condition.

## Compare two angles numerically

Take a line making thirty degrees with the horizontal axis. Its sine is one half, while its tangent is one divided by the square root of three, approximately zero point five seven seven.

At sixty degrees, the sine is the square root of three over two, approximately zero point eight six six. The tangent is the square root of three, approximately one point seven three two.

At eighty-nine degrees, the sine is already extremely close to one. But the tangent is roughly fifty-seven. A sine error bound near one reports that the trial line may be almost perpendicular. A tangent bound records just how steep its graph representation has become.

The tangent theorem will use an ordered gap and an adapted residual to control that slope. We should expect its hypotheses to be more structured than a generic geometric angle comparison.

## What a graph tells us beyond an angle

The graph operator gives an explicit way to reconstruct trial vectors from exact-subspace coordinates. If T is small, each trial vector x plus T x differs only slightly from its exact horizontal component.

The norm of T bounds that relative complementary error. The largest principal tangent measures the worst slope, while symmetric singular-value norms describe how slopes are distributed across directions.

This information is useful for perturbation theory because a graph can be manipulated algebraically. The invariance of a graph under a block operator leads to a Riccati equation, where the unknown is T. We will reach that connection after proving the single-angle tangent theorem.

Our next task is to show how the residual and a suitable ordered spectral gap control the graph slope. The sine theorem came from the complementary block X and a Sylvester estimate. The tangent theorem will add an invertible cosine component, then explain how the ordered gap pays for that inverse without losing the desired constant.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

For `H=U⊕Uᗮ` and bounded `T:U→Uᗮ`, the graph frame is `E=(I,T)(I+T*T)⁻¹ᐟ²`. Then `C=P_U E=(I+T*T)⁻¹ᐟ²`, `S=P_{Uᗮ}E=T(I+T*T)⁻¹ᐟ²`, and `|S|=|T|(I+|T|²)⁻¹ᐟ²`. Hence on the graph domain `tanΘ=|T|`. For a finite-dimensional trial isometry `X`, `tanThetaEmbedding U X` is the totalized map `sinThetaEmbedding U X ∘ moorePenroseInverse(cosThetaMagnitude U X)`; singular-value identification requires transversality.

### Source declaration excerpts

`DavisKahan/FiniteDimensional/Residual/AngleEmbeddings.lean` — `tanThetaEmbedding` (exact declaration header; body omitted):

```lean
noncomputable def tanThetaEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) : F →ₗ[𝕜] E :=
```

`DavisKahan/FiniteDimensional/Residual/AngleEmbeddings.lean` — `cosThetaMagnitude_injective_of_isTransverse` (exact declaration header; body omitted):

```lean
theorem cosThetaMagnitude_injective_of_isTransverse
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (X : F →ₗᵢ[𝕜] E)
    (htrans : Disjoint (approximateSubspace X) Uᗮ) :
    Function.Injective (cosThetaMagnitude U X) :=
```

`DavisKahan/FiniteDimensional/Residual/AngleEmbeddings.lean` — `graphOperator` (exact declaration header; body omitted):

```lean
noncomputable def graphOperator (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) : F →ₗ[𝕜] E :=
```

`DavisKahan/FiniteDimensional/Residual/AngleEmbeddings.lean` — `singularValues_graphOperator` (exact declaration header; body omitted):

```lean
theorem singularValues_graphOperator (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E)
    (htrans : Disjoint (approximateSubspace X) Uᗮ) :
    (graphOperator U X).singularValues =
      (approximateSubspace X).principalTangents U := by
```

**Mapping.** `cosThetaMagnitude_injective_of_isTransverse` converts disjointness with `Uᗮ` into the injectivity needed for the tangent interpretation. `graphOperator` is the source's trial-coordinate tangent representative, and `singularValues_graphOperator` proves its singular values equal the directed principal tangents under transversality. The finite-dimensional graph operator's input is a trial-coordinate space, so it must not be conflated with a map from all of `U` to `Uᗮ` without the additional identification `C⁻¹`.

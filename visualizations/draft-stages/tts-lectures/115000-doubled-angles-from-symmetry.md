# 115000 — Doubled angles from symmetry

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `042000–045000` principal angles, CS blocks, and projections; `114000` block reflections. **Next:** `116000` the sine-two-theta theorem.

<!-- BEGIN SPOKEN LECTURE -->

# Doubled angles from symmetry

Reflecting across a closed subspace means acting by plus one on that subspace and minus one on its orthogonal complement. Conjugation by this reflection reverses the off-diagonal blocks of an operator. Applied to another subspace, the same reflection produces an angle-doubling identity.

For one line in the plane, the answer is straightforward: reflection across a line at angle theta sends the horizontal axis to a line at angle twice theta. Our task is to express that fact through orthogonal projections, then extend it to many principal-angle planes and even to a Hilbert space without a discrete principal-vector basis.

## Reflect the horizontal axis across a tilted line

Start in the real plane. Let U be the horizontal axis. Let V be the line making an angle theta counterclockwise from U, with theta between zero and ninety degrees.

A reflection across V fixes the vectors along V and reverses the perpendicular vectors. We can derive its matrix by choosing the unit vector v with coordinates cosine theta and sine theta.

Projection onto V is the rank-one matrix formed from v times its transpose. Its entries are cosine squared theta, sine theta cosine theta, and sine squared theta in the familiar symmetric pattern.

The reflection is twice that projection minus the identity. Using the double-angle identities, its matrix has first row cosine twice theta and sine twice theta, and second row sine twice theta and negative cosine twice theta.

Apply this reflection to the horizontal unit vector. The result has coordinates cosine twice theta and sine twice theta. Therefore the reflected line has oriented angle twice theta relative to U.

The ordinary acute angle between two unoriented lines may fold back after ninety degrees, but the magnitude of the sine of that angle remains the magnitude of sine twice theta. Because theta lies between zero and ninety degrees, sine twice theta is nonnegative.

## Turn the geometry into a difference of projections

Let P be the orthogonal projection onto U, and let J be reflection through V. The projection onto the reflected subspace J U is J P J, because J is an isometry and its inverse equals itself.

Define the projection difference D equal to J P J minus P. It is self-adjoint. In the two-dimensional principal plane, the eigenvalues of D are plus sine twice theta and minus sine twice theta.

One way to see this without solving a characteristic polynomial is to square D. Direct multiplication using the reflection matrix gives D squared equal to sine squared twice theta times the identity.

The modulus of D is the positive square root of D squared. It therefore equals sine twice theta times the identity on that principal plane.

So the positive operator that measures sine twice the angle is precisely the modulus of the displacement of P under reflection through V.

This identity is more informative than a statement about maximum angles. It identifies an actual operator, and therefore determines every singular value and every unitarily invariant norm.

## Repeat the calculation using a cosine–sine block

In a principal plane for two subspaces U and V, the projection P onto U has matrix with one on the first diagonal entry and zero on the second.

The projection Q onto V has entries cosine squared theta, sine theta cosine theta in the two off-diagonal positions, and sine squared theta.

The reflection J equals twice Q minus the identity. Multiply J P J. The resulting projection is the one onto the line spanned by the vector with coordinates cosine twice theta and sine twice theta.

The eigenvalues of the difference J P J minus P are therefore plus and minus sine twice theta. This verifies the reflection identity directly from the cosine–sine decomposition.

An orthogonal direct sum of principal planes repeats this calculation independently. On each plane, the positive modulus contributes sine twice the corresponding principal angle. Degenerate intersection and perpendicular blocks contribute zero.

The full-space operator has repeated singular values on each nontrivial principal plane. A directed coordinate block may record each principal angle only once. We must keep these conventions distinct when comparing Frobenius or nuclear norms.

## A coordinate-free operator identity

The same result can be proved without choosing a principal-vector basis.

Let S be the positive sine-angle operator, the modulus of P minus Q. Its spectrum lies between zero and one. The positive angle operator Theta can be defined by applying arcsine to S.

Now apply the scalar function sine of twice the angle to Theta. Since the spectrum of Theta lies between zero and pi over two, this produces a positive operator.

The scalar identity says that sine squared of twice theta equals four times sine squared theta times one minus sine squared theta.

On the operator side, the square of the sine-two-theta operator is therefore four times S squared minus four times S to the fourth power. The two factors commute because both are functions of S.

Independently, expand the square of J P J minus P using only P squared equals P, Q squared equals Q, and their self-adjointness. Its square is exactly the same polynomial in S.

Both the sine-two-theta operator and the modulus of the projection difference are positive. They have the same square. By uniqueness of the positive square root, they are equal.

This is the coordinate-free reflection double-angle identity. The functional-calculus identity applies in the complex Hilbert-space setting, with corresponding real formulations.

## Check the two extreme angles

If theta is zero, U and V coincide. Reflection through V leaves U unchanged, so the displaced projection is zero. Sine of zero is zero, as expected.

If theta is ninety degrees, V is perpendicular to U. Reflection through V sends a vector of U to its negative, which spans the same line U. Again the displaced projection is zero. Sine of one hundred eighty degrees is zero.

At forty-five degrees, the reflected horizontal line is vertical. The projection difference has norm one, and sine twice theta equals one.

The three tests show that the doubled sine is not a monotone measure of the original angle across the entire interval from zero to ninety degrees. It increases up to forty-five degrees, then decreases.

This branch ambiguity will be crucial when we interpret perturbation estimates. A small doubled sine may mean that two subspaces are nearly equal, but it may also mean that they are nearly perpendicular.

## Why reflection helps a perturbation theorem

Suppose T is self-adjoint and U reduces T. Suppose S equals T plus H, and V reduces S. Reflection through V commutes with S, even though it need not commute with T.

The mirror defect J V T J V minus T equals H minus J V H J V. Its norm is at most twice the norm of H in any compatible unitarily invariant norm.

The reflected operator J V T J V has a reducing subspace J V U, because U reduces T. We can now apply a single-angle sine comparison to T and its reflected copy, provided the spectral separation hypotheses match.

But the angle between U and the reflected U is encoded by the sine-two-theta operator we have just constructed. Thus reflection converts a doubled-angle question for U and V into a single-angle question for a reflected pair.

The algebra explains both the doubled angle and the factor of two in the perturbation norm. Neither is an arbitrary feature of the statement.

## What to retain

The key geometric identity is: positive sine of twice the operator angle equals the modulus of the difference between the projection onto U and the projection onto U reflected through V.

It works across the full angle range, including right angles, because the sine is nonnegative on twice that range. It does not, by itself, choose the near-zero branch.

The outcome is the sine-two-theta theorem, with a bound valid even when the permitted geometry has not yet identified which branch of the doubled sine is relevant.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

Let `P=P_U`, `Q=P_V`, `J_V=2Q-I`, and `Θ=arcsin |P-Q|` (ambient positive angle). The operator identity is

\[\sin(2\Theta)=|J_V P J_V-P|=|P_{J_VU}-P_U|.\]

In each nondegenerate principal plane, `|J_V P J_V-P| = sin(2θ) I`. In ambient coordinates, every plane contributes twice to the singular-value list; a directed sine block generally contributes once. For `θ∈[0,π/2]`, `sin(2θ)≥0` but is not injective as a function of `θ`.

### Source declaration excerpts

`DavisKahan/Geometry/Angle/DoubleAngleFunctionalCalculus.lean` — `sinTwoAngleOperatorC` (exact declaration header; body omitted):

```lean
noncomputable def sinTwoAngleOperatorC (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[ℂ] E :=
```

`DavisKahan/Geometry/Angle/DoubleAngleFunctionalCalculus.lean` — `starProjection_map_reflection_eq` (exact declaration header; body omitted):

```lean
theorem starProjection_map_reflection_eq (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    (U.map (V.reflection.toLinearEquiv : E →ₗ[ℂ] E)).starProjection =
      V.reflectionOperator * U.starProjection * V.reflectionOperator := by
```

`DavisKahan/Geometry/Angle/DoubleAngleFunctionalCalculus.lean` — `directedSinTwoAngleOperatorC_eq_modulus_reflect` (exact declaration header; body omitted):

```lean
theorem directedSinTwoAngleOperatorC_eq_modulus_reflect :
    sinTwoAngleOperatorC U V =
      (V.reflectionOperator * U.starProjection * V.reflectionOperator -
        U.starProjection).modulus := by
```

**Mapping.** `sinTwoAngleOperatorC` uses functional calculus on the ambient positive angle; `starProjection_map_reflection_eq` expresses projection conjugation; `directedSinTwoAngleOperatorC_eq_modulus_reflect` identifies the full positive doubled-sine operator, not merely its operator norm. The formal theorem's types and complete Hilbert-space assumptions are retained in the excerpts.

# 116000 — The sine-two-theta theorem

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `110000` the sine theorem, `114000` block reflection, `115000` doubled-angle identity. **Next:** `117000` the tangent-two-theta theorem.

<!-- BEGIN SPOKEN LECTURE -->

# The sine-two-theta theorem

We have all the ingredients for the sine-two-theta theorem: a two-block spectral gap, a reflection identity for doubled angles, and a bound on the mirror defect of an operator under that reflection.

The conclusion says that the gap times the sine of twice the subspace angle is at most twice the perturbation size. We will derive this estimate carefully, and then explain what it can and cannot tell us about the original angle.

## Set up the operators and reducing subspaces

Work first in a finite-dimensional real or complex inner-product space. Let T be self-adjoint, and let U be a reducing subspace for T.

Assume there are real numbers a and b, with a less than b, such that T is at least b in quadratic-form order on U and at most a on U perpendicular. This places its two diagonal blocks on opposite sides of an ordered gap delta equal to b minus a.

Now perturb T to another self-adjoint operator S equal to T plus H. Choose a reducing subspace V for S. At this stage, we do not need to assume that H is off-diagonal relative to U.

The theorem bounds the ambient positive sine-two-theta operator between U and V, measured in any supported unitarily invariant norm, by twice the norm of H divided by delta.

Notice what is not in the hypotheses. V need not have been described as the graph of a small operator. We have not assumed the principal angles are below forty-five degrees. The theorem's conclusion uses a function of the angle that makes sense over the entire interval from zero to ninety degrees.

## Reflect through the perturbed reducing space

Let J be the reflection through V, equal to twice its orthogonal projection minus the identity.

Because V reduces S and S is self-adjoint, J commutes with S. Thus J S J equals S.

Replace S by T plus H. We obtain J T J plus J H J equals T plus H. Rearranging gives J T J minus T equal to H minus J H J.

The norm of J H J equals the norm of H in every unitarily invariant norm because J is unitary. The triangle inequality therefore yields that the norm of J T J minus T is at most twice the norm of H.

This is the mirror defect bound. It is the only place where the perturbation appears on the right side of our proof.

## What is the reflected spectral subspace?

Define T prime as J T J. Since J is an isometry and U reduces T, the reflected subspace J U also reduces T prime. The reflected complement J U perpendicular reduces T prime as well.

Furthermore, the quadratic-form spectral bounds are preserved by this unitary conjugation. T prime has the same upper and lower block spectra as T, merely transported by J.

Thus the single-angle sine theorem can be applied to a suitable crossed pair of reducing subspaces: one belonging to T and the other to T prime. One block lies above b, the other below a, so the gap remains delta.

The resulting cross-projection norm is bounded by the norm of T prime minus T divided by delta.

Which cross projection do we obtain? Project from U onto the reflected perpendicular subspace J U perpendicular. In a principal plane, that projection has magnitude sine twice theta, where theta is the angle between U and V.

This is exactly the reflected overlap given by composing the reflected projections. The relevant ambient positive operator, after matching the polar and singular-value representations, is sine of twice the angle operator.

## Put the two inequalities together

The single-angle theorem for the reflected pair yields delta times the norm of sine two theta at most the norm of the mirror defect J T J minus T.

The mirror defect bound yields that this norm is at most twice the norm of H.

Combining them gives the result: delta times the unitarily invariant norm of sine two theta is at most two times the unitarily invariant norm of the perturbation.

For operator norm, this controls the largest value of sine twice a principal angle, not necessarily twice the largest angle itself. For a Frobenius or Ky Fan norm, we must account for the complete singular-value list of the ambient angle operator. The formal theorem does so through the full-space angle representation and the corresponding unitarily invariant norm.

This norm inequality is stated for finite-dimensional unitarily invariant seminorms. In infinite-dimensional symmetric ideals the same conclusion requires the appropriate membership, domain, and spectral-separation hypotheses.

## Examine a two-by-two perturbation

Take the real plane with T diagonal, having entries negative one and one. Choose U to be the upper eigenspace, the vertical line. Then the quadratic-form gap is two.

Let H be symmetric with zero diagonal and off-diagonal entries h. The perturbed operator S has rows negative one, h and h, one.

The upper eigenvector of S rotates away from the vertical line through an angle theta satisfying tangent twice theta equals h. For now, recall the equivalent relation: sine twice theta equals the absolute value of h divided by the square root of one plus h squared.

The sine-two-theta inequality reads two times sine twice theta at most twice times the absolute value of h. This holds because the square root of one plus h squared is at least one.

For small h, the ratio between the two sides approaches one. Thus the factor two in this normalization cannot be uniformly reduced in the perturbation theorem even though equality need not hold for a nonzero finite h.

At h equal to one, theta equals twenty-two point five degrees. Sine twice theta is the square root of two divided by two. The left side is the square root of two and the right side is two.

As the coupling becomes larger, theta approaches forty-five degrees and sine twice theta approaches one. The estimate becomes less restrictive, because its right-hand side grows without bound.

## A different example shows the branch ambiguity

Take two perpendicular lines U and V in the same plane. Their principal angle is ninety degrees. Sine twice that angle is zero.

So the doubled-sine operator vanishes even though the projection difference has norm one, the maximum possible value.

The theorem therefore cannot by itself certify that V is close to U. A small right-hand side may indicate closeness, but without information selecting the relevant branch, the same small doubled sine is consistent with an almost perpendicular pair.

This is a statement about the information carried by the left-hand side, not a defect in the proof. The function sine twice theta loses the distinction between angles near zero and angles near ninety degrees.

Later spectral-selection results will supply conditions that choose the intended branch.

## Compare with the single-angle sine theorem

The single-angle sine theorem typically uses a residual and a gap between a trial operator and the unwanted exact spectrum. Its angle is directed from the trial space toward the exact subspace.

The sine-two-theta theorem uses a two-block form gap for one exact operator and a perturbation difference between two self-adjoint operators. Its angle is the ambient angle between two reducing subspaces.

The formulas can look similar, but their inputs are different. One cannot simply substitute a residual in place of the full perturbation or replace the two-block gap with an arbitrary pairwise distance.

In the special off-diagonal setting, the two-block structure has an additional consequence: it prevents the selected spectral subspace from rotating beyond forty-five degrees. That extra information makes it possible to divide the doubled sine by a positive doubled cosine and obtain a tangent theorem.

## The theorem we have proved

We began with a self-adjoint T whose reducing subspace U lies on one side of a form gap, and a self-adjoint perturbation S with reducing subspace V. Reflection through V turned T into a nearby operator with a reflected reducing subspace. The ordinary sine theorem controlled that reflected overlap. The reflection identity identified it with the sine of twice the original angle.

The result has a clean constant and accommodates arbitrary angles, but it does not select the near-zero branch.

The maximal angle will stay strictly below forty-five degrees, and the stronger tangent of twice the angle will have its own sharp estimate.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

For finite-dimensional self-adjoint `T,S`, `H=S-T`, reducing `U` of `T` and reducing `V` of `S`, and a two-block form gap `T|U ≥ b`, `T|Uᗮ ≤ a` (`δ=b-a>0`), the canonical ambient theorem is

\[(b-a)\,N(\sin(2\Theta(U,V)))\le 2N(S-T).\]

Let `J=J_V`. Because `J S J=S`, `J T J-T=H-JHJ`, whence `N(J T J-T)≤2N(H)`. Applying the cross-subspace sine comparison to `T` and `J T J` and identifying `|J P_U J-P_U|=sin(2Θ)` supplies the conclusion. No off-diagonal hypothesis on `H` is required. The full ambient-angle norm and directed coordinate norms should not be silently interchanged.

### Source declaration excerpts

`DavisKahan/FiniteDimensional/DoubleAngle/SinTheta.lean` — `sin_two_theta_reflection_le` (exact declaration header; body omitted):

```lean
theorem sin_two_theta_reflection_le (N : UnitarilyInvariantSeminorm 𝕜 E E)
    (hT : T.IsSymmetric) {U W : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (hUinv : ∀ x ∈ U, T x ∈ U) {a b : ℝ} (hab : a < b)
    (hUb : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_𝕜)
    (hUa : ∀ x ∈ Uᗮ, RCLike.re ⟪T x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2) :
    2 * N ((Uᗮ.starProjection ∘L W.starProjection ∘L U.starProjection
        : E →L[𝕜] E) : E →ₗ[𝕜] E)
      ≤ N (W.reflection.toLinearMap ∘ₗ T ∘ₗ W.reflection.toLinearMap - T)
        / (b - a) := by
```

`DavisKahan/FiniteDimensional/DoubleAngle/SinTheta.lean` — `sinTwoTheta_perturbation_le` (exact declaration header; body omitted):

```lean
theorem sinTwoTheta_perturbation_le
    (N : UnitarilyInvariantSeminorm 𝕜 E E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : (U ∈ Module.End.invtSubmodule A)) (hV : (V ∈
        Module.End.invtSubmodule B))
    {a b : ℝ} (_hab : a < b) (hgap : TwoBlockFormGap A U a b) :
    (b - a) * N ((U.sinTwoAngleOperator V).toLinearMap) ≤ 2 * N (B - A) := by
```

`DavisKahan/FiniteDimensional/DoubleAngle/SinTheta.lean` — `opNorm_sinTwoTheta_le` (exact declaration header; body omitted):

```lean
theorem opNorm_sinTwoTheta_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : (U ∈ Module.End.invtSubmodule A)) (hV : (V ∈
        Module.End.invtSubmodule B))
    {a b : ℝ} (hab : a < b) (hgap : TwoBlockFormGap A U a b) :
    (b - a) * ‖(U.sinTwoAngleOperator V)‖ ≤
      2 * ‖(B - A).toContinuousLinearMap‖ := by
```

**Mapping.** `sinTwoTheta_perturbation_le` is the finite-dimensional every-UI-norm statement for reducing `U,V`; `sin_two_theta_reflection_le` is the mirror-defect intermediate result. The `opNorm` specialization records the usual maximum singular-angle bound. `TwoBlockFormGap` encodes a form-order gap on both exact blocks rather than a generic distance between two unordered spectral sets.

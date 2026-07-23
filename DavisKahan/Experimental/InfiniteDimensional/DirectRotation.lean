/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import DavisKahan.Experimental.InfiniteDimensional.GraphSubspace
import DavisKahan.Experimental.InfiniteDimensional.DoubleAngle

/-!
# Infinite-dimensional direct rotations

Literature writeup: local TeX, Section 25.  The direct rotation is the
canonical unitary transporting one acute closed subspace to another.
-/


/-! ## Construction plan

Define `directRotation U V` as the unitary polar factor of
`Q P + Qperp Pperp` under the acute hypothesis.  First prove the positive
factor is invertible, then prove the polar factor maps `U` onto `V` and
intertwines the projections.  The symmetry, square, minimality, and
trigonometric formulas should be consequences of uniqueness of the acute
unitary and the operator-angle functional calculus, not separate choices.
-/


/-! ## Weak-agent execution plan: bounded direct rotation

Let `P,Q` be the two orthogonal projections and
`S := QP + QᗮPᗮ`.  Prove acuteness makes `S` bounded below, hence invertible.
Define the direct rotation as the unitary polar factor
`S (S* S)^(-1/2)`.  Add named lemmas for:

* `S P = Q S`;
* `S* S` commutes with `P`;
* the inverse square root commutes with `P`;
* the polar factor intertwines `P,Q`;
* reversal of the pair takes adjoints.

Prove mapping and square identities before any extremality theorem.  For the
operator-norm minimizer, reduce to the Halmos generic two-projection block and
prove the scalar fiber inequality.  Do not generalize that result to arbitrary
symmetric ideals without a separate majorization theorem.
-/

namespace ForMathlib
namespace DavisKahanExt

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-! ## Canonical intertwiner and its polar data

`operatorAbsoluteValue` is the leaf-defined absolute value from
`SinTheta/General`.  The invertibility of the intertwiner and of its absolute
value on acute pairs, the commutation of the absolute value with the
projection, and the Halmos two-projection decomposition are the genuinely
missing polar-campaign ingredients; they are isolated as leaf obligations.
-/

/-- The canonical intertwiner `S = P_V P_U + P_{Vᗮ} P_{Uᗮ}`. -/
noncomputable def canonicalIntertwiner (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[𝕜] E :=
  projection V ∘L projection U +
    complementaryProjection V ∘L complementaryProjection U

/-- **Leaf obligation.** The square of the absolute value is `S⋆S`. -/
theorem operatorAbsoluteValue_sq (S : E →L[𝕜] E) :
    operatorAbsoluteValue S ∘L operatorAbsoluteValue S = star S ∘L S :=
  sorry

/-- **Leaf obligation.** The absolute value is self-adjoint. -/
theorem operatorAbsoluteValue_isSelfAdjoint (S : E →L[𝕜] E) :
    IsSelfAdjoint (operatorAbsoluteValue S) :=
  sorry

/-- **Leaf obligation.** On an acute pair the canonical intertwiner is a unit:
`S⋆S` is bounded below by a positive scalar. -/
noncomputable def canonicalIntertwinerUnit (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (_hacute : IsAcute U V) : (E →L[𝕜] E)ˣ :=
  sorry

/-- **Leaf obligation.** The intertwiner unit carries the canonical
intertwiner. -/
theorem coe_canonicalIntertwinerUnit (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    ((canonicalIntertwinerUnit U V hacute : (E →L[𝕜] E)ˣ) : E →L[𝕜] E) =
      canonicalIntertwiner U V :=
  sorry

/-- **Leaf obligation.** On an acute pair the absolute value of the canonical
intertwiner is a unit. -/
noncomputable def canonicalAbsoluteValueUnit (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (_hacute : IsAcute U V) : (E →L[𝕜] E)ˣ :=
  sorry

/-- **Leaf obligation.** The absolute-value unit carries the absolute value of
the canonical intertwiner. -/
theorem coe_canonicalAbsoluteValueUnit (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    ((canonicalAbsoluteValueUnit U V hacute : (E →L[𝕜] E)ˣ) : E →L[𝕜] E) =
      operatorAbsoluteValue (canonicalIntertwiner U V) :=
  sorry

/-- **Leaf obligation.** The absolute value of the canonical intertwiner
commutes with the source projection (via `S⋆S P = P S⋆S` and the functional
calculus). -/
theorem canonicalAbsoluteValue_commutes_projection (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    Commute (operatorAbsoluteValue (canonicalIntertwiner U V))
      (projection U) :=
  sorry

/-- The canonical intertwiner carries the source projection to the target
projection: `S P_U = P_V S`. -/
theorem canonicalIntertwiner_intertwines (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    canonicalIntertwiner U V ∘L projection U =
      projection V ∘L canonicalIntertwiner U V := by
  ext x
  have hPP : U.starProjection (U.starProjection x) = U.starProjection x :=
    U.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem x)
  have hP'P : Uᗮ.starProjection (U.starProjection x) = 0 := by
    rw [Submodule.starProjection_apply_eq_zero_iff]
    exact Submodule.le_orthogonal_orthogonal U (U.starProjection_apply_mem x)
  have hQQ : V.starProjection (V.starProjection (U.starProjection x)) =
      V.starProjection (U.starProjection x) :=
    V.starProjection_eq_self_iff.mpr (V.starProjection_apply_mem _)
  have hQQ' : V.starProjection
      (Vᗮ.starProjection (Uᗮ.starProjection x)) = 0 := by
    rw [Submodule.starProjection_apply_eq_zero_iff]
    exact Vᗮ.starProjection_apply_mem _
  simp only [canonicalIntertwiner, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, map_add]
  simp only [projection, complementaryProjection] at *
  rw [hPP, hP'P, map_zero, add_zero, hQQ, hQQ']
  rw [add_zero]

/-- Canonical direct rotation.

Construction strategy: set

`S = P_V P_U + P_{Vᗮ} P_{Uᗮ}`.

For an acute pair, prove `S* S` is bounded below by a positive scalar.  Define
the direct rotation as the polar factor `S (S* S)^{-1/2}` using continuous
functional calculus.  This construction automatically yields a unitary that
intertwines the two projections and is stable under finite specialization. -/
noncomputable def directRotation (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) : E →L[𝕜] E :=
  canonicalIntertwiner U V ∘L
    (↑(canonicalAbsoluteValueUnit U V hacute)⁻¹ : E →L[𝕜] E)

/-- A bounded operator with two-sided star inverse is unitary. -/
private theorem isUnitaryOperator_of_star_identities
    {W : E →L[𝕜] E}
    (hleft : star W ∘L W = 1) (hright : W ∘L star W = 1) :
    IsUnitaryOperator W := by
  constructor
  · intro x
    have happ := congrArg (fun T : E →L[𝕜] E => T x) hleft
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.one_apply] at happ
    have hinner : ⟪W x, W x⟫_𝕜 = ⟪x, x⟫_𝕜 := by
      calc ⟪W x, W x⟫_𝕜
          = ⟪star W (W x), x⟫_𝕜 := by
            rw [ContinuousLinearMap.star_eq_adjoint,
              ContinuousLinearMap.adjoint_inner_left]
        _ = ⟪x, x⟫_𝕜 := by rw [happ]
    have hsq : ‖W x‖ ^ 2 = ‖x‖ ^ 2 := by
      have h1 := congrArg RCLike.re hinner
      rwa [inner_self_eq_norm_sq, inner_self_eq_norm_sq] at h1
    nlinarith [norm_nonneg (W x), norm_nonneg x, hsq,
      sq_nonneg (‖W x‖ - ‖x‖), sq_nonneg (‖W x‖ + ‖x‖)]
  · intro y
    refine ⟨star W y, ?_⟩
    have happ := congrArg (fun T : E →L[𝕜] E => T y) hright
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.one_apply] using happ

/-- The direct rotation is unitary. 

Lean proof route for a weaker agent:

1. For `S = QP+(I-Q)(I-P)`, show acuteness makes `S*S` bounded below and invertible.
2. Define the polar factor `W=S(S*S)^{-1/2}` and compute `W*W=I`.
3. Prove surjectivity from invertibility or similarly compute `WW*=I`.
4. Translate those identities to `IsUnitaryOperator`.


Ext-agent signature audit (GPT 5.6 High): Correct for acute pairs using the polar factor
of the canonical intertwiner.

Preferred dependency route: Construct the polar factor of `QP + QᗮPᗮ`; prove
intertwining before extremality, and use the Halmos decomposition only for the final
minimization theorem.
-/
theorem directRotation_unitary
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hacute : IsAcute U V) :
    IsUnitaryOperator (directRotation U V hacute) := by
  classical
  set S : E →L[𝕜] E := canonicalIntertwiner U V with hS
  set B : E →L[𝕜] E :=
    (↑(canonicalAbsoluteValueUnit U V hacute)⁻¹ : E →L[𝕜] E) with hB
  have hsq' : operatorAbsoluteValue S * operatorAbsoluteValue S =
      star S * S := operatorAbsoluteValue_sq S
  have hAself : star (operatorAbsoluteValue S) = operatorAbsoluteValue S :=
    (operatorAbsoluteValue_isSelfAdjoint S).star_eq
  have hAB : operatorAbsoluteValue S * B = 1 := by
    have h := (canonicalAbsoluteValueUnit U V hacute).mul_inv
    rwa [coe_canonicalAbsoluteValueUnit] at h
  have hBA : B * operatorAbsoluteValue S = 1 := by
    have h := (canonicalAbsoluteValueUnit U V hacute).inv_mul
    rwa [coe_canonicalAbsoluteValueUnit] at h
  have hstarB : star B = B := by
    have h1 : star B * operatorAbsoluteValue S = 1 := by
      have h := congrArg star hAB
      rwa [star_mul, hAself, star_one] at h
    calc star B = star B * (operatorAbsoluteValue S * B) := by
          rw [hAB, mul_one]
      _ = (star B * operatorAbsoluteValue S) * B := by rw [mul_assoc]
      _ = B := by rw [h1, one_mul]
  have hleft : star (directRotation U V hacute) ∘L
      directRotation U V hacute = 1 := by
    show star (S * B) * (S * B) = 1
    calc star (S * B) * (S * B)
        = star B * (star S * S) * B := by rw [star_mul]; noncomm_ring
      _ = star B * (operatorAbsoluteValue S * operatorAbsoluteValue S) *
            B := by rw [hsq']
      _ = B * (operatorAbsoluteValue S * operatorAbsoluteValue S) * B := by
          rw [hstarB]
      _ = (B * operatorAbsoluteValue S) * (operatorAbsoluteValue S * B) := by
          noncomm_ring
      _ = 1 := by rw [hBA, hAB, one_mul]
  have hunit : IsUnit (directRotation U V hacute) := by
    have h1 : IsUnit S := by
      rw [hS, ← coe_canonicalIntertwinerUnit U V hacute]
      exact (canonicalIntertwinerUnit U V hacute).isUnit
    have h2 : IsUnit B := by
      rw [hB]
      exact ((canonicalAbsoluteValueUnit U V hacute)⁻¹).isUnit
    exact h1.mul h2
  have hright : directRotation U V hacute ∘L
      star (directRotation U V hacute) = 1 := by
    have hinvW : star (directRotation U V hacute) = ↑hunit.unit⁻¹ := by
      have h1 : star (directRotation U V hacute) * ↑hunit.unit = 1 := by
        rw [hunit.unit_spec]
        exact hleft
      calc star (directRotation U V hacute)
          = star (directRotation U V hacute) *
              (↑hunit.unit * ↑hunit.unit⁻¹) := by
            rw [hunit.unit.mul_inv, mul_one]
        _ = (star (directRotation U V hacute) * ↑hunit.unit) *
              ↑hunit.unit⁻¹ := by rw [mul_assoc]
        _ = ↑hunit.unit⁻¹ := by rw [h1, one_mul]
    show directRotation U V hacute * star (directRotation U V hacute) = 1
    rw [hinvW]
    have h := hunit.unit.mul_inv
    rwa [hunit.unit_spec] at h
  exact isUnitaryOperator_of_star_identities hleft hright

/-- Intertwining of orthogonal projections. 

Lean proof route for a weaker agent:

1. Unfold the polar-factor construction of `directRotation`.
2. Prove the pre-polar operator `S = QP+(I-Q)(I-P)` satisfies `S P = Q S`.
3. Show `S*S` commutes with `P`; functional calculus then gives commutation of its inverse square root.
4. Reassemble to obtain `W P = Q W`.


Ext-agent signature audit (GPT 5.6 High): Correct; this is the foundational
direct-rotation theorem and should be proved before the range and square formulas.

Preferred dependency route: Construct the polar factor of `QP + QᗮPᗮ`; prove
intertwining before extremality, and use the Halmos decomposition only for the final
minimization theorem.
-/
theorem directRotation_intertwines
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hacute : IsAcute U V) :
    directRotation U V hacute ∘L projection U =
      projection V ∘L directRotation U V hacute := by
  have hS := canonicalIntertwiner_intertwines U V
  have hA := canonicalAbsoluteValue_commutes_projection U V
  have hAinv : Commute
      (↑(canonicalAbsoluteValueUnit U V hacute)⁻¹ : E →L[𝕜] E)
      (projection U) := by
    have hAu : Commute
        ((canonicalAbsoluteValueUnit U V hacute : (E →L[𝕜] E)ˣ) : E →L[𝕜] E)
        (projection U) := by
      rw [coe_canonicalAbsoluteValueUnit]
      exact hA
    exact hAu.units_inv_left
  ext x
  show canonicalIntertwiner U V
      ((↑(canonicalAbsoluteValueUnit U V hacute)⁻¹ : E →L[𝕜] E)
        (projection U x)) =
    projection V (canonicalIntertwiner U V
      ((↑(canonicalAbsoluteValueUnit U V hacute)⁻¹ : E →L[𝕜] E) x))
  have h1 : (↑(canonicalAbsoluteValueUnit U V hacute)⁻¹ : E →L[𝕜] E)
      (projection U x) = projection U
        ((↑(canonicalAbsoluteValueUnit U V hacute)⁻¹ : E →L[𝕜] E) x) := by
    have h := congrArg (fun T : E →L[𝕜] E => T x) hAinv.eq
    simpa only [ContinuousLinearMap.mul_apply] using h
  have h2 : canonicalIntertwiner U V (projection U
      ((↑(canonicalAbsoluteValueUnit U V hacute)⁻¹ : E →L[𝕜] E) x)) =
    projection V (canonicalIntertwiner U V
      ((↑(canonicalAbsoluteValueUnit U V hacute)⁻¹ : E →L[𝕜] E) x)) := by
    have h := congrArg (fun T : E →L[𝕜] E => T
      ((↑(canonicalAbsoluteValueUnit U V hacute)⁻¹ : E →L[𝕜] E) x)) hS
    simpa only [ContinuousLinearMap.comp_apply] using h
  rw [h1, h2]

/-- The direct rotation maps one subspace onto the other. 

Lean proof route for a weaker agent:

1. Convert the intertwining identity into inclusion of `U.map W` in `V`.
2. Use unitarity/surjectivity to compare orthogonal complements or apply the inverse rotation for the reverse inclusion.
3. Conclude equality of submodules by antisymmetry.


Ext-agent signature audit (GPT 5.6 High): Correct and should be derived from projection
intertwining plus unitarity, not from basis choices.

Preferred dependency route: Construct the polar factor of `QP + QᗮPᗮ`; prove
intertwining before extremality, and use the Halmos decomposition only for the final
minimization theorem.
-/
theorem directRotation_maps_subspace
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hacute : IsAcute U V) :
    U.map (directRotation U V hacute).toLinearMap = V := by
  let W := directRotation U V hacute
  have hW := directRotation_unitary U V hacute
  have hint := directRotation_intertwines U V hacute
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    apply V.starProjection_eq_self_iff.mp
    have h := congrArg (fun T : E →L[𝕜] E => T x) hint
    simpa [U.starProjection_eq_self_iff.mpr hx] using h.symm
  · intro y hy
    obtain ⟨x, rfl⟩ := hW.2 y
    have hx : projection U x ∈ U := U.starProjection_apply_mem x
    refine ⟨projection U x, hx, ?_⟩
    have h := congrArg (fun T : E →L[𝕜] E => T x) hint
    simpa [V.starProjection_eq_self_iff.mpr hy] using h

/-- Square of the direct rotation is the product of reflections. 

Lean proof route for a weaker agent:

1. Use the polar/trigonometric formula for the direct rotation on the two-projection decomposition.
2. Verify the scalar `2×2` identity that two equal angle rotations compose to the product of reflections.
3. Extend the identity over the trivial reducing summands and close by operator extensionality.


Ext-agent signature audit (GPT 5.6 High): Correct with the stated reflection order for
the convention that the direct rotation maps `U` to `V`; verify the orientation on the
planar model before general assembly.

Preferred dependency route: Construct the polar factor of `QP + QᗮPᗮ`; prove
intertwining before extremality, and use the Halmos decomposition only for the final
minimization theorem.
-/
theorem directRotation_sq
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hacute : IsAcute U V) :
    directRotation U V hacute ∘L directRotation U V hacute =
      reflectionOperator V ∘L reflectionOperator U :=
  -- **Leaf obligation.** Requires the Halmos two-projection decomposition
  -- framework (reducing summands, angle fibers, scalar rotation identity) —
  -- the parked polar-decomposition campaign; see the proof route above.
  sorry

/-- Direct rotation minimizes maximal displacement from the identity.

Proof strategy: reduce by the two-projection decomposition to scalar
`2 x 2` angle fibers.  On each generic fiber, every unitary carrying the first
line to the second has displacement at least that of the shorter rotation.
Take the supremum over the angle spectrum.  State and prove any necessary
angle restriction explicitly; do not infer an unrestricted extremal theorem
for arbitrary symmetric ideal gauges from the operator-norm result. 

Lean proof route for a weaker agent:

1. Reduce the pair of projections to the Halmos two-projection decomposition.
2. On each generic two-dimensional angle fiber, prove the shorter rotation minimizes `‖W-I‖` among unitaries sending the first line to the second.
3. Take the essential supremum over the angle spectrum and handle common/orthogonal summands separately.
4. Check that the stated acuteness hypothesis excludes the ambiguous `π/2` branch.


Ext-agent signature audit (GPT 5.6 High): Correct as an operator-norm extremal statement
for acute pairs. It must not be generalized automatically to every symmetric ideal
gauge.

Preferred dependency route: Construct the polar factor of `QP + QᗮPᗮ`; prove
intertwining before extremality, and use the Halmos decomposition only for the final
minimization theorem.
-/
theorem directRotation_minimal
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hacute : IsAcute U V)
    (W : E →L[𝕜] E) (hW : IsUnitaryOperator W)
    (hmap : U.map W.toLinearMap = V) :
    ‖directRotation U V hacute - ContinuousLinearMap.id 𝕜 E‖ ≤
      ‖W - ContinuousLinearMap.id 𝕜 E‖ :=
  -- **Leaf obligation.** Requires the Halmos two-projection decomposition
  -- framework (fiber norms, unitary transport constraint, scalar shorter
  -- rotation) — the parked polar-decomposition campaign; see the proof route
  -- above.
  sorry

end DavisKahanExt
end ForMathlib

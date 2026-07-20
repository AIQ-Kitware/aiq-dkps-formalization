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
  let S := canonicalIntertwiner U V
  let A := operatorAbsoluteValue S
  let Au := canonicalAbsoluteValueUnit U V hacute
  have hsq : A ∘L A = star S ∘L S :=
    operatorAbsoluteValue_sq S
  have hAself : star A = A :=
    (operatorAbsoluteValue_isSelfAdjoint S).star_eq
  have hleft : star (directRotation U V hacute) ∘L
      directRotation U V hacute = 1 := by
    unfold directRotation
    rw [star_mul, ← coe_canonicalAbsoluteValueUnit]
    change (↑Au⁻¹ : E →L[𝕜] E) ∘L star S ∘L S ∘L
      (↑Au⁻¹ : E →L[𝕜] E) = 1
    rw [← hsq]
    simp [ContinuousLinearMap.comp_assoc, hAself]
  have hright : directRotation U V hacute ∘L
      star (directRotation U V hacute) = 1 := by
    have hunit : IsUnit (directRotation U V hacute) := by
      exact IsUnit.mul
        (canonicalIntertwinerUnit U V hacute).isUnit
        (canonicalAbsoluteValueUnit U V hacute).isUnit.inv
    exact left_inv_eq_right_inv hleft hunit.unit.mul_inv
  exact isUnitaryOperator_of_star_mul_self_and_mul_star_self hleft hright

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
    apply hW.1.injective
    have h := congrArg (fun T : E →L[𝕜] E => T x) hint
    simpa [V.starProjection_eq_self_iff.mpr hy] using h

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
    exact IsUnit.commute_inv_left hA
      (canonicalAbsoluteValueUnit U V hacute).isUnit
  unfold directRotation
  calc
    (canonicalIntertwiner U V ∘L
        (↑(canonicalAbsoluteValueUnit U V hacute)⁻¹ : E →L[𝕜] E)) ∘L
        projection U
        = canonicalIntertwiner U V ∘L projection U ∘L
            (↑(canonicalAbsoluteValueUnit U V hacute)⁻¹ : E →L[𝕜] E) := by
              rw [ContinuousLinearMap.comp_assoc, hAinv.eq,
                ← ContinuousLinearMap.comp_assoc]
    _ = projection V ∘L canonicalIntertwiner U V ∘L
          (↑(canonicalAbsoluteValueUnit U V hacute)⁻¹ : E →L[𝕜] E) := by
            rw [hS]
    _ = projection V ∘L directRotation U V hacute := by
          simp [directRotation, ContinuousLinearMap.comp_assoc]

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
      reflectionOperator V ∘L reflectionOperator U := by
  obtain ⟨D, hreduce, hP, hQ, hW⟩ :=
    halmosTwoProjectionDecomposition U V
  apply D.ext_reducingSummands
  · simp [directRotation, canonicalIntertwiner, hP, hQ]
  · simp [directRotation, canonicalIntertwiner, hP, hQ]
  · exact defectSummands_bot_of_acute hacute
  · intro ξ
    let θ := D.angle ξ
    have hθ : 0 ≤ θ ∧ θ < Real.pi/2 := D.angle_mem_acute ξ hacute
    rw [hW ξ, D.reflectionProduct_on_generic ξ]
    exact scalar_rotation_sq_eq_reflectionProduct θ

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
      ‖W - ContinuousLinearMap.id 𝕜 E‖ := by
  obtain ⟨D, hreduce, hP, hQ, hcanonical⟩ :=
    halmosTwoProjectionDecomposition U V
  rw [D.opNorm_eq_iSup_fiberNorm]
  apply iSup_le
  intro ξ
  have htransport := D.unitary_transport_constraint W hW hmap ξ
  have hshort := scalar_shorter_rotation_minimizes_displacement
    (D.angle ξ) (D.angle_mem_acute ξ hacute) htransport
  exact le_trans hshort (D.fiberNorm_le_opNorm (W-1) ξ)

end DavisKahanExt
end ForMathlib

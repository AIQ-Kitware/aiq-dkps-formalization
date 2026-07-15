/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.GraphSubspace
import DavisKahan.Experimental.InfiniteDimensional.DoubleAngle
import Mathlib.Analysis.Normed.Ring.Units

/-!
# Infinite-dimensional direct rotations

For an acute pair of orthogonally complemented subspaces, the canonical
intertwiner

`S = P_V P_U + P_{Vᗮ} P_{Uᗮ}`

lies at distance less than one from the identity.  Its polar factor is the
direct rotation.  The construction below is scalar-generic over `RCLike`; the
complex Spectra bridge supplies an independent implementation and comparison
surface.
-/

namespace ForMathlib
namespace DavisKahanExt

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- Canonical pre-polar intertwiner. -/
noncomputable def canonicalIntertwiner
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[𝕜] E :=
  projection V ∘L projection U +
    complementaryProjection V ∘L complementaryProjection U

/-- The canonical intertwiner intertwines the source and target projections. -/
theorem canonicalIntertwiner_intertwines
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    canonicalIntertwiner U V ∘L projection U =
      projection V ∘L canonicalIntertwiner U V := by
  unfold canonicalIntertwiner projection complementaryProjection
  rw [Submodule.starProjection_orthogonal',
    Submodule.starProjection_orthogonal']
  have hP := U.isIdempotentElem_starProjection
  have hQ := V.isIdempotentElem_starProjection
  noncomm_ring [hP, hQ]

/-- Reversing the pair takes the adjoint of the canonical intertwiner. -/
theorem star_canonicalIntertwiner
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    star (canonicalIntertwiner U V) = canonicalIntertwiner V U := by
  unfold canonicalIntertwiner
  simp [star_add, star_mul,
    (isSelfAdjoint_starProjection U).star_eq,
    (isSelfAdjoint_starProjection V).star_eq,
    (isSelfAdjoint_starProjection Uᗮ).star_eq,
    (isSelfAdjoint_starProjection Vᗮ).star_eq]

/-- Exact displacement factorization. -/
theorem canonicalIntertwiner_sub_one
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    canonicalIntertwiner U V - 1 =
      (projection V - projection U) ∘L reflectionOperator U := by
  unfold canonicalIntertwiner projection complementaryProjection
  rw [Submodule.starProjection_orthogonal',
    Submodule.starProjection_orthogonal']
  ext x
  rw [Submodule.reflectionOperator_apply]
  have hP := U.isIdempotentElem_starProjection
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply, ContinuousLinearMap.comp_apply]
  module
  noncomm_ring [hP]

/-- Acuteness makes the canonical intertwiner a unit. -/
noncomputable def canonicalIntertwinerUnit
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) : (E →L[𝕜] E)ˣ := by
  classical
  have hnorm : ‖1 - canonicalIntertwiner U V‖ < 1 := by
    rw [show 1 - canonicalIntertwiner U V =
      -(canonicalIntertwiner U V - 1) by abel,
      norm_neg, canonicalIntertwiner_sub_one]
    calc
      ‖(projection V - projection U) ∘L reflectionOperator U‖
          ≤ ‖projection V - projection U‖ * ‖reflectionOperator U‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖projection V - projection U‖ := by
        have href := norm_reflectionOperator_le_one U
        nlinarith [norm_nonneg (projection V - projection U)]
      _ = subspaceGap U V := by
        change ‖V.starProjection - U.starProjection‖ =
          ‖U.starProjection - V.starProjection‖
        rw [show V.starProjection - U.starProjection =
          -(U.starProjection - V.starProjection) by abel, norm_neg]
      _ < 1 := hacute
  exact Units.oneSub (1 - canonicalIntertwiner U V) hnorm

@[simp] theorem coe_canonicalIntertwinerUnit
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    (canonicalIntertwinerUnit U V hacute : E →L[𝕜] E) =
      canonicalIntertwiner U V := by
  simp [canonicalIntertwinerUnit]

/-- The modulus of the canonical intertwiner, bundled as a unit. -/
noncomputable def canonicalAbsoluteValueUnit
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) : (E →L[𝕜] E)ˣ := by
  classical
  let S := canonicalIntertwiner U V
  have hS : IsUnit S := (canonicalIntertwinerUnit U V hacute).isUnit
  exact (operatorAbsoluteValue_isUnit hS).unit

@[simp] theorem coe_canonicalAbsoluteValueUnit
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    (canonicalAbsoluteValueUnit U V hacute : E →L[𝕜] E) =
      operatorAbsoluteValue (canonicalIntertwiner U V) := by
  exact IsUnit.unit_spec (operatorAbsoluteValue_isUnit
    (canonicalIntertwinerUnit U V hacute).isUnit)

/-- Canonical direct rotation: the polar factor `S |S|⁻¹`. -/
noncomputable def directRotation (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) : E →L[𝕜] E :=
  canonicalIntertwiner U V ∘L
    (↑(canonicalAbsoluteValueUnit U V hacute)⁻¹ : E →L[𝕜] E)

/-- The modulus commutes with the source projection. -/
theorem canonicalAbsoluteValue_commutes_projection
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    Commute (operatorAbsoluteValue (canonicalIntertwiner U V))
      (projection U) := by
  have hSP := canonicalIntertwiner_intertwines U V
  have hstar : projection U ∘L star (canonicalIntertwiner U V) =
      star (canonicalIntertwiner U V) ∘L projection V := by
    simpa [star_mul,
      (isSelfAdjoint_starProjection U).star_eq,
      (isSelfAdjoint_starProjection V).star_eq] using congrArg star hSP
  have hgram : Commute
      (star (canonicalIntertwiner U V) ∘L canonicalIntertwiner U V)
      (projection U) := by
    rw [commute_iff_eq]
    calc
      (star (canonicalIntertwiner U V) ∘L canonicalIntertwiner U V) ∘L projection U
          = star (canonicalIntertwiner U V) ∘L
              (projection V ∘L canonicalIntertwiner U V) := by
                rw [ContinuousLinearMap.comp_assoc,
                  canonicalIntertwiner_intertwines]
      _ = projection U ∘L
          (star (canonicalIntertwiner U V) ∘L canonicalIntertwiner U V) := by
            rw [← ContinuousLinearMap.comp_assoc, ← hstar,
              ContinuousLinearMap.comp_assoc]
  exact RCLikeContinuousFunctionalCalculus.sqrt_commute hgram

/-- The direct rotation is unitary. -/
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

/-- Intertwining of orthogonal projections. -/
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

/-- The direct rotation maps one subspace onto the other. -/
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

/-- Square of the direct rotation is the ordered product of reflections. -/
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

/-- Reversal of the ordered pair takes the adjoint direct rotation. -/
theorem star_directRotation
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hacute : IsAcute U V) :
    star (directRotation U V hacute) =
      directRotation V U (by simpa [IsAcute, Submodule.projectionGap_comm] using hacute) := by
  obtain ⟨D, hreduce, hP, hQ, hW⟩ :=
    halmosTwoProjectionDecomposition U V
  apply D.ext_reducingSummands
  · simp [directRotation, canonicalIntertwiner]
  · simp [directRotation, canonicalIntertwiner]
  · exact defectSummands_bot_of_acute hacute
  · intro ξ
    rw [hW ξ, D.reversed_directRotation_on_generic ξ]
    exact star_scalar_rotation

/-- Direct rotation minimizes maximal displacement from the identity. -/
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

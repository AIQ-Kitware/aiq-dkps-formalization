/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedQuarticStability

/-!
# Stability of the exact commuting-unitary correction

Unitary invariance transfers the transporter growth certificates to the
literal operator-difference objective for corrections preserving a prescribed
subspace. The named spectral optimizer equals the canonical correction
through the closed cutoff. These are the quantitative consequences of the
journal paper's commuting-correction corollary.
-/

public section

noncomputable section
namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
private theorem frobenius_correction_eq_transport (A C R : E ≃ₗᵢ[ℂ] E) :
    UnitarilyInvariantSeminorm.frobenius ℂ E E
      ((C.symm.trans A).toLinearMap - R.toLinearMap) =
    UnitarilyInvariantSeminorm.frobenius ℂ E E
      (C.toLinearMap - (A.trans R.symm).toLinearMap) := by
  let F := UnitarilyInvariantSeminorm.frobenius ℂ E E
  have hfac : ((C.symm.trans A).toLinearMap - R.toLinearMap) ∘ₗ C.toLinearMap =
      R.toLinearMap ∘ₗ ((A.trans R.symm).toLinearMap - C.toLinearMap) := by
    ext x
    simp
  calc
    _ = F (((C.symm.trans A).toLinearMap - R.toLinearMap) ∘ₗ C.toLinearMap) :=
      (F.map_comp_linearIsometryEquiv C _).symm
    _ = F (R.toLinearMap ∘ₗ ((A.trans R.symm).toLinearMap - C.toLinearMap)) :=
      congrArg F hfac
    _ = F ((A.trans R.symm).toLinearMap - C.toLinearMap) :=
      F.map_linearIsometryEquiv_comp R _
    _ = _ := by rw [← neg_sub, map_neg_eq_map]

omit [CompleteSpace E] in
private theorem correction_cost_eq (tau : ℝ) (A R : E ≃ₗᵢ[ℂ] E) :
    smoothedOperatorDistance tau A.toLinearMap (A.trans R.symm).toLinearMap =
      smoothedDisplacementCost tau R.toLinearMap := by
  rw [smoothedOperatorDistance_eq_displacement]
  have heq : (A.trans R.symm).symm.trans A = R := by ext x; simp
  rw [heq]

/-- The strict-subcritical objective error controls the distance from the
canonical subspace-preserving correction, with a dimension-independent constant. -/
theorem smoothed_correction_quadratic_growth
    (tau bound : ℝ) (htau : 0 < tau) (hbound : bound ∈ Set.Icc 0 (Real.pi / 2))
    (hcut : ((smoothingRadius tau)⁻¹) ^ 2 < Real.cos bound)
    (K : Submodule ℂ E) (A : E ≃ₗᵢ[ℂ] E)
    (hmax : ∀ i : Fin (Module.finrank ℂ K), K.principalAngles (K.map A.toLinearMap) i ≤ bound) :
    let V := K.map A.toLinearMap
    let hKV := (A.toLinearEquiv.finrank_map_eq K).symm
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation K V (finiteCrossedDefectEquiv K V hKV),
        nonacuteDirectRotation_mem_unitary K V (finiteCrossedDefectEquiv K V hKV)⟩ :
          unitary (E →L[ℂ] E))
    let C₀ := A.trans R.symm
    ∀ C : E ≃ₗᵢ[ℂ] E, K.map C.toLinearMap = K →
      smoothedStabilityCoefficient tau bound * UnitarilyInvariantSeminorm.frobenius ℂ E E
          (C.toLinearMap - C₀.toLinearMap) ^ 2 ≤
        smoothedOperatorDistance tau A.toLinearMap C.toLinearMap -
          smoothedOperatorDistance tau A.toLinearMap C₀.toLinearMap := by
  dsimp only
  intro C hC
  have hg := smoothed_transport_growth_of_principalAngles_le tau bound htau hbound hcut
    K (K.map A.toLinearMap) (A.toLinearEquiv.finrank_map_eq K).symm hmax
    (C.symm.trans A) (transporter_of_correction_preserves_subspace K A C hC)
  rw [frobenius_correction_eq_transport] at hg
  rw [smoothedOperatorDistance_eq_displacement, correction_cost_eq]
  exact hg

/-- The closed canonical regime gives a fourth-power objective-error
certificate for every unitary correction preserving the specified subspace. -/
theorem smoothed_correction_quartic_growth
    (tau : ℝ) (htau : 0 < tau) (K : Submodule ℂ E) (A : E ≃ₗᵢ[ℂ] E)
    (hmax : ∀ i : Fin (Module.finrank ℂ K),
      K.principalAngles (K.map A.toLinearMap) i ≤ smoothedCriticalAngle tau) :
    let V := K.map A.toLinearMap
    let hKV := (A.toLinearEquiv.finrank_map_eq K).symm
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation K V (finiteCrossedDefectEquiv K V hKV),
        nonacuteDirectRotation_mem_unitary K V (finiteCrossedDefectEquiv K V hKV)⟩ :
          unitary (E →L[ℂ] E))
    let C₀ := A.trans R.symm
    ∀ C : E ≃ₗᵢ[ℂ] E, K.map C.toLinearMap = K →
      3 * tau * UnitarilyInvariantSeminorm.frobenius ℂ E E
          (C.toLinearMap - C₀.toLinearMap) ^ 4 ≤
        32 * (smoothingRadius tau) ^ 4 * Module.finrank ℂ E *
          (smoothedOperatorDistance tau A.toLinearMap C.toLinearMap -
            smoothedOperatorDistance tau A.toLinearMap C₀.toLinearMap) := by
  dsimp only
  intro C hC
  have hg := smoothed_transport_quartic_growth tau htau
    K (K.map A.toLinearMap) (A.toLinearEquiv.finrank_map_eq K).symm hmax
    (C.symm.trans A) (transporter_of_correction_preserves_subspace K A C hC)
  rw [frobenius_correction_eq_transport] at hg
  rw [smoothedOperatorDistance_eq_displacement, correction_cost_eq]
  exact hg


/-- In the closed canonical regime the named spectral correction is the
canonical rotation correction. -/
theorem optimalSmoothedCorrection_eq_canonical_of_angles_le
    (tau : ℝ) (htau : 0 < tau) (K : Submodule ℂ E) (A : E ≃ₗᵢ[ℂ] E)
    (hmax : ∀ i : Fin (Module.finrank ℂ K),
      K.principalAngles (K.map A.toLinearMap) i ≤ smoothedCriticalAngle tau) :
    let V := K.map A.toLinearMap
    let hKV := (A.toLinearEquiv.finrank_map_eq K).symm
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation K V (finiteCrossedDefectEquiv K V hKV),
        nonacuteDirectRotation_mem_unitary K V (finiteCrossedDefectEquiv K V hKV)⟩ :
          unitary (E →L[ℂ] E))
    optimalSmoothedCorrection tau K A = A.trans R.symm := by
  dsimp only
  have hcan := smoothed_canonical_unique_minimizer tau htau K (K.map A.toLinearMap)
    (A.toLinearEquiv.finrank_map_eq K).symm hmax
  dsimp only at hcan
  have heq := (hcan.2 _ (optimalSmoothedTransport_maps tau K (K.map A.toLinearMap)
      (A.toLinearEquiv.finrank_map_eq K).symm)).2
    (optimalSmoothedTransport_isMin tau htau K (K.map A.toLinearMap)
      (A.toLinearEquiv.finrank_map_eq K).symm _ hcan.1)
  unfold optimalSmoothedCorrection
  rw [heq]

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

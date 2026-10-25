/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedCorrectionStability
public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedCanonicalOptimality
public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedOptimizerUniqueness
public import ForTauCeti.Analysis.InnerProductSpace.Projection.GapThreshold

/-!
# The exact commutator cutoff for canonical unitary correction

For a given unitary `A` and source projection `P`, the canonical correction
is globally optimal for the literal Charbonnier cost exactly when
`‖A P - P A‖ ≤ sqrt (1 - eta⁻⁴)`. This tests the closed canonical regime
using a single operator-norm defect. The accepted principal-angle and
projection-gap APIs provide the geometric reduction.

This is the commutator criterion in the journal paper's exact correction
application. The projection-gap identity is classical; the norm-specific
cutoff is a consequence of the exact smoothed minimum theorem.
-/

public section

noncomputable section
namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition
/-- The sine cutoff expressed directly in the smoothing radius. -/
theorem sin_smoothedCriticalAngle (tau : ℝ) :
    Real.sin (smoothedCriticalAngle tau) =
      Real.sqrt (1 - ((smoothingRadius tau)⁻¹) ^ 4) := by
  rw [smoothedCriticalAngle, Real.sin_arccos]
  congr 1
  ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- The closed canonical regime can be tested directly from the projection
gap, without computing the full list of principal angles. -/
theorem smoothed_canonical_isMin_iff_projectionGap
    (tau : ℝ) (htau : 0 < tau) (K L : Submodule ℂ E)
    (hKL : Module.finrank ℂ K = Module.finrank ℂ L) :
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
        nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
          unitary (E →L[ℂ] E))
    (∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
      smoothedDisplacementCost tau R.toLinearMap ≤ smoothedDisplacementCost tau T.toLinearMap) ↔
      K.projectionGap L ≤ Real.sin (smoothedCriticalAngle tau) := by
  have hc := smoothed_canonical_isMin_iff tau htau K L hKL
  dsimp only at hc ⊢
  rw [hc, Submodule.finite_principalAngles_le_iff_directedProjectionGap_le K L _ (smoothedCriticalAngle_mem_Icc tau),
    K.projectionGap_eq_directedProjectionGap_of_finrank_eq L hKL]

omit [CompleteSpace E] in
/-- The correction--transport bijection preserves global minimality for the
literal singular-value distance. -/
theorem correction_isMin_iff_transport_isMin
    (tau : ℝ) (K : Submodule ℂ E) (A R : E ≃ₗᵢ[ℂ] E) :
    (∀ C : E ≃ₗᵢ[ℂ] E, K.map C.toLinearMap = K →
      smoothedOperatorDistance tau A.toLinearMap (A.trans R.symm).toLinearMap ≤
        smoothedOperatorDistance tau A.toLinearMap C.toLinearMap) ↔
    (∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = K.map A.toLinearMap →
      smoothedDisplacementCost tau R.toLinearMap ≤ smoothedDisplacementCost tau T.toLinearMap) := by
  have hcost (T : E ≃ₗᵢ[ℂ] E) :
      smoothedOperatorDistance tau A.toLinearMap (A.trans T.symm).toLinearMap =
        smoothedDisplacementCost tau T.toLinearMap := by
    rw [smoothedOperatorDistance_eq_displacement]
    have hrel : (A.trans T.symm).symm.trans A = T := by ext x; simp
    rw [hrel]
  constructor
  · intro h T hT
    have hh := h (A.trans T.symm) (correction_preserves_subspace K A T hT)
    rwa [hcost, hcost] at hh
  · intro h C hC
    rw [hcost, smoothedOperatorDistance_eq_displacement]
    exact h (C.symm.trans A) (transporter_of_correction_preserves_subspace K A C hC)

/-- Canonical correction is globally optimal exactly when the commutator
norm stays below the explicit smoothed sine cutoff. -/
theorem canonical_correction_isMin_iff_commutator
    (tau : ℝ) (htau : 0 < tau) (K : Submodule ℂ E) (A : E ≃ₗᵢ[ℂ] E) :
    let L := K.map A.toLinearMap
    let hKL := (A.toLinearEquiv.finrank_map_eq K).symm
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
        nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
          unitary (E →L[ℂ] E))
    (∀ C : E ≃ₗᵢ[ℂ] E, K.map C.toLinearMap = K →
      smoothedOperatorDistance tau A.toLinearMap (A.trans R.symm).toLinearMap ≤
        smoothedOperatorDistance tau A.toLinearMap C.toLinearMap) ↔
      ‖(A : E →L[ℂ] E) * K.starProjection - K.starProjection * (A : E →L[ℂ] E)‖ ≤
        Real.sqrt (1 - ((smoothingRadius tau)⁻¹) ^ 4) := by
  dsimp only
  rw [correction_isMin_iff_transport_isMin]
  have h := smoothed_canonical_isMin_iff_projectionGap tau htau K (K.map A.toLinearMap)
    (A.toLinearEquiv.finrank_map_eq K).symm
  dsimp only at h
  rwa [Submodule.projectionGap_unitary_image_eq_commutator, sin_smoothedCriticalAngle] at h


/-- The exact commutator threshold characterizes uniqueness of the nearest
subspace-preserving unitary, including all noncanonical competitors. -/
theorem smoothed_correction_unique_minimizer_iff_commutator
    (tau : ℝ) (htau : 0 < tau) (K : Submodule ℂ E) (A : E ≃ₗᵢ[ℂ] E) :
    (∃! C : E ≃ₗᵢ[ℂ] E, K.map C.toLinearMap = K ∧
      ∀ D : E ≃ₗᵢ[ℂ] E, K.map D.toLinearMap = K →
        smoothedOperatorDistance tau A.toLinearMap C.toLinearMap ≤
          smoothedOperatorDistance tau A.toLinearMap D.toLinearMap) ↔
      ‖(A : E →L[ℂ] E) * K.starProjection - K.starProjection * (A : E →L[ℂ] E)‖ ≤
        Real.sqrt (1 - ((smoothingRadius tau)⁻¹) ^ 4) := by
  let L := K.map A.toLinearMap
  let hKL := (A.toLinearEquiv.finrank_map_eq K).symm
  let e : (E ≃ₗᵢ[ℂ] E) ≃ (E ≃ₗᵢ[ℂ] E) :=
    { toFun := fun C => C.symm.trans A
      invFun := fun W => A.trans W.symm
      left_inv := by intro C; ext x; simp
      right_inv := by intro W; ext x; simp }
  let CorrMin (C : E ≃ₗᵢ[ℂ] E) : Prop := K.map C.toLinearMap = K ∧
    ∀ D : E ≃ₗᵢ[ℂ] E, K.map D.toLinearMap = K →
      smoothedOperatorDistance tau A.toLinearMap C.toLinearMap ≤
        smoothedOperatorDistance tau A.toLinearMap D.toLinearMap
  let TransMin (W : E ≃ₗᵢ[ℂ] E) : Prop := K.map W.toLinearMap = L ∧
    ∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
      smoothedDisplacementCost tau W.toLinearMap ≤ smoothedDisplacementCost tau T.toLinearMap
  have hpred (C : E ≃ₗᵢ[ℂ] E) : CorrMin C ↔ TransMin (e C) := by
    have hback : A.trans (C.symm.trans A).symm = C := by ext x; simp
    have hm := correction_isMin_iff_transport_isMin tau K A (C.symm.trans A)
    rw [hback] at hm
    constructor
    · intro h
      exact ⟨transporter_of_correction_preserves_subspace K A C h.1, hm.mp h.2⟩
    · intro h
      have hc := correction_preserves_subspace K A (C.symm.trans A) h.1
      rw [hback] at hc
      exact ⟨hc, hm.mpr h.2⟩
  have hu : (∃! C, CorrMin C) ↔ ∃! W, TransMin W := e.existsUnique_congr hpred
  have hcut : (∀ i : Fin (Module.finrank ℂ K), K.principalAngles L i ≤ smoothedCriticalAngle tau) ↔
      K.projectionGap L ≤ Real.sin (smoothedCriticalAngle tau) := by
    rw [Submodule.finite_principalAngles_le_iff_directedProjectionGap_le K L _ (smoothedCriticalAngle_mem_Icc tau),
      K.projectionGap_eq_directedProjectionGap_of_finrank_eq L hKL]
  change (∃! C, CorrMin C) ↔ _
  rw [hu]
  change (∃! W : E ≃ₗᵢ[ℂ] E, K.map W.toLinearMap = L ∧
    ∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
      smoothedDisplacementCost tau W.toLinearMap ≤ smoothedDisplacementCost tau T.toLinearMap) ↔ _
  rw [smoothed_transport_unique_minimizer_iff tau htau K L hKL, hcut]
  rw [Submodule.projectionGap_unitary_image_eq_commutator, sin_smoothedCriticalAngle]

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

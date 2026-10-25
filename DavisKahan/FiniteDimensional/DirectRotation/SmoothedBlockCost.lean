/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedSpectralCost
public import ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.BlockSchatten
public import ForTauCeti.Analysis.InnerProductSpace.SchattenTransportRestriction

/-!
# Coordinate invariance and block additivity of the literal Charbonnier cost

Both identities apply to arbitrary operators and every real smoothing
parameter. They retain every zero singular value and allow empty blocks.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] [CompleteSpace F]

/-- The literal Charbonnier displacement cost is unchanged by unitary
coordinates, including an isometric change of ambient carrier. -/
theorem smoothedDisplacementCost_conj_linearIsometryEquiv_complex
    (tau : ℝ) (e : E ≃ₗᵢ[ℂ] F) (A : E →L[ℂ] E) :
    smoothedDisplacementCost tau (e.conjStarAlgEquiv A).toLinearMap =
      smoothedDisplacementCost tau A.toLinearMap := by
  have hconj : LinearMap.id - (e.conjStarAlgEquiv A).toLinearMap =
      (e : E →ₗ[ℂ] F) ∘ₗ (LinearMap.id - A.toLinearMap) ∘ₗ
        (e.symm : F →ₗ[ℂ] E) := by
    ext x
    change x - e (A (e.symm x)) = e (e.symm x - A (e.symm x))
    rw [map_sub, e.apply_symm_apply]
  rw [smoothedDisplacementCost, smoothedDisplacementCost, hconj,
    LinearMap.singularValues_linearIsometryEquiv_comp,
    LinearMap.singularValues_comp_linearIsometryEquiv, ← e.toLinearEquiv.finrank_eq]

omit [CompleteSpace E] [CompleteSpace F] in
/-- Orthogonal blocks contribute additively to the literal displacement
cost. No unitarity or positivity assumption is needed. -/
theorem smoothedDisplacementCost_withLpProdMap_complex
    (tau : ℝ) (A : E →L[ℂ] E) (B : F →L[ℂ] F) :
    smoothedDisplacementCost tau (A.withLpProdMap 2 B).toLinearMap =
      smoothedDisplacementCost tau A.toLinearMap + smoothedDisplacementCost tau B.toLinearMap := by
  have hblock : LinearMap.id - (A.withLpProdMap 2 B).toLinearMap =
      ((LinearMap.id - A.toLinearMap).prodMap (LinearMap.id - B.toLinearMap)).withLpMap 2 := by
    rw [ContinuousLinearMap.coe_withLpProdMap]
    ext x
    apply WithLp.ofLp_injective 2
    rfl
  rw [smoothedDisplacementCost, smoothedDisplacementCost, smoothedDisplacementCost, hblock]
  exact sum_singularValues_prodMap_withLpMap _ _ (fun s : ℝ =>
    Real.sqrt (tau ^ 2 + s ^ 2) - tau)

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

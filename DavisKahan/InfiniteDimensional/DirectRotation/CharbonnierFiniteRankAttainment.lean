/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.InfiniteDimensional.DirectRotation.CharbonnierGlobalLowerBound
public import DavisKahan.Geometry.Polar.DirectRotationRank
public import ForTauCeti.Analysis.InnerProductSpace.Projection.ExtendTransport

/-!
# Exact smoothed minima for finite-rank Hilbert-space projection pairs

A finite-section optimizer extends by identity and attains the intrinsic
ambient angle sum. The unrestricted lower bound compares it with every
ambient complex unitary transporter, including infinite-rank competitors.
The subspaces may have infinite rank and corank and the ambient Hilbert
space need not be separable. Balanced finite crossed defects are essential.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.InfiniteDimensional.SmoothedPhaseTransition

open FiniteDimensional.SmoothedPhaseTransition
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- An actual finite-rank feasible reference gives a finite-rank global
smoothed minimizer, with the exact ambient singular-angle value. -/
theorem exists_unitary_minimizing_charbonnier_transport_of_finite_rank_reference
    (tau : ℝ) (hτ : 0 < tau)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (R : E ≃ₗᵢ[ℂ] E) (hRmap : K.map R.toLinearMap = L)
    (n : ℕ) (hR : (1 - R.toLinearMap).rank ≤ n) :
    ∃ U : E ≃ₗᵢ[ℂ] E, K.map U.toLinearMap = L ∧
      (∃ m : ℕ, (1 - U.toLinearMap).rank ≤ m) ∧
      (1 - (U : E →L[ℂ] E)).charbonnierCost tau ≠ ∞ ∧
      (1 - (U : E →L[ℂ] E)).charbonnierCost tau =
        ∑' j, ENNReal.ofReal (smoothedPhaseMinimum tau
          (Real.arcsin ((K.sinThetaMap L).singularValue j : ℝ))) ∧
      ∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
        (1 - (U : E →L[ℂ] E)).charbonnierCost tau ≤
          (1 - (T : E →L[ℂ] E)).charbonnierCost tau := by
  obtain ⟨M, hM, _, V, _, hlocal, hK, hL, heq, _⟩ :=
    K.exists_finite_transport_section L ⊥ R hRmap n hR
  let : FiniteDimensional ℂ M := hM
  let K₀ := K.comap M.subtype
  let L₀ := L.comap M.subtype
  have hdim := V.toLinearEquiv.finrank_map_eq K₀
  rw [hlocal] at hdim
  obtain ⟨W, hWmap, hWcost, _⟩ :=
    exists_unitary_minimizing_smoothed_transport_principalAngles tau hτ K₀ L₀ hdim.symm
  obtain ⟨U, hUmap, _, _, hdisp⟩ :=
    K.exists_transport_extension_by_identity L M hK hL heq W hWmap
  have hcost : (1 - (U : E →L[ℂ] E)).charbonnierCost tau =
      ENNReal.ofReal (smoothedDisplacementCost tau W.toLinearMap) := by
    rw [hdisp, ContinuousLinearMap.charbonnierCost_orthogonal_extension,
      ContinuousLinearMap.charbonnierCost_eq_ofReal_sum tau hτ.le]
    rfl
  have hvalue : (1 - (U : E →L[ℂ] E)).charbonnierCost tau =
      ∑' j, ENNReal.ofReal (smoothedPhaseMinimum tau
        (Real.arcsin ((K.sinThetaMap L).singularValue j : ℝ))) := by
    rw [hcost, hWcost,
      Submodule.tsum_sine_penalty_eq_principalAngle_sum_of_finite_core K L M hK hL heq
        (fun t => ENNReal.ofReal (smoothedPhaseMinimum tau t))
        (by rw [smoothedPhaseMinimum_zero_angle tau hτ, ENNReal.ofReal_zero])]
    exact ENNReal.ofReal_sum_of_nonneg (fun i _ => smoothedPhaseMinimum_nonneg tau _ hτ
      ⟨K₀.principalAngles_nonneg L₀ i, K₀.principalAngles_le_pi_div_two L₀ i⟩)
  refine ⟨U, hUmap, ⟨Module.finrank ℂ M, ?_⟩,
    by rw [hcost]; exact ENNReal.ofReal_ne_top, hvalue, ?_⟩
  · have hlin : 1 - U.toLinearMap =
        ((M.subtypeL ∘L (1 - (W : M →L[ℂ] M))) ∘L M.orthogonalProjectionOnto).toLinearMap := by
      change (1 - (U : E →L[ℂ] E)).toLinearMap = _
      rw [hdisp, ContinuousLinearMap.comp_assoc]
    rw [hlin, ContinuousLinearMap.toLinearMap_comp]
    exact (LinearMap.rank_comp_le_left _ _).trans (by
      simpa only [Module.finrank_eq_rank] using
        LinearMap.rank_le_domain (M.subtypeL ∘L (1 - (W : M →L[ℂ] M))).toLinearMap)
  · intro T hT
    rw [hvalue]
    exact sine_smoothedPhaseMinimum_sum_le_transport tau hτ K L T hT

/-- **Exact unrestricted smoothed minimum for finite-rank projection
pairs.** Finite-rank projection difference and balanced crossed defects
give a finite-cost attainer against all ambient complex unitary competitors. -/
theorem exists_unitary_minimizing_charbonnier_transport_of_finite_rank_projection_sub
    (tau : ℝ) (hτ : 0 < tau)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (n : ℕ) (hD : (K.starProjection - L.starProjection).rank ≤ n)
    (hbalance : Module.finrank ℂ (halmosSourceDefect K L) =
      Module.finrank ℂ (halmosTargetDefect K L)) :
    ∃ U : E ≃ₗᵢ[ℂ] E, K.map U.toLinearMap = L ∧
      (∃ m : ℕ, (1 - U.toLinearMap).rank ≤ m) ∧
      (1 - (U : E →L[ℂ] E)).charbonnierCost tau ≠ ∞ ∧
      (1 - (U : E →L[ℂ] E)).charbonnierCost tau =
        ∑' j, ENNReal.ofReal (smoothedPhaseMinimum tau
          (Real.arcsin ((K.sinThetaMap L).singularValue j : ℝ))) ∧
      ∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
        (1 - (U : E →L[ℂ] E)).charbonnierCost tau ≤
          (1 - (T : E →L[ℂ] E)).charbonnierCost tau := by
  obtain ⟨R, hRmap, hR⟩ :=
    exists_finite_rank_transport_of_projection_sub_rank_le_of_defect_balance K L n hD hbalance
  exact exists_unitary_minimizing_charbonnier_transport_of_finite_rank_reference
    tau hτ K L R hRmap n hR

end TauCeti.DavisKahan.InfiniteDimensional.SmoothedPhaseTransition

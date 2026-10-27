/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedNonacuteClassification

/-! # Every smoothed optimizer preserves the intrinsic angle sectors -/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- Every global finite complex smoothed optimizer commutes with the
full sine-angle operator. Unequal angle sectors cannot mix, including
zero and right-angle sectors. -/
theorem commute_sinAngleOperator_of_smoothed_minimal
    (tau : ℝ) (hτ : 0 < tau) (K L : Submodule ℂ E)
    (hKL : Module.finrank ℂ K = Module.finrank ℂ L)
    (U : E ≃ₗᵢ[ℂ] E) (hmap : K.map U.toLinearMap = L)
    (hmin : ∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
      smoothedDisplacementCost tau U.toLinearMap ≤ smoothedDisplacementCost tau T.toLinearMap) :
    Commute (U : E →L[ℂ] E) (K.sinAngleOperator L) := by
  let a := smoothingRadius tau
  have ha : 1 < a := one_lt_smoothingRadius tau hτ
  have ha0 : 0 < a := zero_lt_one.trans ha
  have hUC := minimizing_weighted_transport_commutes_cosine_complex
    a a⁻¹ (inv_pos.mpr ha0) (((inv_lt_one₀ ha0).mpr ha).trans ha) K L hKL U hmap
      (smoothed_minimizer_weighted_cost_eq_complex tau hτ K L hKL U hmap hmin)
  let S := K.sinAngleOperator L
  let C := Proposition35.section3CosAngleOperator K L
  have hSin : Proposition35.section3SinAngleOperator K L = S := by
    dsimp only [S, Proposition35.section3SinAngleOperator]
    rw [Submodule.sinAngleOperator_def]
  have hSS : S * S = 1 - C * C := by
    have h := Proposition35.section3Sin_sq_add_cos_sq K L
    rw [hSin] at h
    exact eq_sub_of_add_eq h
  have hgram : Commute (U : E →L[ℂ] E) (star S * S) := by
    rw [(K.isPositive_sinAngleOperator L).isSelfAdjoint.star_eq, hSS]
    exact (Commute.one_right _).sub_right (hUC.mul_right hUC)
  have h := ContinuousLinearMap.commute_modulus_of_commute hgram
  rwa [(K.isPositive_sinAngleOperator L).modulus_eq] at h

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

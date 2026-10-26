/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.OperatorIdeal.Charbonnier
public import ForTauCeti.Analysis.OperatorIdeal.OrthogonalExtension

/-! # Orthogonal extensions and finite sections of the Charbonnier trace -/

public section

noncomputable section

namespace ContinuousLinearMap

open scoped ENNReal

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Orthogonal zero extension preserves the extended smoothed spectral
cost, with no rank or ideal-membership hypothesis. -/
theorem charbonnierCost_orthogonal_extension (tau : ℝ)
    (M : Submodule 𝕜 E) (N : Submodule 𝕜 F)
    [M.HasOrthogonalProjection] [N.HasOrthogonalProjection] (T : M →L[𝕜] N) :
    (N.subtypeL ∘L T ∘L M.orthogonalProjectionOnto).charbonnierCost tau =
      T.charbonnierCost tau := by
  simp only [charbonnierCost, singularValue_orthogonal_extension]

/-- On finite-dimensional spaces, the extended spectral trace agrees
exactly with the real finite singular-value sum. -/
theorem charbonnierCost_eq_ofReal_sum (tau : ℝ) (hτ : 0 ≤ tau)
    [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] (T : E →L[𝕜] F) :
    T.charbonnierCost tau = ENNReal.ofReal
      (∑ i : Fin (Module.finrank 𝕜 E),
        (Real.sqrt (tau ^ 2 + (T.toLinearMap.singularValues i) ^ 2) - tau)) := by
  rw [charbonnierCost, TauCeti.OperatorIdealFamily.tsum_singularValue_penalty_eq_sum T
    (fun s => ENNReal.ofReal (Real.sqrt (tau ^ 2 + (s : ℝ) ^ 2) - tau))
    (by simp [Real.sqrt_sq hτ])]
  simp_rw [singularValue_eq_linearMap_singularValues]
  rw [ENNReal.ofReal_sum_of_nonneg]
  intro i _
  have hr := Real.sq_sqrt (show 0 ≤ tau ^ 2 + (T.toLinearMap.singularValues i) ^ 2 by
    positivity)
  have hr0 := Real.sqrt_nonneg (tau ^ 2 + (T.toLinearMap.singularValues i) ^ 2)
  nlinarith [sq_nonneg (T.toLinearMap.singularValues i)]

end ContinuousLinearMap

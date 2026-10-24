/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Schatten
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.EckartYoung
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Continuity of finite Schatten powers

The accepted approximation numbers are continuous in operator norm. In finite
dimension their finite power sum is the actual Schatten power, including at
rank changes and zero singular values.
-/

public section

noncomputable section

namespace TauCeti

open scoped ENNReal BigOperators
open UnitarilyInvariantSeminorm

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- The finite Schatten power is the finite sum of the accepted bounded
operator singular-value powers. -/
theorem schatten_rpow_eq_sum_singularValue
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (A : E →L[𝕜] F) :
    schatten 𝕜 E F p A.toLinearMap ^ p.toReal =
      ∑ i : Fin (Module.finrank 𝕜 E), (A.singularValue i : ℝ) ^ p.toReal := by
  have hp0 : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hp
  have hsum : 0 ≤ A.toLinearMap.singularValues.sum (fun _ s => s ^ p.toReal) :=
    Finsupp.sum_nonneg (fun _ _ => Real.rpow_nonneg (A.toLinearMap.singularValues_nonneg _) _)
  rw [schatten_apply_of_ne_top p hp,
    ← Real.rpow_mul hsum, one_div_mul_cancel hp0.ne', Real.rpow_one]
  rw [← A.toLinearMap.sum_fin_singularValues (· ^ p.toReal) (by simp [hp0.ne'])]
  apply Finset.sum_congr rfl
  intro i _
  rw [ContinuousLinearMap.singularValue_eq_linearMap_singularValues]

/-- The actual finite Schatten power is continuous in operator norm. -/
theorem continuous_schatten_rpow_toLinearMap
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    Continuous (fun A : E →L[𝕜] F => schatten 𝕜 E F p A.toLinearMap ^ p.toReal) := by
  simp_rw [schatten_rpow_eq_sum_singularValue p hp]
  apply continuous_finsetSum
  intro i _
  exact (Real.continuous_rpow_const ENNReal.toReal_nonneg).comp
    (NNReal.continuous_coe.comp (ContinuousLinearMap.continuous_singularValue i))

end TauCeti

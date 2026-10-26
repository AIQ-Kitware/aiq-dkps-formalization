/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.OperatorIdeal.Family.SchattenFinite
public import ForTauCeti.Analysis.InnerProductSpace.CompactApproximationEigenvalues

/-!
# A quantitative dimension bound for compact spectral cutoffs

A spectral band above a positive threshold contributes at least the
threshold's `p`-th power per dimension to the native Schatten power.
The bound is extended-valued, works over both fields, and does not
assume an ambient eigenbasis or separability.
-/

public section

noncomputable section

namespace TauCeti

open scoped ENNReal

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- A compact self-adjoint spectral band above `c > 0` has dimension
at most its Schatten `p`-power divided by `c^p`. The multiplicative
form includes infinite Schatten cost without division conventions. -/
theorem finrank_eigenSpan_mul_cutoff_rpow_le_schatten_rpow
    (p : ℝ) (hp : 1 ≤ p) (A : E →L[𝕜] E)
    (hAc : IsCompactOperator A) (hAs : IsSelfAdjoint A)
    (c : ℝ) (hc : 0 < c) (S : Set ℝ) (hS : ∀ s ∈ S, c ≤ s) :
    (Module.finrank 𝕜 (eigenSpan A S) : ℝ≥0∞) * ENNReal.ofReal c ^ p ≤
      (OperatorIdealFamily.schatten 𝕜 p hp).gauge A ^ p := by
  let : FiniteDimensional 𝕜 (eigenSpan A S) := finiteDimensional_eigenSpan hAc hAs hc hS
  rw [OperatorIdealFamily.gauge_schatten_rpow]
  calc
    _ = ∑ k ∈ Finset.range (Module.finrank 𝕜 (eigenSpan A S)),
        ENNReal.ofReal c ^ p := by simp
    _ ≤ ∑ k ∈ Finset.range (Module.finrank 𝕜 (eigenSpan A S)),
        (A.singularValue k : ℝ≥0∞) ^ p := by
      apply Finset.sum_le_sum
      intro k hk
      have hreal := le_approximationNumber_of_lt_rank_eigenSpan hAs hc.le hS (n := k) (by
        rw [← Module.finrank_eq_rank' 𝕜 (eigenSpan A S)]
        exact_mod_cast Finset.mem_range.mp hk)
      rw [ContinuousLinearMap.approximationNumber_eq_singularValue_toReal] at hreal
      apply ENNReal.rpow_le_rpow _ (by linarith : 0 ≤ p)
      rw [← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_le_ofReal hreal
    _ ≤ _ := ENNReal.sum_le_tsum _

end TauCeti

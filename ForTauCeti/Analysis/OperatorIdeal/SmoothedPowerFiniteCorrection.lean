/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.OperatorIdeal.SmoothedPower
public import ForTauCeti.Analysis.OperatorIdeal.ReducingTrace

/-!
# Finite unitary replacements preserve the common finite-cost domain

The existing native-ideal finite-correction theorem applies in both smoothing
regimes. This corollary uses S2 at positive smoothing and Schatten p at zero;
it adds no new ideal or perturbation theorem. The ingredients are classical
and their formal ancestry is preserved in `ReducingTrace`.
-/

public section
noncomputable section

namespace ContinuousLinearMap

open scoped ENNReal

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- A finite actual unitary replacement preserves finite family cost,
with the entire reference tail retained. Both fields and zero smoothing
are included; the natural native ideals differ between the regimes. -/
theorem smoothedPowerCost_displacement_ne_top_of_finite_restriction_and_tail
    (p tau : ℝ) (hp : 1 ≤ p) (hp2 : p ≤ 2) (htau : 0 ≤ tau)
    (M : Submodule 𝕜 E) [FiniteDimensional 𝕜 M]
    (U : E ≃ₗᵢ[𝕜] E) (R : E →L[𝕜] E) (V : M ≃ₗᵢ[𝕜] M)
    (hV : ∀ x : M, (V x : E) = U x) (htail : ∀ x ∈ Mᗮ, U x = R x)
    (hR : (1 - R).smoothedPowerCost p tau ≠ ∞) :
    (1 - (U : E →L[𝕜] E)).smoothedPowerCost p tau ≠ ∞ := by
  by_cases hz : tau = 0
  · subst tau
    rw [smoothedPowerCost_zero_smoothing p hp] at hR ⊢
    have hR' : (TauCeti.OperatorIdealFamily.schatten 𝕜 p hp).gauge (1 - R) ≠ ∞ :=
      fun h => hR ((ENNReal.rpow_eq_top_iff_of_pos (by linarith : 0 < p)).mpr h)
    have hU := gauge_schatten_displacement_ne_top_of_finite_restriction_and_ideal_tail
      p hp M U R V hV htail hR'
    exact ENNReal.rpow_ne_top_of_nonneg (by linarith) hU
  · have hpos : 0 < tau := lt_of_le_of_ne htau (Ne.symm hz)
    apply (smoothedPowerCost_ne_top_iff_schatten_two p tau (by linarith) hp2 hpos _).mpr
    apply gauge_schatten_displacement_ne_top_of_finite_restriction_and_ideal_tail
      2 (by norm_num) M U R V hV htail
    exact (smoothedPowerCost_ne_top_iff_schatten_two p tau (by linarith) hp2 hpos _).mp hR

end ContinuousLinearMap

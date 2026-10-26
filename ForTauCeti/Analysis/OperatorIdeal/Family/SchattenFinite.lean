/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import TauCeti.Analysis.OperatorIdeal.Family.Schatten
public import ForTauCeti.Analysis.InnerProductSpace.SchattenContinuity

/-!
# Finite sections of the accepted Schatten family

The extended Schatten power agrees with the finite-dimensional Schatten
seminorm power. A zero-preserving singular-value penalty has the same
finite-section interpretation. These identities connect the accepted
finite and Hilbert-space APIs without introducing a second norm.
-/

public section

noncomputable section

namespace TauCeti.OperatorIdealFamily

open scoped ENNReal NNReal

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Raising the accepted Schatten gauge to its exponent recovers the
extended singular-value power sum, even when it diverges. -/
theorem gauge_schatten_rpow (p : ℝ) (hp : 1 ≤ p) (T : E →L[𝕜] F) :
    (schatten 𝕜 p hp).gauge T ^ p = ∑' n, (T.singularValue n : ℝ≥0∞) ^ p := by
  rw [gauge_schatten, ← ENNReal.rpow_mul, one_div_mul_cancel (by linarith : p ≠ 0),
    ENNReal.rpow_one]

/-- A finite-rank map belongs to every finite-exponent Schatten ideal. -/
theorem gauge_schatten_ne_top_of_rank_le
    (p : ℝ) (hp : 1 ≤ p) (T : E →L[𝕜] F) (n : ℕ) (hT : T.rank ≤ n) :
    (schatten 𝕜 p hp).gauge T ≠ ∞ := by
  have hsum : Summable (fun k => T.singularValue k ^ p) := by
    apply summable_of_ne_finset_zero (s := Finset.range n)
    intro k hk
    rw [T.singularValue_eq_zero_of_rank_le
      (hT.trans (by exact_mod_cast Nat.le_of_not_gt (Finset.mem_range.not.mp hk)))]
    exact NNReal.zero_rpow (by linarith : p ≠ 0)
  have hmem := (mem_finiteSubmodule_schatten_iff p hp T).mpr hsum
  exact (lt_top_iff_ne_top.mp (by
    simpa only [OperatorGauge.mem_finiteSubmodule, operatorGauge_apply] using hmem))

section Finite

variable [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]

omit [CompleteSpace E] [CompleteSpace F] in
/-- A zero-preserving spectral penalty of a finite map is a finite sum,
with the ambient source dimension as index bound. -/
theorem tsum_singularValue_penalty_eq_sum
    (T : E →L[𝕜] F) (f : ℝ≥0 → ℝ≥0∞) (hf : f 0 = 0) :
    (∑' n, f (T.singularValue n)) =
      ∑ i : Fin (Module.finrank 𝕜 E), f (T.singularValue i) := by
  rw [Fin.sum_univ_eq_sum_range (fun n => f (T.singularValue n))]
  apply tsum_eq_sum
  intro n hn
  have hzero : T.singularValue n = 0 := by
    apply NNReal.coe_eq_zero.mp
    rw [ContinuousLinearMap.singularValue_eq_linearMap_singularValues]
    exact T.toLinearMap.singularValues_of_finrank_le
      (Nat.le_of_not_gt (Finset.mem_range.not.mp hn))
  rw [hzero, hf]

/-- Exact agreement between the accepted Hilbert-space Schatten power
and the accepted finite-dimensional Schatten seminorm power. -/
theorem gauge_schatten_rpow_eq_ofReal_finite
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (T : E →L[𝕜] F) :
    (schatten 𝕜 p.toReal (by
      simpa using ENNReal.toReal_mono hp (show 1 ≤ p from Fact.out))).gauge T ^ p.toReal =
      ENNReal.ofReal (UnitarilyInvariantSeminorm.schatten 𝕜 E F p T.toLinearMap ^ p.toReal) := by
  have hp1 : 1 ≤ p.toReal := by
    simpa using ENNReal.toReal_mono hp (show 1 ≤ p from Fact.out)
  have hp0 : 0 < p.toReal := zero_lt_one.trans_le hp1
  rw [gauge_schatten_rpow, tsum_singularValue_penalty_eq_sum T
    (fun s => (s : ℝ≥0∞) ^ p.toReal) (ENNReal.zero_rpow_of_pos hp0),
    TauCeti.schatten_rpow_eq_sum_singularValue p hp T,
    ENNReal.ofReal_sum_of_nonneg (fun _ _ => Real.rpow_nonneg (NNReal.coe_nonneg _) _)]
  apply Finset.sum_congr rfl
  intro i _
  rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_rpow_of_nonneg (NNReal.coe_nonneg _) hp0.le]

end Finite

end TauCeti.OperatorIdealFamily

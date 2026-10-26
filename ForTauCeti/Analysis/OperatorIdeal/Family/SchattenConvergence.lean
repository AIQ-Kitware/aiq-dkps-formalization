/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import TauCeti.Analysis.OperatorIdeal.Family.Schatten
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Compact
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Dominated convergence in finite-exponent Schatten ideals

Operator-norm convergence to zero upgrades to Schatten convergence when
the approximation numbers are dominated by one fixed Schatten operator.
The proof applies dominated convergence to the real singular-value power
sum and then takes its positive root. All gauges are the accepted Tau
Ceti gauges, including their extended values.

## Provenance

Classical dominated convergence for trace ideals, implemented here for
the DKPS finite-rank unitary approximation argument. This is a new Lean
implementation, not a claim of new mathematical priority.
-/

public section

namespace TauCeti.OperatorIdealFamily

open Filter
open scoped Topology ENNReal NNReal

universe u v w

variable {𝕜 : Type u} [RCLike 𝕜] {E : Type v} {F : Type w}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Singular-value domination by a fixed Schatten operator upgrades
operator-norm convergence to zero to Schatten-gauge convergence. The
ambient Hilbert spaces and the parameter filter are arbitrary. -/
theorem tendsto_gauge_schatten_zero_of_singularValue_le
    (p : ℝ) (hp : 1 ≤ p) (A : E →L[𝕜] F)
    (hA : (schatten 𝕜 p hp).gauge A ≠ ∞)
    {α : Type*} {l : Filter α} (T : α → E →L[𝕜] F)
    (hT : Tendsto T l (𝓝 0))
    (hdom : ∀ n k, (T n).singularValue k ≤ A.singularValue k) :
    Tendsto (fun n => (schatten 𝕜 p hp).gauge (T n)) l (𝓝 0) := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hsumNN : Summable (fun k => A.singularValue k ^ p) := by
    apply (mem_finiteSubmodule_schatten_iff p hp A).mp
    simp only [OperatorGauge.mem_finiteSubmodule, operatorGauge_apply]
    exact lt_top_iff_ne_top.mpr hA
  have hsum : Summable (fun k => (A.singularValue k : ℝ) ^ p) := by
    simpa only [NNReal.coe_rpow] using NNReal.summable_coe.mpr hsumNN
  have hpoint (k : ℕ) :
      Tendsto (fun n => ((T n).singularValue k : ℝ) ^ p) l (𝓝 0) := by
    have hsv : Tendsto (fun n => ((T n).singularValue k : ℝ)) l (𝓝 0) := by
      simpa only [Function.comp_def, ContinuousLinearMap.zero_singularValue, NNReal.coe_zero]
        using ((NNReal.continuous_coe.comp
          (ContinuousLinearMap.continuous_singularValue k)).tendsto 0).comp hT
    have h := ((Real.continuous_rpow_const hp0.le).tendsto 0).comp hsv
    simpa only [Function.comp_def, ContinuousLinearMap.zero_singularValue, NNReal.coe_zero,
      Real.zero_rpow hp0.ne'] using h
  have hbound (n : α) (k : ℕ) :
      ‖((T n).singularValue k : ℝ) ^ p‖ ≤ (A.singularValue k : ℝ) ^ p := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)]
    exact Real.rpow_le_rpow (NNReal.coe_nonneg _) (NNReal.coe_le_coe.mpr (hdom n k)) hp0.le
  have hlim := tendsto_tsum_of_dominated_convergence hsum hpoint
    (Eventually.of_forall hbound)
  simp only [tsum_zero] at hlim
  have hsumT (n : α) : Summable (fun k => ((T n).singularValue k : ℝ) ^ p) :=
    hsum.of_norm_bounded (hbound n)
  have hvalue (n : α) : (schatten 𝕜 p hp).gauge (T n) =
      ENNReal.ofReal (∑' k, ((T n).singularValue k : ℝ) ^ p) ^ (1/p) := by
    rw [gauge_schatten]
    congr 1
    rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => Real.rpow_nonneg (NNReal.coe_nonneg _) _)
      (hsumT n)]
    apply tsum_congr
    intro k
    rw [← ENNReal.ofReal_rpow_of_nonneg (NNReal.coe_nonneg _) hp0.le,
      ENNReal.ofReal_coe_nnreal]
  simp_rw [hvalue]
  have hof : Tendsto (fun n => ENNReal.ofReal (∑' k, ((T n).singularValue k : ℝ) ^ p))
      l (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.tendsto (0 : ℝ) |>.comp hlim
  have h := ((ENNReal.continuous_rpow_const (y := 1/p)).tendsto (0 : ℝ≥0∞)).comp hof
  simpa only [Function.comp_def, ENNReal.zero_rpow_of_pos (one_div_pos.mpr hp0)] using h

/-- Every member of a finite-exponent Schatten ideal is compact, in
arbitrary Hilbert dimension. The proof uses the summable approximation
numbers rather than a separable spectral representation. -/
theorem isCompactOperator_of_gauge_schatten_ne_top
    (p : ℝ) (hp : 1 ≤ p) (A : E →L[𝕜] F)
    (hA : (schatten 𝕜 p hp).gauge A ≠ ∞) : IsCompactOperator A := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hsum : Summable (fun k => A.singularValue k ^ p) := by
    apply (mem_finiteSubmodule_schatten_iff p hp A).mp
    simp only [OperatorGauge.mem_finiteSubmodule, operatorGauge_apply]
    exact lt_top_iff_ne_top.mpr hA
  apply ContinuousLinearMap.isCompactOperator_iff_tendsto_singularValue.mpr
  have hreal : Summable (fun n => (A.singularValue n : ℝ) ^ p) := by
    simpa only [NNReal.coe_rpow] using NNReal.summable_coe.mpr hsum
  have hpow := hreal.tendsto_atTop_zero
  have h := ((Real.continuous_rpow_const (one_div_pos.mpr hp0).le).tendsto 0).comp hpow
  have hroot (n : ℕ) : ((A.singularValue n : ℝ) ^ p) ^ (1/p) = A.singularValue n := by
    rw [← Real.rpow_mul (NNReal.coe_nonneg _), mul_one_div_cancel hp0.ne', Real.rpow_one]
  apply NNReal.tendsto_coe.mp
  simpa only [Function.comp_def, hroot, Real.zero_rpow (one_div_ne_zero hp0.ne'), NNReal.coe_zero]
    using h

end TauCeti.OperatorIdealFamily

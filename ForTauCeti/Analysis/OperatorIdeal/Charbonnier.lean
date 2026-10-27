/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.OperatorIdeal.Family.SchattenFinite
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The ideal domain of the Charbonnier spectral penalty

The renormalized trace of `sqrt(tau^2 + |T|^2) - tau` is finite exactly
on the Hilbert--Schmidt ideal, for every positive smoothing scale.
Explicit quadratic bounds use the finite operator norm to control the
denominator in the rationalized scalar penalty. The cost is a spectral
penalty, not a second operator-ideal norm.
-/

public section

noncomputable section

namespace TauCeti

/-- On a bounded interval, the Charbonnier penalty has two-sided
quadratic bounds. These include the zero singular value exactly. -/
theorem charbonnier_quadratic_bounds (tau s M : ℝ) (hτ : 0 < tau)
    (hs : 0 ≤ s) (hsM : s ≤ M) :
    s ^ 2 ≤ (Real.sqrt (tau ^ 2 + M ^ 2) + tau) *
        (Real.sqrt (tau ^ 2 + s ^ 2) - tau) ∧
      Real.sqrt (tau ^ 2 + s ^ 2) - tau ≤ (2 * tau)⁻¹ * s ^ 2 := by
  have hr := Real.sq_sqrt (show 0 ≤ tau ^ 2 + s ^ 2 by positivity)
  have hr0 := Real.sqrt_nonneg (tau ^ 2 + s ^ 2)
  have hτr : tau ≤ Real.sqrt (tau ^ 2 + s ^ 2) := by nlinarith [sq_nonneg s]
  have hrM : Real.sqrt (tau ^ 2 + s ^ 2) ≤ Real.sqrt (tau ^ 2 + M ^ 2) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have hcost : 0 ≤ Real.sqrt (tau ^ 2 + s ^ 2) - tau := sub_nonneg.mpr hτr
  have hprod : (Real.sqrt (tau ^ 2 + s ^ 2) + tau) *
      (Real.sqrt (tau ^ 2 + s ^ 2) - tau) = s ^ 2 := by nlinarith
  constructor
  · calc
      _ = (Real.sqrt (tau ^ 2 + s ^ 2) + tau) *
          (Real.sqrt (tau ^ 2 + s ^ 2) - tau) := hprod.symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith :
        Real.sqrt (tau ^ 2 + s ^ 2) + tau ≤
          Real.sqrt (tau ^ 2 + M ^ 2) + tau) hcost
  · rw [inv_mul_eq_div]
    apply (le_div_iff₀ (by linarith : 0 < 2 * tau)).mpr
    calc
      _ ≤ (Real.sqrt (tau ^ 2 + s ^ 2) + tau) *
          (Real.sqrt (tau ^ 2 + s ^ 2) - tau) := by nlinarith
      _ = _ := hprod

end TauCeti

namespace ContinuousLinearMap

open scoped ENNReal

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The extended renormalized Charbonnier spectral trace. In infinite
dimension its baseline is subtracted inside each summand, so no
undefined subtraction of infinite traces occurs. -/
@[expose] def charbonnierCost (tau : ℝ) (T : E →L[𝕜] F) : ℝ≥0∞ :=
  ∑' n, ENNReal.ofReal (Real.sqrt (tau ^ 2 + (T.singularValue n : ℝ) ^ 2) - tau)

omit [CompleteSpace E] [CompleteSpace F] in
/-- Pointwise singular-value domination decreases the Charbonnier
spectral cost, for any scale and including infinite sums. -/
theorem charbonnierCost_le_of_singularValue_le (tau : ℝ) (A B : E →L[𝕜] F)
    (h : ∀ n, A.singularValue n ≤ B.singularValue n) :
    A.charbonnierCost tau ≤ B.charbonnierCost tau := by
  apply ENNReal.tsum_le_tsum
  intro n
  apply ENNReal.ofReal_le_ofReal
  apply sub_le_sub_right
  apply Real.sqrt_le_sqrt
  have hn : (A.singularValue n : ℝ) ≤ (B.singularValue n : ℝ) := by exact_mod_cast h n
  nlinarith [NNReal.coe_nonneg (A.singularValue n), NNReal.coe_nonneg (B.singularValue n)]

/-- The Hilbert--Schmidt square is bounded by a finite multiple of the
Charbonnier trace, with the exact denominator bound from the operator norm. -/
theorem schatten_two_sq_le_mul_charbonnierCost (tau : ℝ) (hτ : 0 < tau) (T : E →L[𝕜] F) :
    (TauCeti.OperatorIdealFamily.schatten 𝕜 2 (by norm_num)).gauge T ^ (2 : ℝ) ≤
      ENNReal.ofReal (Real.sqrt (tau ^ 2 + ‖T‖ ^ 2) + tau) * T.charbonnierCost tau := by
  rw [TauCeti.OperatorIdealFamily.gauge_schatten_rpow, charbonnierCost, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro n
  have hs : 0 ≤ (T.singularValue n : ℝ) := NNReal.coe_nonneg _
  have hsM : (T.singularValue n : ℝ) ≤ ‖T‖ := by exact_mod_cast T.singularValue_le_nnnorm n
  have h := ENNReal.ofReal_le_ofReal (TauCeti.charbonnier_quadratic_bounds
    tau (T.singularValue n : ℝ) ‖T‖ hτ hs hsM).1
  rw [ENNReal.ofReal_pow hs, ENNReal.ofReal_coe_nnreal,
    ENNReal.ofReal_mul (by positivity)] at h
  simpa only [ENNReal.rpow_two] using h

/-- The Charbonnier trace is bounded by the Hilbert--Schmidt square
divided by twice the positive smoothing scale. -/
theorem charbonnierCost_le_mul_schatten_two_sq (tau : ℝ) (hτ : 0 < tau) (T : E →L[𝕜] F) :
    T.charbonnierCost tau ≤ ENNReal.ofReal ((2 * tau)⁻¹) *
      (TauCeti.OperatorIdealFamily.schatten 𝕜 2 (by norm_num)).gauge T ^ (2 : ℝ) := by
  rw [TauCeti.OperatorIdealFamily.gauge_schatten_rpow, charbonnierCost, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro n
  have hs : 0 ≤ (T.singularValue n : ℝ) := NNReal.coe_nonneg _
  have hsM : (T.singularValue n : ℝ) ≤ ‖T‖ := by exact_mod_cast T.singularValue_le_nnnorm n
  have h := ENNReal.ofReal_le_ofReal (TauCeti.charbonnier_quadratic_bounds
    tau (T.singularValue n : ℝ) ‖T‖ hτ hs hsM).2
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hs,
    ENNReal.ofReal_coe_nnreal] at h
  simpa only [ENNReal.rpow_two] using h

/-- **The correct ideal for the smoothed penalty.** At every positive
smoothing scale the Charbonnier spectral trace is finite exactly for
Hilbert--Schmidt operators, in arbitrary Hilbert dimensions. -/
theorem charbonnierCost_ne_top_iff_schatten_two (tau : ℝ) (hτ : 0 < tau) (T : E →L[𝕜] F) :
    T.charbonnierCost tau ≠ ∞ ↔
      (TauCeti.OperatorIdealFamily.schatten 𝕜 2 (by norm_num)).gauge T ≠ ∞ := by
  constructor
  · intro hcost htop
    have h := T.schatten_two_sq_le_mul_charbonnierCost tau hτ
    rw [htop, ENNReal.top_rpow_of_pos (by norm_num : (0 : ℝ) < 2)] at h
    exact (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hcost) (top_unique h)
  · intro hT
    have hsquare :
        (TauCeti.OperatorIdealFamily.schatten 𝕜 2 (by norm_num)).gauge T ^ (2 : ℝ) ≠ ∞ := by
      rw [ENNReal.rpow_two, pow_two]
      exact ENNReal.mul_ne_top hT hT
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hsquare)
      (T.charbonnierCost_le_mul_schatten_two_sq tau hτ)

omit [CompleteSpace E] [CompleteSpace F] in
/-- At every nonnegative smoothing scale, the native extended
Charbonnier trace vanishes exactly at the zero operator. -/
theorem charbonnierCost_eq_zero_iff (tau : ℝ) (hτ : 0 ≤ tau) (T : E →L[𝕜] F) :
    T.charbonnierCost tau = 0 ↔ T = 0 := by
  constructor
  · intro hzero
    have h := ENNReal.le_tsum (f := fun n : ℕ => ENNReal.ofReal
      (Real.sqrt (tau ^ 2 + (T.singularValue n : ℝ) ^ 2) - tau)) 0
    change ENNReal.ofReal (Real.sqrt (tau ^ 2 + (T.singularValue 0 : ℝ) ^ 2) - tau) ≤
      T.charbonnierCost tau at h
    rw [hzero] at h
    have hle := ENNReal.ofReal_eq_zero.mp (le_antisymm h bot_le)
    rw [ContinuousLinearMap.singularValue_zero] at hle
    change Real.sqrt (tau ^ 2 + ‖T‖ ^ 2) - tau ≤ 0 at hle
    have hs := Real.sq_sqrt (show 0 ≤ tau ^ 2 + ‖T‖ ^ 2 by positivity)
    have hr := Real.sqrt_nonneg (tau ^ 2 + ‖T‖ ^ 2)
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg T]
  · rintro rfl
    simp [charbonnierCost, Real.sqrt_sq hτ]

end ContinuousLinearMap

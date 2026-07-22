/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.Sources.DavisKahan1970.Section9.NumericalBounds

/-!
# Davis--Kahan 1970, Section 9: Weinberger comparison

The historical comparison uses independent lower eigenvalue bounds.  This file
formalizes the algebraic conversion from a sine-square estimate to a tangent-
square estimate and records the exact arrowhead comparison polynomial.  The
asymptotic expansion mentioned in the paper is intentionally not encoded;
constructing certified roots of the comparison polynomial is the correct
future interface.
-/

namespace ForMathlib
namespace DavisKahan1970
namespace Section9

/-- The symmetric three-by-three arrowhead data used in the comparison with
Weinberger and Lehmann. -/
structure ArrowheadThreeByThree where
  diagonal₀ : ℝ
  diagonal₁ : ℝ
  tail : ℝ
  coupling₀ : ℝ
  coupling₁ : ℝ

namespace ArrowheadThreeByThree

/-- Characteristic polynomial of the arrowhead matrix, evaluated at `lam`. -/
def charAt (M : ArrowheadThreeByThree) (lam : ℝ) : ℝ :=
  (M.diagonal₀ - lam) * (M.diagonal₁ - lam) * (M.tail - lam)
    - M.coupling₀ ^ 2 * (M.diagonal₁ - lam)
    - M.coupling₁ ^ 2 * (M.diagonal₀ - lam)

end ArrowheadThreeByThree

/-- The exact comparison matrix from Section 9. -/
noncomputable def weinbergerComparisonMatrix (ε : ℝ) : ArrowheadThreeByThree where
  diagonal₀ := ritzLow ε
  diagonal₁ := ritzHigh ε
  tail := 500
  coupling₀ := ε * (Real.sqrt 30 / 30)
  coupling₁ := ε * (Real.sqrt 30 / 30)

lemma weinbergerComparisonMatrix_charAt (ε lam : ℝ) :
    (weinbergerComparisonMatrix ε).charAt lam =
      (ritzLow ε - lam) * (ritzHigh ε - lam) * (500 - lam)
        - (ε ^ 2 / 30) * (ritzHigh ε - lam)
        - (ε ^ 2 / 30) * (ritzLow ε - lam) := by
  have hs : Real.sqrt (30 : ℝ) ^ 2 = 30 := Real.sq_sqrt (by norm_num)
  unfold weinbergerComparisonMatrix ArrowheadThreeByThree.charAt
  dsimp
  -- the two sides differ only by `(ε * (√30 / 30)) ^ 2` versus `ε ^ 2 / 30`,
  -- multiplied against each of the two shifted diagonal entries
  linear_combination
    (-(ε ^ 2) / 900 * (ritzHigh ε - lam + (ritzLow ε - lam))) * hs

/-- A certified pair of lower roots for the comparison matrix.  This is the
precise boundary replacing the informal fourth-order expansion in the source
discussion. -/
structure WeinbergerLowerRootCertificate (ε : ℝ) where
  lower₀ : ℝ
  lower₁ : ℝ
  ordered : lower₀ ≤ lower₁
  lower₀_is_root : (weinbergerComparisonMatrix ε).charAt lower₀ = 0
  lower₁_is_root : (weinbergerComparisonMatrix ε).charAt lower₁ = 0
  lower₀_le_ritz : lower₀ ≤ ritzLow ε
  lower₁_le_ritz : lower₁ ≤ ritzHigh ε
  lower₁_lt_tail : lower₁ < 500

/-- Weinberger's sine-square estimate algebraically implies the corresponding
tangent-square estimate. -/
theorem tangent_sq_le_of_weinberger_sine_sq
    {s alphaCheck alphaHat gap : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hcheck : alphaCheck ≤ alphaHat) (hhat : alphaHat < gap)
    (hweinberger : s ^ 2 ≤
      (alphaHat - alphaCheck) / (gap - alphaCheck)) :
    s ^ 2 / (1 - s ^ 2) ≤
      (alphaHat - alphaCheck) / (gap - alphaHat) := by
  have hgapCheck : 0 < gap - alphaCheck := by linarith
  have hgapHat : 0 < gap - alphaHat := by linarith
  have hsden : 0 < 1 - s ^ 2 := by nlinarith [sq_nonneg s]
  have hcross : s ^ 2 * (gap - alphaCheck) ≤ alphaHat - alphaCheck :=
    (le_div_iff₀ hgapCheck).mp hweinberger
  apply (div_le_div_iff₀ hsden hgapHat).2
  nlinarith

/-- Exact normalized envelope for the first historical comparison bound. -/
noncomputable def weinbergerLowerTangentExactBound (ε : ℝ) : ℝ :=
  ((Real.sqrt 15 / 15) / 500 * ε) /
    (1 - (ritzLowCoefficient / 500) * ε)

/-- Exact normalized envelope for the second historical comparison bound. -/
noncomputable def weinbergerUpperTangentExactBound (ε : ℝ) : ℝ :=
  tangentThetaExactBound ε

private theorem historical_ratio_bound
    {ε c C : ℝ} (hε : 0 < ε)
    (hc : c ≤ C) (hC : C * ε < 1) :
    (((Real.sqrt 15 / 15) / 500) * ε) / (1 - c * ε) <
      ((1291 : ℝ) / 2500000 * ε) / (1 - C * ε) := by
  have hs15 : Real.sqrt 15 < (3873 : ℝ) / 1000 := by
    nlinarith [Real.sqrt_nonneg (15 : ℝ),
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 15)]
  have ha : (Real.sqrt 15 / 15) / 500 < (1291 : ℝ) / 2500000 := by
    nlinarith
  have hdC : 0 < 1 - C * ε := by linarith
  have hdc : 0 < 1 - c * ε := by nlinarith
  have hfirst :
      (((Real.sqrt 15 / 15) / 500) * ε) / (1 - c * ε) <
        ((1291 : ℝ) / 2500000 * ε) / (1 - c * ε) := by
    apply div_lt_div_of_pos_right _ hdc
    exact mul_lt_mul_of_pos_right ha hε
  have hden : 1 - C * ε ≤ 1 - c * ε := by nlinarith
  have hnum0 : 0 ≤ (1291 : ℝ) / 2500000 * ε := by positivity
  have hsecond :
      ((1291 : ℝ) / 2500000 * ε) / (1 - c * ε) ≤
        ((1291 : ℝ) / 2500000 * ε) / (1 - C * ε) := by
    apply (div_le_div_iff₀ hdc hdC).2
    exact mul_le_mul_of_nonneg_left hden hnum0
  exact hfirst.trans_le hsecond

/-- First line of equation (9.8), conditional on the exact comparison bound. -/
theorem equation_9_8_lower
    (ε tanPhi₁ : ℝ) (hε : 0 < ε) (hε100 : ε < 100)
    (h : tanPhi₁ ≤ weinbergerLowerTangentExactBound ε) :
    tanPhi₁ <
      ((1291 : ℝ) / 2500000 * ε) /
        (1 - (4227 : ℝ) / 10000000 * ε) := by
  apply h.trans_lt
  unfold weinbergerLowerTangentExactBound
  apply historical_ratio_bound hε
  · nlinarith [ritzLowCoefficient_lt_printed]
  · nlinarith

/-- Second line of equation (9.8), conditional on the exact comparison bound. -/
theorem equation_9_8_upper
    (ε tanPhi₂ : ℝ) (hε : 0 < ε) (hε100 : ε < 100)
    (h : tanPhi₂ ≤ weinbergerUpperTangentExactBound ε) :
    tanPhi₂ <
      ((1291 : ℝ) / 2500000 * ε) /
        (1 - (7887 : ℝ) / 5000000 * ε) := by
  apply h.trans_lt
  unfold weinbergerUpperTangentExactBound
  exact tangentThetaExactBound_lt_printed ε hε hε100

end Section9
end DavisKahan1970
end ForMathlib

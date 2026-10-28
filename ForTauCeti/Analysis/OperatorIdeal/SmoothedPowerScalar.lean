/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Quadratic comparison for the common smoothed-power penalty

Positive smoothing makes every positive subquadratic power comparable to
squared displacement on bounded intervals. The proof is the ordinary mean
value theorem applied to a positive real power. These classical scalar
bounds identify the native ideal; no new ideal norm is introduced.
The generalized Charbonnier scalar family is established prior art, as
recorded in S13 of `dev/spectral-transport-unification.md`.
-/

public section

namespace TauCeti

/-- Normalization of the common scalar formula, including zero smoothing. -/
theorem smoothedPower_scalar_zero (p tau : ℝ) (htau : 0 ≤ tau) :
    (tau ^ 2 + (0 : ℝ) ^ 2) ^ (p / 2) - tau ^ p = 0 := by
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero]
  rw [← Real.rpow_natCast_mul htau]
  rw [show (2 : ℕ) * (p / 2) = p by norm_num; ring, sub_self]

/-- **The common quadratic comparison.** The constants are positive
when p and smoothing are positive. The bound includes s=0 exactly. -/
theorem smoothedPower_quadratic_bounds (p tau s M : ℝ)
    (hp : 0 < p) (hp2 : p ≤ 2) (htau : 0 < tau) (hs : 0 ≤ s) (hsM : s ≤ M) :
    (p / 2) * (tau ^ 2 + M ^ 2) ^ (p / 2 - 1) * s ^ 2 ≤
        (tau ^ 2 + s ^ 2) ^ (p / 2) - tau ^ p ∧
      (tau ^ 2 + s ^ 2) ^ (p / 2) - tau ^ p ≤
        (p / 2) * (tau ^ 2) ^ (p / 2 - 1) * s ^ 2 := by
  have hbase : 0 < tau ^ 2 := sq_pos_of_pos htau
  have hnorm : (tau ^ 2) ^ (p / 2) = tau ^ p := by
    rw [← Real.rpow_natCast_mul htau.le]
    congr 1
    norm_num
    ring
  by_cases hz : s = 0
  · subst s
    simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero, mul_zero, hnorm, sub_self,
      le_refl, and_self]
  have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hz)
  have hinterval : tau ^ 2 < tau ^ 2 + s ^ 2 := by nlinarith [sq_pos_of_pos hspos]
  have hcont : ContinuousOn (fun x : ℝ => x ^ (p / 2)) (Set.Icc (tau ^ 2) (tau ^ 2 + s ^ 2)) :=
    (Real.continuous_rpow_const (by linarith : 0 ≤ p / 2)).continuousOn
  have hderiv : ∀ x ∈ Set.Ioo (tau ^ 2) (tau ^ 2 + s ^ 2),
      HasDerivAt (fun x : ℝ => x ^ (p / 2)) ((p / 2) * x ^ (p / 2 - 1)) x := by
    intro x hx
    exact Real.hasDerivAt_rpow_const (Or.inl (hbase.trans hx.1).ne')
  obtain ⟨x, hx, heq⟩ := exists_hasDerivAt_eq_slope _ _ hinterval hcont hderiv
  have hvalue : (tau ^ 2 + s ^ 2) ^ (p / 2) - tau ^ p =
      (p / 2) * x ^ (p / 2 - 1) * s ^ 2 := by
    rw [hnorm] at heq
    have hden : tau ^ 2 + s ^ 2 - tau ^ 2 = s ^ 2 := by ring
    rw [hden] at heq
    exact ((eq_div_iff (sq_pos_of_pos hspos).ne').mp heq).symm
  have hxpos : 0 < x := hbase.trans hx.1
  have hxM : x ≤ tau ^ 2 + M ^ 2 := by nlinarith [hx.2, hsM, hs]
  have hlow := Real.rpow_le_rpow_of_nonpos hxpos hxM (by linarith : p / 2 - 1 ≤ 0)
  have hhigh := Real.rpow_le_rpow_of_nonpos hbase hx.1.le (by linarith : p / 2 - 1 ≤ 0)
  rw [hvalue]
  exact ⟨mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlow (by linarith)) (sq_nonneg s),
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hhigh (by linarith)) (sq_nonneg s)⟩

end TauCeti

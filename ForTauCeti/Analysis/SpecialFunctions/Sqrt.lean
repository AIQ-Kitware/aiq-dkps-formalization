/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5, Claude Opus 4.8, Claude Opus 5
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Elementary square-root estimates near `1`

Two scalar inequalities controlling how far `√μ` and `(√μ)⁻¹` move away from `1`
when `μ` is close to `1`.  They are the scalar content behind the operator
near-isometry estimates in
`ForTauCeti/Analysis/InnerProductSpace/PolarIsometry.lean` and
`ForTauCeti/Analysis/InnerProductSpace/NearIsometry.lean`: an operator whose
Gram operator is `δ`-close to the identity has all of its spectral data in
`[1 - δ, 1 + δ]`, and these lemmas turn that into a bound on the associated
square-root rescaling.

Both are staged for `Mathlib/Analysis/SpecialFunctions/Sqrt.lean`; they are
collected in their own module (rather than next to their operator-theoretic
consumers) so that the real and complex near-isometry developments can share
them without either importing the other.

## Main results

* `Real.abs_sqrt_sub_one_le_abs_sub_one`: `|√μ - 1| ≤ |μ - 1|` for every
  real `μ`.  For `μ ≤ 0` the square root vanishes; for `μ ≥ 0` the estimate
  follows from `(√μ - 1) (√μ + 1) = μ - 1`.  It makes the operator estimate
  `‖|M| - 1‖ ≤ ‖M⋆ M - 1‖` lossless.
* `Real.abs_one_sub_inv_sqrt_le`: `|1 - (√μ)⁻¹| ≤ δ` when
  `|μ - 1| ≤ δ ≤ 1 / 2`.  The *inverse* square root genuinely needs a smallness
  hypothesis (as `μ ↓ 0` the left-hand side blows up), which is why the
  factorization-based proofs prefer the first lemma.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* `abs_one_sub_inv_sqrt_le` was originally
  `ForMathlib.Real.abs_one_sub_inv_sqrt_le` in
  `ForMathlib/Analysis/InnerProductSpace/NearIsometry.lean` at Davis--Kahan
  commit `9b69db43` (formalized by Claude Fable 5; refined in `3329b60e`
  by Claude Opus 4.8), then moved here with the `Real.sqrt` API.
* `abs_sqrt_sub_one_le_abs_sub_one` is **new**.
* Spectra influence: **none** — this module imports only Mathlib.
-/

public section

namespace Real

/-- For every real `μ`, the square root is no farther from `1` than `μ` is:
`|√μ - 1| ≤ |μ - 1|`. -/
theorem abs_sqrt_sub_one_le_abs_sub_one {μ : ℝ} :
    |Real.sqrt μ - 1| ≤ |μ - 1| := by
  rcases le_total 0 μ with hμ | hμ
  · have hs : 0 ≤ Real.sqrt μ := Real.sqrt_nonneg μ
    have hsq : Real.sqrt μ * Real.sqrt μ = μ := Real.mul_self_sqrt hμ
    have key : |Real.sqrt μ - 1| * (Real.sqrt μ + 1) = |μ - 1| := by
      rw [← abs_of_nonneg (by linarith : (0 : ℝ) ≤ Real.sqrt μ + 1), ← abs_mul]
      congr 1
      nlinarith [hsq]
    nlinarith [key, mul_nonneg (abs_nonneg (Real.sqrt μ - 1)) hs]
  · have hsqrt : Real.sqrt μ = 0 := Real.sqrt_eq_zero_of_nonpos hμ
    calc
      |Real.sqrt μ - 1| = 1 := by rw [hsqrt]; norm_num
      _ ≤ |μ - 1| := by
        rw [abs_of_nonpos (by linarith : μ - 1 ≤ 0)]
        linarith

/-- If `|μ - 1| ≤ δ ≤ 1 / 2`, then `|1 - (√μ)⁻¹| ≤ δ`.

The point: `1 - (√μ)⁻¹ = (μ - 1) / (μ + √μ)` and the denominator `μ + √μ ≥ 1`
when `μ ≥ 1 / 2`.

Unlike `Real.abs_sqrt_sub_one_le_abs_sub_one`, a smallness hypothesis on
`δ` is unavoidable here: `(√μ)⁻¹ → ∞` as `μ ↓ 0`.  Nonnegativity of `δ` is not
assumed separately — it is forced by `hμ`, since `0 ≤ |μ - 1| ≤ δ`. -/
theorem abs_one_sub_inv_sqrt_le {μ δ : ℝ} (hδ : δ ≤ 1 / 2) (hμ : |μ - 1| ≤ δ) :
    |1 - (Real.sqrt μ)⁻¹| ≤ δ := by
  have hμlb : 1 - δ ≤ μ := by rw [abs_le] at hμ; linarith
  have hμpos : (0 : ℝ) < μ := by linarith
  set s := Real.sqrt μ
  have hs0 : 0 < s := Real.sqrt_pos.mpr hμpos
  have hssq : s ^ 2 = μ := Real.sq_sqrt (le_of_lt hμpos)
  -- `s ≥ 1/2` (since `s² = μ ≥ 1/2`)
  have hssqlb : (1 : ℝ) / 2 ≤ s ^ 2 := by rw [hssq]; linarith
  have hsge : (1 : ℝ) / 2 ≤ s := by nlinarith [hs0, hssqlb]
  have hδ0 : 0 ≤ δ := le_trans (abs_nonneg _) hμ
  rw [abs_le] at hμ ⊢
  obtain ⟨hμ1, hμ2⟩ := hμ
  have hssq' : s * s = μ := by nlinarith [hssq]
  -- Lower bound `1 ≤ (1 + δ) * s`: its square is `(1 + δ)² μ ≥ (1 + δ)² (1 - δ) ≥ 1`.
  have hlow : 1 ≤ (1 + δ) * s := by
    have hpos : 0 < (1 + δ) * s := by positivity
    nlinarith [hpos, hssq', hμ1, hμ2, hδ0, hsge, mul_nonneg hδ0 hδ0,
      mul_nonneg (mul_nonneg hδ0 hδ0) hδ0]
  -- Upper bound `(1 - δ) * s ≤ 1`: equivalently `(1 - δ)² μ ≤ 1` when `1 - δ ≥ 0`.
  have hhigh : (1 - δ) * s ≤ 1 := by
    rcases le_or_gt (1 - δ) 0 with h | h
    · nlinarith [hs0, h]
    · nlinarith [hssq', hμ1, hμ2, hδ0, hsge, h, mul_nonneg hδ0 hδ0]
  -- Translate the two multiplicative bounds into bounds on `s⁻¹`.
  have hinv_le : s⁻¹ ≤ 1 + δ := by
    rw [inv_eq_one_div, div_le_iff₀ hs0]; linarith [hlow]
  have hle_inv : 1 - δ ≤ s⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hs0]; linarith [hhigh]
  exact ⟨by linarith [hinv_le], by linarith [hle_inv]⟩

end Real

end

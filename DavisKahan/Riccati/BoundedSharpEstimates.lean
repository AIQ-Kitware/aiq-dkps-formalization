/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 Thinking
-/
import DavisKahan.Riccati.BoundedEstimates

/-!
# Sharp contractive-branch majorant for bounded Riccati solutions

This leaf module solves the scalar quadratic inequality produced by the
interval/exterior Sylvester estimate.  On the contractive branch, the solution
norm is bounded by the smaller root of the Riccati majorant polynomial.

The result is stated in an algebraic square-root form.  This keeps the operator
argument independent of trigonometric normalization and exposes the exact
scalar endpoint needed by later continuation and branch-selection proofs.
-/

namespace TauCeti
namespace DavisKahanExt

open scoped InnerProductSpace

variable {E0 : Type*} [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
  [CompleteSpace E0]
variable {E1 : Type*} [NormedAddCommGroup E1] [InnerProductSpace ℂ E1]
  [CompleteSpace E1]

/-- The contractive branch of `d * t ≤ b * (1 + t ^ 2)` lies below the
smaller root of the associated quadratic polynomial. -/
theorem le_riccati_small_root_of_quadratic
    {b d t : ℝ}
    (hb : 0 ≤ b) (hd : 0 < d) (hsmall : 2 * b < d)
    (ht1 : t < 1)
    (hquad : d * t ≤ b * (1 + t ^ 2)) :
    t ≤ 2 * b / (d + Real.sqrt (d ^ 2 - 4 * b ^ 2)) := by
  have hsumpos : 0 < d + 2 * b := by
    nlinarith
  have hdiscpos : 0 < d ^ 2 - 4 * b ^ 2 := by
    have hprod := mul_pos (sub_pos.mpr hsmall) hsumpos
    nlinarith
  have hdisc : 0 ≤ d ^ 2 - 4 * b ^ 2 := le_of_lt hdiscpos
  let s : ℝ := Real.sqrt (d ^ 2 - 4 * b ^ 2)
  let r : ℝ := 2 * b / (d + s)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = d ^ 2 - 4 * b ^ 2 := by
    dsimp [s]
    exact Real.sq_sqrt hdisc
  have hden : 0 < d + s := by
    linarith
  have hr1 : r < 1 := by
    dsimp [r]
    apply (div_lt_one hden).2
    linarith
  have hroot : b * (1 + r ^ 2) = d * r := by
    dsimp [r]
    field_simp [ne_of_gt hden]
    nlinarith [hs2]
  by_contra hnot
  have hrt : r < t := lt_of_not_ge hnot
  have hsum : t + r < 2 := by
    linarith
  have hcoef : b * (t + r) - d < 0 := by
    have hmul : b * (t + r) ≤ b * 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hsum) hb
    nlinarith
  have hfactor :
      b * (1 + t ^ 2) - d * t =
        (b * (1 + r ^ 2) - d * r) +
          (t - r) * (b * (t + r) - d) := by
    ring
  have hprod : (t - r) * (b * (t + r) - d) < 0 :=
    mul_neg_of_pos_of_neg (sub_pos.mpr hrt) hcoef
  have hneg : b * (1 + t ^ 2) - d * t < 0 := by
    rw [hfactor]
    nlinarith [hroot, hprod]
  nlinarith

/-- A contractive bounded Riccati solution lies below the smaller root of the
quadratic interval/exterior majorant. -/
theorem norm_riccati_solution_le_small_root_of_contractive_spectrum_gap
    (H : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {left right d : ℝ} (hd : 0 < d) (hlr : left ≤ right)
    (hA0spec : spectrum ℝ H.A0 ⊆ Set.Icc left right)
    (hA1spec : ∀ x ∈ spectrum ℝ H.A1,
      x ≤ left - d ∨ right + d ≤ x)
    (hsmall : 2 * ‖H.B01‖ < d)
    {X : E0 →L[ℂ] E1} (hX : SolvesRiccati H X)
    (hXc : ‖X‖ < 1) :
    ‖X‖ ≤
      2 * ‖H.B01‖ /
        (d + Real.sqrt (d ^ 2 - 4 * ‖H.B01‖ ^ 2)) := by
  apply le_riccati_small_root_of_quadratic
    (b := ‖H.B01‖) (d := d) (t := ‖X‖)
  · exact norm_nonneg H.B01
  · exact hd
  · exact hsmall
  · exact hXc
  · exact norm_riccati_solution_quadratic_le_of_spectrum_gap
      H hd hlr hA0spec hA1spec hX

/-- A finite-error sharp Riccati estimate evaluated on a normalized
near-singular pair.  The error is exactly the defect in the adjoint singular
relation `X* y = t x`.

In the exact singular-pair case (`eta = 0`, `s = t`) the conclusion is

`d * t <= ||B01|| * (1 - t^2)`.
-/
theorem riccati_near_singular_pair_bound
    (H : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {d t s eta : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hs0 : 0 ≤ s) (hst : s ≤ t)
    (hA0 : ∀ z : E0, RCLike.re ⟪H.A0 z, z⟫_ℂ ≤ 0)
    (hA1 : ∀ z : E1, d * ‖z‖ ^ 2 ≤ RCLike.re ⟪H.A1 z, z⟫_ℂ)
    {X : E0 →L[ℂ] E1} (hX : SolvesRiccati H X)
    {x : E0} {y : E1}
    (hxnorm : ‖x‖ = 1) (hynorm : ‖y‖ = 1)
    (hXx : X x = (s : ℂ) • y)
    (hadj : ‖X.adjoint y - (t : ℂ) • x‖ ≤ eta) :
    d * s ≤ ‖H.B01‖ * (1 - s * t) +
      (‖H.A0‖ + s * ‖H.B01‖) * eta := by
  set e : E0 := X.adjoint y - (t : ℂ) • x with he
  have he_norm : ‖e‖ ≤ eta := by simpa [he] using hadj
  have hst1 : s * t < 1 := by
    have htt : t * t < 1 := by nlinarith
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hst ht0) htt
  have hA1lower : d * s ≤ s * RCLike.re ⟪H.A1 y, y⟫_ℂ := by
    have hy := hA1 y
    rw [hynorm, one_pow, mul_one] at hy
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hy hs0
  have hA0cross : RCLike.re ⟪H.A0 x, X.adjoint y⟫_ℂ ≤ ‖H.A0‖ * eta := by
    have hadj_expand : X.adjoint y = (t : ℂ) • x + e := by
      rw [he]
      abel
    rw [hadj_expand, inner_add_right, map_add]
    have hmain : RCLike.re ⟪H.A0 x, (t : ℂ) • x⟫_ℂ ≤ 0 := by
      rw [inner_smul_right, ← Complex.real_smul, RCLike.smul_re]
      exact mul_nonpos_of_nonneg_of_nonpos ht0 (hA0 x)
    have herr : RCLike.re ⟪H.A0 x, e⟫_ℂ ≤ ‖H.A0‖ * eta := by
      calc
        RCLike.re ⟪H.A0 x, e⟫_ℂ ≤ ‖⟪H.A0 x, e⟫_ℂ‖ := RCLike.re_le_norm _
        _ ≤ ‖H.A0 x‖ * ‖e‖ := norm_inner_le_norm _ _
        _ ≤ (‖H.A0‖ * ‖x‖) * ‖e‖ := by
          exact mul_le_mul_of_nonneg_right (H.A0.le_opNorm x) (norm_nonneg e)
        _ ≤ (‖H.A0‖ * ‖x‖) * eta := by
          exact mul_le_mul_of_nonneg_left he_norm
            (mul_nonneg (norm_nonneg H.A0) (norm_nonneg x))
        _ = ‖H.A0‖ * eta := by rw [hxnorm, mul_one]
    linarith
  have hleft_lower :
      d * s - ‖H.A0‖ * eta ≤
        RCLike.re ⟪H.A1 (X x) - X (H.A0 x), y⟫_ℂ := by
    have hA1exact :
        RCLike.re ⟪H.A1 (X x), y⟫_ℂ =
          s * RCLike.re ⟪H.A1 y, y⟫_ℂ := by
      rw [hXx, map_smul, inner_smul_left, Complex.conj_ofReal,
        ← Complex.real_smul, RCLike.smul_re]
    have hA0exact :
        RCLike.re ⟪X (H.A0 x), y⟫_ℂ =
          RCLike.re ⟪H.A0 x, X.adjoint y⟫_ℂ := by
      rw [ContinuousLinearMap.adjoint_inner_right]
    rw [inner_sub_left, map_sub, hA1exact, hA0exact]
    linarith
  have hpoint := (solvesRiccati_iff_pointwise H X).1 hX x
  have heq : H.A1 (X x) - X (H.A0 x) =
      X (H.B01 (X x)) - H.B10 x := by
    rw [map_add] at hpoint
    calc
      H.A1 (X x) - X (H.A0 x) =
          (H.B10 x + H.A1 (X x)) - (H.B10 x + X (H.A0 x)) := by abel
      _ = (X (H.A0 x) + X (H.B01 (X x))) -
          (H.B10 x + X (H.A0 x)) := by rw [hpoint]
      _ = X (H.B01 (X x)) - H.B10 x := by abel
  have hB10real :
      RCLike.re ⟪H.B10 x, y⟫_ℂ =
        RCLike.re ⟪H.B01 y, x⟫_ℂ := by
    rw [← RCLike.conj_re ⟪H.B10 x, y⟫_ℂ, inner_conj_symm,
      ← H.offDiagonalAdjoint x y]
  have hBexact :
      RCLike.re ⟪X (H.B01 (X x)) - H.B10 x, y⟫_ℂ =
        (s * t - 1) * RCLike.re ⟪H.B01 y, x⟫_ℂ +
          s * RCLike.re ⟪H.B01 y, e⟫_ℂ := by
    have hadj_expand : X.adjoint y = (t : ℂ) • x + e := by
      rw [he]
      abel
    have hXterm :
        RCLike.re ⟪X (H.B01 (X x)), y⟫_ℂ =
          s * (t * RCLike.re ⟪H.B01 y, x⟫_ℂ +
            RCLike.re ⟪H.B01 y, e⟫_ℂ) := by
      calc
        RCLike.re ⟪X (H.B01 (X x)), y⟫_ℂ =
            RCLike.re ⟪H.B01 (X x), X.adjoint y⟫_ℂ := by
              rw [ContinuousLinearMap.adjoint_inner_right]
        _ = s * RCLike.re ⟪H.B01 y, X.adjoint y⟫_ℂ := by
              rw [hXx, map_smul, inner_smul_left, Complex.conj_ofReal,
                ← Complex.real_smul, RCLike.smul_re]
        _ = s * (t * RCLike.re ⟪H.B01 y, x⟫_ℂ +
              RCLike.re ⟪H.B01 y, e⟫_ℂ) := by
              rw [hadj_expand, inner_add_right, map_add, inner_smul_right,
                ← Complex.real_smul, RCLike.smul_re]
    rw [inner_sub_left, map_sub, hXterm, hB10real]
    ring
  have hq : |RCLike.re ⟪H.B01 y, x⟫_ℂ| ≤ ‖H.B01‖ := by
    calc
      |RCLike.re ⟪H.B01 y, x⟫_ℂ| ≤ ‖⟪H.B01 y, x⟫_ℂ‖ := RCLike.abs_re_le_norm _
      _ ≤ ‖H.B01 y‖ * ‖x‖ := norm_inner_le_norm _ _
      _ ≤ (‖H.B01‖ * ‖y‖) * ‖x‖ := by
        gcongr
        exact H.B01.le_opNorm y
      _ = ‖H.B01‖ := by rw [hynorm, hxnorm, mul_one, mul_one]
  have herrB : |RCLike.re ⟪H.B01 y, e⟫_ℂ| ≤ ‖H.B01‖ * eta := by
    calc
      |RCLike.re ⟪H.B01 y, e⟫_ℂ| ≤ ‖⟪H.B01 y, e⟫_ℂ‖ := RCLike.abs_re_le_norm _
      _ ≤ ‖H.B01 y‖ * ‖e‖ := norm_inner_le_norm _ _
      _ ≤ (‖H.B01‖ * ‖y‖) * ‖e‖ := by
        exact mul_le_mul_of_nonneg_right (H.B01.le_opNorm y) (norm_nonneg e)
      _ ≤ (‖H.B01‖ * ‖y‖) * eta := by
        exact mul_le_mul_of_nonneg_left he_norm
          (mul_nonneg (norm_nonneg H.B01) (norm_nonneg y))
      _ = ‖H.B01‖ * eta := by rw [hynorm, mul_one]
  have hright_upper :
      RCLike.re ⟪X (H.B01 (X x)) - H.B10 x, y⟫_ℂ ≤
        ‖H.B01‖ * (1 - s * t) + s * ‖H.B01‖ * eta := by
    rw [hBexact]
    have hcoef : s * t - 1 ≤ 0 := by linarith
    have hfirst :
        (s * t - 1) * RCLike.re ⟪H.B01 y, x⟫_ℂ ≤
          ‖H.B01‖ * (1 - s * t) := by
      calc
        (s * t - 1) * RCLike.re ⟪H.B01 y, x⟫_ℂ
            ≤ |(s * t - 1) * RCLike.re ⟪H.B01 y, x⟫_ℂ| :=
              le_abs_self _
        _ = |s * t - 1| * |RCLike.re ⟪H.B01 y, x⟫_ℂ| := by
              rw [abs_mul]
        _ ≤ (1 - s * t) * ‖H.B01‖ := by
              rw [abs_of_nonpos hcoef, neg_sub]
              exact mul_le_mul_of_nonneg_left hq (by linarith)
        _ = ‖H.B01‖ * (1 - s * t) := mul_comm _ _
    have hsecond :
        s * RCLike.re ⟪H.B01 y, e⟫_ℂ ≤ s * ‖H.B01‖ * eta := by
      calc
        s * RCLike.re ⟪H.B01 y, e⟫_ℂ
            ≤ s * |RCLike.re ⟪H.B01 y, e⟫_ℂ| :=
              mul_le_mul_of_nonneg_left (le_abs_self _) hs0
        _ ≤ s * (‖H.B01‖ * eta) :=
              mul_le_mul_of_nonneg_left herrB hs0
        _ = s * ‖H.B01‖ * eta := by ring
    linarith
  rw [heq] at hleft_lower
  have hmain : d * s - ‖H.A0‖ * eta ≤
      ‖H.B01‖ * (1 - s * t) + s * ‖H.B01‖ * eta :=
    hleft_lower.trans hright_upper
  nlinarith

end DavisKahanExt
end TauCeti
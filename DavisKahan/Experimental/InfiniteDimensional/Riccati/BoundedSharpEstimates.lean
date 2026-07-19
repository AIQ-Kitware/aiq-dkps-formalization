/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.Riccati.BoundedEstimates

/-!
# Sharp contractive-branch majorant for bounded Riccati solutions

This leaf module solves the scalar quadratic inequality produced by the
interval/exterior Sylvester estimate.  On the contractive branch, the solution
norm is bounded by the smaller root of the Riccati majorant polynomial.

The result is stated in an algebraic square-root form.  This keeps the operator
argument independent of trigonometric normalization and exposes the exact
scalar endpoint needed by later continuation and branch-selection proofs.
-/

namespace ForMathlib
namespace DavisKahanExt

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

end DavisKahanExt
end ForMathlib

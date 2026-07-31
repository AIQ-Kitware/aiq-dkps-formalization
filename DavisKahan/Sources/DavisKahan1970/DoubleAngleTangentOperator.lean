/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Sources.DavisKahan1970.Ideals.SpectralSelection
import DavisKahan.DoubleAngle.TanTwoThetaKyFan
import ForTauCeti.Analysis.CStarAlgebra.SelfAdjointGapInverse
import ForTauCeti.Analysis.Matrix.EntrywiseOpNorm

/-!
# Canonical double-angle tangent operator

For a strict contraction `X`, the graph-coordinate tangent operator is

`2 X (I - X* X)^{-1}`.

The scalar singular-value transform is proved through two local statements:

* a finite-rank upper approximant obtained from a Gram spectral cutoff; and
* a min--max lower bound obtained from approximate leading singular families.

Both are stated and attacked here.  No nonexistent polar-factor or functional-
calculus approximation-number theorem is referenced.
-/

namespace TauCeti
namespace DavisKahan

open ApproximationNumber
open scoped InnerProductSpace BigOperators
open Set
open DavisKahan.Experimental.ExactSinTheta

noncomputable section

universe u v

variable {E0 : Type u} [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
  [CompleteSpace E0]
variable {E1 : Type v} [NormedAddCommGroup E1] [InnerProductSpace ℂ E1]
  [CompleteSpace E1]


/-- The scalar double-angle tangent is increasing on the contractive interval. -/
theorem doubleAngleTangent_mono {s t : ℝ}
    (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : t < 1) :
    DavisKahanTheory.doubleAngleTangent s ≤
      DavisKahanTheory.doubleAngleTangent t := by
  have ht0 : 0 ≤ t := hs0.trans hst
  have hs1 : s < 1 := hst.trans_lt ht1
  have hds : 0 < 1 - s ^ 2 := by nlinarith
  have hdt : 0 < 1 - t ^ 2 := by nlinarith
  unfold DavisKahanTheory.doubleAngleTangent
  apply (div_le_div_iff₀ hds hdt).2
  nlinarith [mul_nonneg (sub_nonneg.mpr hst) (by nlinarith : 0 ≤ 1 + s * t)]

/-- Exact difference formula for the scalar double-angle tangent.

The numerator factors through `s - t`, which is what makes the function
Lipschitz on every contractive interval without any differentiation. -/
theorem doubleAngleTangent_sub {s t : ℝ} (hs1 : s ^ 2 ≠ 1) (ht1 : t ^ 2 ≠ 1) :
    DavisKahanTheory.doubleAngleTangent s -
        DavisKahanTheory.doubleAngleTangent t =
      2 * (s - t) * (1 + s * t) / ((1 - s ^ 2) * (1 - t ^ 2)) := by
  have hs : (1 : ℝ) - s ^ 2 ≠ 0 := sub_ne_zero_of_ne (Ne.symm hs1)
  have ht : (1 : ℝ) - t ^ 2 ≠ 0 := sub_ne_zero_of_ne (Ne.symm ht1)
  unfold DavisKahanTheory.doubleAngleTangent
  field_simp
  ring

/-- **The scalar double-angle tangent is Lipschitz on `[0, r]` for `r < 1`.**

This is what lets the selection argument report the *achieved* values
`sᵢ = ‖X xᵢ‖` instead of the approximation numbers `aᵢ(X)` themselves: the
resulting slack in the Ky Fan sum is bounded-norm bookkeeping, with no
appearance of the unbounded diagonal blocks. -/
theorem abs_doubleAngleTangent_sub_le {r s t : ℝ}
    (hs0 : 0 ≤ s) (ht0 : 0 ≤ t) (hsr : s ≤ r) (htr : t ≤ r) (hr1 : r < 1) :
    |DavisKahanTheory.doubleAngleTangent s -
        DavisKahanTheory.doubleAngleTangent t| ≤
      2 * (1 + r ^ 2) / (1 - r ^ 2) ^ 2 * |s - t| := by
  have hr0 : 0 ≤ r := hs0.trans hsr
  have hs1 : s < 1 := hsr.trans_lt hr1
  have ht1 : t < 1 := htr.trans_lt hr1
  have hds : 0 < 1 - s ^ 2 := by nlinarith
  have hdt : 0 < 1 - t ^ 2 := by nlinarith
  have hdr : 0 < 1 - r ^ 2 := by nlinarith
  rw [doubleAngleTangent_sub (ne_of_lt (by nlinarith : s ^ 2 < 1))
    (ne_of_lt (by nlinarith : t ^ 2 < 1))]
  rw [abs_div, abs_of_pos (by positivity : 0 < (1 - s ^ 2) * (1 - t ^ 2))]
  rw [div_le_iff₀ (by positivity)]
  have hnum : |2 * (s - t) * (1 + s * t)| = 2 * |s - t| * (1 + s * t) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_nonneg (by nlinarith : (0 : ℝ) ≤ 1 + s * t)]
  rw [hnum]
  have habs : 0 ≤ |s - t| := abs_nonneg _
  have hst : 1 + s * t ≤ 1 + r ^ 2 := by
    nlinarith [mul_le_mul hsr htr ht0 hr0]
  have hlow : (1 - r ^ 2) ^ 2 ≤ (1 - s ^ 2) * (1 - t ^ 2) := by
    have h1 : 1 - r ^ 2 ≤ 1 - s ^ 2 := by nlinarith
    have h2 : 1 - r ^ 2 ≤ 1 - t ^ 2 := by nlinarith
    calc (1 - r ^ 2) ^ 2 = (1 - r ^ 2) * (1 - r ^ 2) := sq _
      _ ≤ (1 - s ^ 2) * (1 - t ^ 2) :=
        mul_le_mul h1 h2 hdr.le (by linarith)
  have hne : ((1 : ℝ) - r ^ 2) ^ 2 ≠ 0 := by positivity
  calc
    2 * |s - t| * (1 + s * t) ≤ 2 * |s - t| * (1 + r ^ 2) :=
      mul_le_mul_of_nonneg_left hst (by positivity)
    _ = 2 * (1 + r ^ 2) / (1 - r ^ 2) ^ 2 * |s - t| * (1 - r ^ 2) ^ 2 := by
        field_simp
    _ ≤ 2 * (1 + r ^ 2) / (1 - r ^ 2) ^ 2 * |s - t| *
        ((1 - s ^ 2) * (1 - t ^ 2)) :=
      mul_le_mul_of_nonneg_left hlow (by positivity)

/-- Positive denominator in graph coordinates. -/
def doubleAngleDenominator (X : E0 →L[ℂ] E1) : E0 →L[ℂ] E0 :=
  ContinuousLinearMap.id ℂ E0 - X.adjoint ∘L X

/-- A strict contraction has invertible double-angle denominator. -/
theorem isUnit_doubleAngleDenominator (X : E0 →L[ℂ] E1)
    (hX : ‖X‖ < 1) : IsUnit (doubleAngleDenominator X) := by
  have hcomp : ‖X.adjoint ∘L X‖ < 1 := by
    calc
      ‖X.adjoint ∘L X‖ ≤ ‖X.adjoint‖ * ‖X‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ = ‖X‖ ^ 2 := by
        rw [ContinuousLinearMap.adjoint.norm_map]
        ring
      _ < 1 := by nlinarith [norm_nonneg X]
  change IsUnit (1 - X.adjoint ∘L X)
  exact isUnit_one_sub_of_norm_lt_one hcomp

/-- Quantitative Neumann-series bound for the graph denominator. -/
theorem norm_ringInverse_doubleAngleDenominator_le
    (X : E0 →L[ℂ] E1) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hXr : ‖X‖ ≤ r) :
    ‖Ring.inverse (doubleAngleDenominator X)‖ ≤ (1 - r ^ 2)⁻¹ := by
  let T : E0 →L[ℂ] E0 := X.adjoint ∘L X
  have hTnorm : ‖T‖ ≤ r ^ 2 := by
    calc
      ‖T‖ ≤ ‖X.adjoint‖ * ‖X‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ = ‖X‖ ^ 2 := by
        rw [ContinuousLinearMap.adjoint.norm_map]
        ring
      _ ≤ r ^ 2 := by nlinarith [norm_nonneg X]
  have hTlt : ‖T‖ < 1 := hTnorm.trans_lt (by nlinarith)
  have hdenT : 0 < 1 - ‖T‖ := by linarith
  have hdenr : 0 < 1 - r ^ 2 := by nlinarith
  have hgeomRaw := tsum_geometric_le_of_norm_lt_one T hTlt
  rw [ContinuousLinearMap.one_def] at hgeomRaw
  have hgeom : ‖∑' n : ℕ, T ^ n‖ ≤ (1 - ‖T‖)⁻¹ := by
    have hone : ‖ContinuousLinearMap.id ℂ E0‖ ≤ 1 :=
      ContinuousLinearMap.norm_id_le
    exact hgeomRaw.trans (by linarith)
  change ‖Ring.inverse (1 - T)‖ ≤ (1 - r ^ 2)⁻¹
  rw [NormedRing.inverse_one_sub T hTlt]
  calc
    ‖∑' n : ℕ, T ^ n‖ ≤ (1 - ‖T‖)⁻¹ := hgeom
    _ ≤ (1 - r ^ 2)⁻¹ := by
      exact inv_anti₀ hdenr (by linarith)

/-- Canonical tangent of twice the graph angle. -/
noncomputable def doubleAngleTangentOperator
    (X : E0 →L[ℂ] E1) (_hX : ‖X‖ < 1) : E0 →L[ℂ] E1 :=
  (2 : ℂ) • (X ∘L Ring.inverse (doubleAngleDenominator X))

/-- The denominator acts diagonally on an exact right singular vector. -/
theorem doubleAngleDenominator_apply_of_singularPair
    (X : E0 →L[ℂ] E1) {x : E0} {y : E1} {s : ℝ}
    (hXx : X x = (s : ℂ) • y)
    (hXay : X.adjoint y = (s : ℂ) • x) :
    doubleAngleDenominator X x = ((1 - s ^ 2 : ℝ) : ℂ) • x := by
  unfold doubleAngleDenominator
  change x - X.adjoint (X x) = ((1 - s ^ 2 : ℝ) : ℂ) • x
  rw [hXx, map_smul, hXay]
  simp only [smul_smul]
  apply sub_eq_iff_eq_add.mpr
  module

/-- The inverse denominator acts by the reciprocal scalar on an exact right
singular vector. -/
theorem inverse_doubleAngleDenominator_apply_of_singularPair
    (X : E0 →L[ℂ] E1) (hcontractive : ‖X‖ < 1)
    {x : E0} {y : E1} {s : ℝ}
    (hs0 : 0 ≤ s) (hsX : s ≤ ‖X‖)
    (hXx : X x = (s : ℂ) • y)
    (hXay : X.adjoint y = (s : ℂ) • x) :
    Ring.inverse (doubleAngleDenominator X) x =
      (((1 - s ^ 2)⁻¹ : ℝ) : ℂ) • x := by
  have hs1 : s < 1 := hsX.trans_lt hcontractive
  have hden : 1 - s ^ 2 ≠ 0 := by nlinarith
  have hunit := isUnit_doubleAngleDenominator X hcontractive
  have hinj : Function.Injective (doubleAngleDenominator X) :=
    (ContinuousLinearMap.isUnit_iff_bijective.mp hunit).1
  apply hinj
  have hleft : doubleAngleDenominator X
      (Ring.inverse (doubleAngleDenominator X) x) = x := by
    have hmul := Ring.mul_inverse_cancel (doubleAngleDenominator X) hunit
    have happly := DFunLike.congr_fun hmul x
    simpa only [mul_apply_eq_comp, ContinuousLinearMap.comp_apply,
      one_apply_eq_self] using happly
  rw [hleft, map_smul,
    doubleAngleDenominator_apply_of_singularPair X hXx hXay]
  simp only [smul_smul]
  have hscalar :
      (((1 - s ^ 2)⁻¹ : ℝ) : ℂ) * (((1 - s ^ 2 : ℝ) : ℂ)) = 1 := by
    rw [← Complex.ofReal_mul]
    simp [hden]
  rw [hscalar, one_smul]

/-- Exact singular-pair action of the canonical tangent operator. -/
theorem doubleAngleTangentOperator_apply_of_singularPair
    (X : E0 →L[ℂ] E1) (hcontractive : ‖X‖ < 1)
    {x : E0} {y : E1} {s : ℝ}
    (hs0 : 0 ≤ s) (hsX : s ≤ ‖X‖)
    (hXx : X x = (s : ℂ) • y)
    (hXay : X.adjoint y = (s : ℂ) • x) :
    doubleAngleTangentOperator X hcontractive x =
      (DavisKahanTheory.doubleAngleTangent s : ℂ) • y := by
  unfold doubleAngleTangentOperator
  rw [smul_apply, ContinuousLinearMap.comp_apply,
    inverse_doubleAngleDenominator_apply_of_singularPair
      X hcontractive hs0 hsX hXx hXay,
    map_smul, hXx]
  unfold DavisKahanTheory.doubleAngleTangent
  simp only [smul_smul]
  congr 1
  norm_cast
  ring

/-- Stability of the canonical tangent action under an approximate singular
pair.  This is the resolvent calculation needed by the lower min--max bound. -/
theorem norm_doubleAngleTangentOperator_apply_sub_le
    (X : E0 →L[ℂ] E1) {r s ε : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hXr : ‖X‖ ≤ r)
    (hs0 : 0 ≤ s) (hsr : s ≤ r) (_hε0 : 0 ≤ ε)
    {x : E0} {y : E1}
    (hXx : ‖X x - (s : ℂ) • y‖ ≤ ε)
    (hXay : ‖X.adjoint y - (s : ℂ) • x‖ ≤ ε) :
    ‖doubleAngleTangentOperator X (hXr.trans_lt hr1) x -
        (DavisKahanTheory.doubleAngleTangent s : ℂ) • y‖ ≤
      (2 / (1 - r ^ 2) + 4 * r ^ 2 / (1 - r ^ 2) ^ 2) * ε := by
  let D := doubleAngleDenominator X
  let Q := Ring.inverse D
  have hdenr : 0 < 1 - r ^ 2 := by nlinarith
  have hQnorm : ‖Q‖ ≤ (1 - r ^ 2)⁻¹ :=
    norm_ringInverse_doubleAngleDenominator_le X hr0 hr1 hXr
  set e0 : E1 := X x - (s : ℂ) • y with he0
  set e1 : E0 := X.adjoint y - (s : ℂ) • x with he1
  have he0norm : ‖e0‖ ≤ ε := by simpa [he0] using hXx
  have he1norm : ‖e1‖ ≤ ε := by simpa [he1] using hXay
  have hgramResidual :
      ‖D x - ((1 - s ^ 2 : ℝ) : ℂ) • x‖ ≤ 2 * r * ε := by
    have hidentity :
        D x - ((1 - s ^ 2 : ℝ) : ℂ) • x =
          -(X.adjoint e0 + (s : ℂ) • e1) := by
      unfold D doubleAngleDenominator
      rw [he0, he1]
      simp only [sub_apply, ContinuousLinearMap.id_apply,
        ContinuousLinearMap.comp_apply, map_sub, map_smul]
      have hscalar :
          (((1 - s ^ 2 : ℝ) : ℂ)) = 1 - (s : ℂ) * (s : ℂ) := by
        norm_num [pow_two]
      rw [hscalar]
      module
    rw [hidentity, norm_neg]
    calc
      ‖X.adjoint e0 + (s : ℂ) • e1‖ ≤
          ‖X.adjoint e0‖ + ‖(s : ℂ) • e1‖ := norm_add_le _ _
      _ ≤ ‖X.adjoint‖ * ‖e0‖ + |s| * ‖e1‖ := by
          gcongr
          · exact X.adjoint.le_opNorm e0
          · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ r * ε + r * ε := by
          rw [ContinuousLinearMap.adjoint.norm_map, abs_of_nonneg hs0]
          gcongr
      _ = 2 * r * ε := by ring
  have hunit := isUnit_doubleAngleDenominator X (hXr.trans_lt hr1)
  have hQD : Q ∘L D = ContinuousLinearMap.id ℂ E0 := by
    exact Ring.inverse_mul_cancel D hunit
  have hQResidual :
      ‖Q x - (((1 - s ^ 2)⁻¹ : ℝ) : ℂ) • x‖ ≤
        (2 * r / (1 - r ^ 2) ^ 2) * ε := by
    have hdens : 0 < 1 - s ^ 2 := by nlinarith
    have hidentity :
        Q x - (((1 - s ^ 2)⁻¹ : ℝ) : ℂ) • x =
          -((((1 - s ^ 2)⁻¹ : ℝ) : ℂ) •
            Q (D x - ((1 - s ^ 2 : ℝ) : ℂ) • x)) := by
      have happly := DFunLike.congr_fun hQD x
      change Q (D x) = x at happly
      rw [map_sub, map_smul, happly]
      have hscalar :
          (((1 - s ^ 2)⁻¹ : ℝ) : ℂ) * (((1 - s ^ 2 : ℝ) : ℂ)) = 1 := by
        rw [← Complex.ofReal_mul]
        simp [ne_of_gt hdens]
      rw [smul_sub, smul_smul, hscalar, one_smul]
      module
    rw [hidentity, norm_neg, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_inv, abs_of_pos hdens]
    calc
      (1 - s ^ 2)⁻¹ * ‖Q (D x - ((1 - s ^ 2 : ℝ) : ℂ) • x)‖
          ≤ (1 - s ^ 2)⁻¹ *
              (‖Q‖ * ‖D x - ((1 - s ^ 2 : ℝ) : ℂ) • x‖) := by
            gcongr
            exact Q.le_opNorm _
      _ ≤ (1 - r ^ 2)⁻¹ * ((1 - r ^ 2)⁻¹ * (2 * r * ε)) := by
            have hinv : (1 - s ^ 2)⁻¹ ≤ (1 - r ^ 2)⁻¹ :=
              inv_anti₀ hdenr (by nlinarith)
            gcongr
      _ = (2 * r / (1 - r ^ 2) ^ 2) * ε := by field_simp
  unfold doubleAngleTangentOperator DavisKahanTheory.doubleAngleTangent
  have hdens : 0 < 1 - s ^ 2 := by nlinarith
  have hsplit :
      (2 : ℂ) • X (Q x) -
          ((2 * s / (1 - s ^ 2) : ℝ) : ℂ) • y =
        (2 : ℂ) • X
          (Q x - (((1 - s ^ 2)⁻¹ : ℝ) : ℂ) • x) +
        (((2 * (1 - s ^ 2)⁻¹ : ℝ) : ℂ)) •
          (X x - (s : ℂ) • y) := by
    have hscalar :
        ((2 * s / (1 - s ^ 2) : ℝ) : ℂ) =
          (2 : ℂ) * (((1 - s ^ 2)⁻¹ : ℝ) : ℂ) * (s : ℂ) := by
      norm_cast
      simp only [div_eq_mul_inv]
      ring
    have htwoInv :
        ((2 * (1 - s ^ 2)⁻¹ : ℝ) : ℂ) =
          (2 : ℂ) * (((1 - s ^ 2)⁻¹ : ℝ) : ℂ) := by
      norm_cast
    simp only [map_sub, map_smul]
    rw [hscalar, htwoInv]
    module
  rw [smul_apply, ContinuousLinearMap.comp_apply, hsplit]
  calc
    ‖(2 : ℂ) • X
          (Q x - (((1 - s ^ 2)⁻¹ : ℝ) : ℂ) • x) +
        (((2 * (1 - s ^ 2)⁻¹ : ℝ) : ℂ)) •
          (X x - (s : ℂ) • y)‖
        ≤ ‖(2 : ℂ) • X
            (Q x - (((1 - s ^ 2)⁻¹ : ℝ) : ℂ) • x)‖ +
          ‖(((2 * (1 - s ^ 2)⁻¹ : ℝ) : ℂ)) •
            (X x - (s : ℂ) • y)‖ := norm_add_le _ _
    _ ≤ 2 * r * ((2 * r / (1 - r ^ 2) ^ 2) * ε) +
          (2 / (1 - r ^ 2)) * ε := by
        have hnorm2 : ‖(2 : ℂ)‖ = 2 := by norm_num
        have hnormInv :
            ‖(((2 * (1 - s ^ 2)⁻¹ : ℝ) : ℂ))‖ =
              2 * (1 - s ^ 2)⁻¹ := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
          positivity
        rw [norm_smul, norm_smul, hnorm2, hnormInv]
        have hinv : (1 - s ^ 2)⁻¹ ≤ (1 - r ^ 2)⁻¹ :=
          inv_anti₀ hdenr (by nlinarith)
        have hcoef :
            2 * (1 - s ^ 2)⁻¹ ≤ 2 / (1 - r ^ 2) := by
          rw [div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_left hinv (by norm_num)
        have hXQ :
            ‖X (Q x - (((1 - s ^ 2)⁻¹ : ℝ) : ℂ) • x)‖ ≤
              r * ((2 * r / (1 - r ^ 2) ^ 2) * ε) := by
          calc
            ‖X (Q x - (((1 - s ^ 2)⁻¹ : ℝ) : ℂ) • x)‖ ≤
                ‖X‖ * ‖Q x - (((1 - s ^ 2)⁻¹ : ℝ) : ℂ) • x‖ :=
              X.le_opNorm _
            _ ≤ r * ((2 * r / (1 - r ^ 2) ^ 2) * ε) :=
              mul_le_mul hXr hQResidual (norm_nonneg _) hr0
        apply add_le_add
        · simpa only [mul_assoc] using
            mul_le_mul_of_nonneg_left hXQ (by norm_num : (0 : ℝ) ≤ 2)
        · exact mul_le_mul hcoef hXx (norm_nonneg _)
            (by positivity : 0 ≤ 2 / (1 - r ^ 2))
    _ = (2 / (1 - r ^ 2) + 4 * r ^ 2 / (1 - r ^ 2) ^ 2) * ε := by ring

/-- Spectral-cutoff upper approximant for the transformed operator.

For `u > a_n(X)`, the Gram projection of `(u^2,∞)` has rank at most `n`;
otherwise the existing min--max lower theorem would force `a_n(X) > u`.
Composing the tangent with that projection gives the required finite-rank
approximant, and the complementary spectral energy bound gives norm at most
`doubleAngleTangent u`.
-/
theorem exists_rank_le_norm_doubleAngleTangent_sub_lt
    (X : E0 →L[ℂ] E1) (hcontractive : ‖X‖ < 1) (n : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : E0 →L[ℂ] E1,
      R.rank ≤ (n : Cardinal) ∧
      ‖doubleAngleTangentOperator X hcontractive - R‖ <
        DavisKahanTheory.doubleAngleTangent (X.approximationNumber n) + ε := by
  classical
  let a := X.approximationNumber n
  have ha0 : 0 ≤ a := X.approximationNumber_nonneg n
  have ha1 : a < 1 := (X.approximationNumber_le_norm n).trans_lt hcontractive
  obtain ⟨v, hav, hv1, hfv⟩ : ∃ v : ℝ,
      a < v ∧ v < 1 ∧
      DavisKahanTheory.doubleAngleTangent v <
        DavisKahanTheory.doubleAngleTangent a + ε := by
    -- The scalar transform is rational and continuous on `(-1,1)`.
    have hdena : 0 < 1 - a ^ 2 := by nlinarith
    let step : ℝ := min ((1 - a) / 2) (ε * (1 - a ^ 2) ^ 2 / 16)
    have hstep0 : 0 < step := by
      dsimp [step]
      exact lt_min (by nlinarith)
        (div_pos (mul_pos hε (sq_pos_of_pos hdena)) (by norm_num))
    have hstepHalf : step ≤ (1 - a) / 2 := by
      exact min_le_left _ _
    have hstepEps : step ≤ ε * (1 - a ^ 2) ^ 2 / 16 := by
      exact min_le_right _ _
    refine ⟨a + step, ?_, ?_, ?_⟩
    · exact lt_add_of_pos_right a hstep0
    · nlinarith
    · unfold DavisKahanTheory.doubleAngleTangent
      have hdenu : 0 < 1 - (a + step) ^ 2 := by
        nlinarith
      have hdenHalf : (1 - a ^ 2) / 2 ≤ 1 - (a + step) ^ 2 := by
        nlinarith
      have hau : 1 + a * (a + step) ≤ 2 := by
        nlinarith
      have hgap :
          2 * step * (1 + a * (a + step)) <
            ε * (1 - a ^ 2) * (1 - (a + step) ^ 2) := by
        have hleft :
            2 * step * (1 + a * (a + step)) ≤ 4 * step := by
          nlinarith
        have hmid : 4 * step ≤ ε * (1 - a ^ 2) ^ 2 / 4 := by
          nlinarith
        have hright :
            ε * (1 - a ^ 2) ^ 2 / 4 <
              ε * (1 - a ^ 2) * (1 - (a + step) ^ 2) := by
          nlinarith
        exact hleft.trans_lt (hmid.trans_lt hright)
      have hdiff :
          (2 * a / (1 - a ^ 2) + ε) * (1 - (a + step) ^ 2) -
              2 * (a + step) =
            (ε * (1 - a ^ 2) * (1 - (a + step) ^ 2) -
                2 * step * (1 + a * (a + step))) /
              (1 - a ^ 2) := by
        field_simp [ne_of_gt hdena]
        ring
      apply (div_lt_iff₀ hdenu).2
      rw [← sub_pos]
      rw [hdiff]
      exact div_pos (sub_pos.mpr hgap) hdena
  let u : ℝ := (a + v) / 2
  have hau : a < u := by dsimp only [u]; linarith
  have huv : u < v := by dsimp only [u]; linarith
  have hu0 : 0 ≤ u := ha0.trans hau.le
  have hv0 : 0 ≤ v := hu0.trans huv.le
  have hu1 : u < 1 := huv.trans hv1
  let C : E0 →L[ℂ] E0 := gramOperator X
  let PVM : ProjValMeasure E0 := gramSpectralPVM X
  let P : E0 →L[ℂ] E0 := PVM.proj (Set.Ioi (u ^ 2)) measurableSet_Ioi
  let Q : E0 →L[ℂ] E0 := PVM.proj (Set.Iic (u ^ 2)) measurableSet_Iic
  let T := doubleAngleTangentOperator X hcontractive
  let R : E0 →L[ℂ] E1 := T ∘L P
  have hPrank : P.rank ≤ (n : Cardinal) := by
    simpa only [P, PVM] using
      rank_gramProjection_Ioi_le_natCast_of_approximationNumber_lt
        X n hu0 hau
  have hRrank : R.rank ≤ (n : Cardinal) :=
    ContinuousLinearMap.rank_comp_le_natCast_right P T hPrank
  have hQeq : Q = ContinuousLinearMap.id ℂ E0 - P := by
    dsimp only [Q, P, PVM]
    simpa only [Set.compl_Ioi] using
      (gramSpectralPVM X).proj_compl (Set.Ioi (u ^ 2)) measurableSet_Ioi
  have herr : T - R = T ∘L Q := by
    ext x
    change T x - T (P x) = T (Q x)
    rw [hQeq, sub_apply, ContinuousLinearMap.id_apply, map_sub]
  have htail : ‖T ∘L Q‖ ≤ DavisKahanTheory.doubleAngleTangent v := by
    have hdenv : 0 < 1 - v ^ 2 := by nlinarith
    have htanv0 : 0 ≤ DavisKahanTheory.doubleAngleTangent v := by
      unfold DavisKahanTheory.doubleAngleTangent
      positivity
    refine ContinuousLinearMap.opNorm_le_bound _ htanv0 fun x => ?_
    let q : E0 := Q x
    let D : E0 →L[ℂ] E0 := doubleAngleDenominator X
    let Dinv : E0 →L[ℂ] E0 := Ring.inverse D
    let w : E0 := Dinv q
    have hQidem : Q q = q := by
      have hidem := PVM.proj_idem (Set.Iic (u ^ 2)) measurableSet_Iic
      have happly := congrArg (fun S : E0 →L[ℂ] E0 => S x) hidem
      simpa only [q, Q, mul_apply_eq_comp,
        ContinuousLinearMap.comp_apply] using happly
    have hCQ (y : E0) : C (Q y) = Q (C y) := by
      have hyDom : y ∈ (gramLinearPMap X).domain := by
        rw [gramLinearPMap_domain]
        exact Submodule.mem_top
      have hcomm := LinearPMap.specProjection_apply_domain
        (gramLinearPMap_isSelfAdjoint X) (Set.Iic (u ^ 2)) measurableSet_Iic
        (⟨y, hyDom⟩ : (gramLinearPMap X).domain)
      change gramOperator X (Q y) = Q (gramOperator X y) at hcomm
      simpa only [C] using hcomm
    have hDQ (y : E0) : D (Q y) = Q (D y) := by
      have hCQ' :
          (ContinuousLinearMap.adjoint X ∘SL X) (Q y) =
            Q ((ContinuousLinearMap.adjoint X ∘SL X) y) := by
        simpa only [C, gramOperator] using hCQ y
      dsimp only [D, doubleAngleDenominator]
      rw [sub_apply, ContinuousLinearMap.id_apply, sub_apply,
        ContinuousLinearMap.id_apply, map_sub, hCQ']
    have hunit : IsUnit D := by
      dsimp only [D]
      exact isUnit_doubleAngleDenominator X hcontractive
    have hinj : Function.Injective D :=
      (ContinuousLinearMap.isUnit_iff_bijective.mp hunit).1
    have hDw : D w = q := by
      have hmul := Ring.mul_inverse_cancel D hunit
      have happly := DFunLike.congr_fun hmul q
      simpa only [w, Dinv, mul_apply_eq_comp,
        ContinuousLinearMap.comp_apply, one_apply_eq_self] using happly
    have hQw : Q w = w := by
      apply hinj
      rw [hDQ, hDw, hQidem]
    have huvSq : u ^ 2 < v ^ 2 := by nlinarith
    have hhighZero :
        (gramSpectralPVM X).proj (Set.Ici (v ^ 2)) measurableSet_Ici w = 0 := by
      rw [← hQw]
      have hinter : Set.Ici (v ^ 2) ∩ Set.Iic (u ^ 2) = ∅ := by
        ext t
        simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Iic,
          Set.mem_empty_iff_false, iff_false]
        exact fun ht => (not_le_of_gt huvSq) (ht.1.trans ht.2)
      change (gramSpectralPVM X).proj (Set.Ici (v ^ 2)) measurableSet_Ici
        ((gramSpectralPVM X).proj (Set.Iic (u ^ 2)) measurableSet_Iic w) = 0
      rw [← mul_apply_eq_comp,
        (gramSpectralPVM X).proj_inter,
        (gramSpectralPVM X).proj_congr hinter
          (measurableSet_Ici.inter measurableSet_Iic) MeasurableSet.empty,
        (gramSpectralPVM X).proj_empty, zero_apply]
    have hwDom : w ∈ (gramLinearPMap X).domain := by
      rw [gramLinearPMap_domain]
      exact Submodule.mem_top
    have hhighZero' :
        LinearPMap.specProjection (gramLinearPMap_isSelfAdjoint X)
            (Set.Ici (v ^ 2)) measurableSet_Ici w = 0 := by
      change (gramSpectralPVM X).proj (Set.Ici (v ^ 2)) measurableSet_Ici w = 0
      exact hhighZero
    have henergy := LinearPMap.re_inner_le_of_specProjection_Ici_apply_eq_zero
      (gramLinearPMap_isSelfAdjoint X)
      (⟨w, hwDom⟩ : (gramLinearPMap X).domain) hhighZero'
    have hXenergy : ‖X w‖ ^ 2 ≤ v ^ 2 * ‖w‖ ^ 2 := by
      calc
        ‖X w‖ ^ 2 = (⟪gramOperator X w, w⟫_ℂ).re :=
          (re_inner_gramOperator X w).symm
        _ = (⟪gramLinearPMap X
            (⟨w, hwDom⟩ : (gramLinearPMap X).domain), w⟫_ℂ).re := by
          rw [gramLinearPMap_apply]
        _ ≤ v ^ 2 * ‖w‖ ^ 2 := henergy
    have hDcoercive :
        (1 - v ^ 2) * ‖w‖ ^ 2 ≤ (⟪D w, w⟫_ℂ).re := by
      have hwInner : (⟪w, w⟫_ℂ).re = ‖w‖ ^ 2 :=
        inner_self_eq_norm_sq (𝕜 := ℂ) w
      have hgramInner : (⟪C w, w⟫_ℂ).re = ‖X w‖ ^ 2 := by
        dsimp only [C, gramOperator]
        rw [ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.adjoint_inner_left]
        exact inner_self_eq_norm_sq (𝕜 := ℂ) (X w)
      have hgramInner' :
          (⟪(ContinuousLinearMap.adjoint X ∘SL X) w, w⟫_ℂ).re =
            ‖X w‖ ^ 2 := by
        simpa only [C, gramOperator] using hgramInner
      have hDform :
          (⟪D w, w⟫_ℂ).re = ‖w‖ ^ 2 - ‖X w‖ ^ 2 := by
        dsimp only [D, doubleAngleDenominator]
        rw [sub_apply, ContinuousLinearMap.id_apply, inner_sub_left,
          Complex.sub_re, hwInner, hgramInner']
      rw [hDform]
      nlinarith
    have hinnerUpper :
        (⟪D w, w⟫_ℂ).re ≤ ‖D w‖ * ‖w‖ := by
      calc
        (⟪D w, w⟫_ℂ).re ≤ ‖⟪D w, w⟫_ℂ‖ :=
          RCLike.re_le_norm (⟪D w, w⟫_ℂ : ℂ)
        _ ≤ ‖D w‖ * ‖w‖ := norm_inner_le_norm _ _
    have hwBound : ‖w‖ ≤ (1 - v ^ 2)⁻¹ * ‖q‖ := by
      by_cases hw : w = 0
      · have hrhs : 0 ≤ (1 - v ^ 2)⁻¹ * ‖q‖ :=
          mul_nonneg (inv_nonneg.mpr hdenv.le) (norm_nonneg q)
        simpa only [hw, norm_zero] using hrhs
      have hwnorm : 0 < ‖w‖ := norm_pos_iff.mpr hw
      have hmain : (1 - v ^ 2) * ‖w‖ ^ 2 ≤ ‖q‖ * ‖w‖ := by
        calc
          (1 - v ^ 2) * ‖w‖ ^ 2 ≤ (⟪D w, w⟫_ℂ).re := hDcoercive
          _ ≤ ‖D w‖ * ‖w‖ := hinnerUpper
          _ = ‖q‖ * ‖w‖ := by rw [hDw]
      have hcancel : (1 - v ^ 2) * ‖w‖ ≤ ‖q‖ := by
        apply le_of_mul_le_mul_right
        · simpa only [pow_two, mul_assoc] using hmain
        · exact hwnorm
      calc
        ‖w‖ ≤ ‖q‖ / (1 - v ^ 2) := by
          apply (le_div_iff₀ hdenv).2
          simpa only [mul_comm] using hcancel
        _ = (1 - v ^ 2)⁻¹ * ‖q‖ := by rw [div_eq_inv_mul]
    have hqNorm : ‖q‖ ≤ ‖x‖ := by
      dsimp only [q, Q]
      exact PVM.norm_proj_apply_le (Set.Iic (u ^ 2)) measurableSet_Iic x
    have hXw : ‖X w‖ ≤ v * ‖w‖ := by
      apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hv0 (norm_nonneg _))).mp
      simpa only [mul_pow] using hXenergy
    change ‖(2 : ℂ) • X w‖ ≤
      DavisKahanTheory.doubleAngleTangent v * ‖x‖
    rw [norm_smul]
    have hnormTwo : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [hnormTwo]
    unfold DavisKahanTheory.doubleAngleTangent
    calc
      2 * ‖X w‖ ≤ 2 * (v * ‖w‖) :=
        mul_le_mul_of_nonneg_left hXw (by norm_num)
      _ ≤ 2 * (v * ((1 - v ^ 2)⁻¹ * ‖q‖)) := by
        gcongr
      _ ≤ 2 * (v * ((1 - v ^ 2)⁻¹ * ‖x‖)) := by
        gcongr
      _ = (2 * v / (1 - v ^ 2)) * ‖x‖ := by
        rw [div_eq_mul_inv]
        ring
  refine ⟨R, hRrank, ?_⟩
  rw [herr]
  exact htail.trans_lt hfv

/-- Lower min--max bound for the transformed approximation number. -/
theorem doubleAngleTangent_approximationNumber_le
    (X : E0 →L[ℂ] E1) (hcontractive : ‖X‖ < 1) (n : ℕ) :
    DavisKahanTheory.doubleAngleTangent (X.approximationNumber n) ≤
      (doubleAngleTangentOperator X hcontractive).approximationNumber n := by
  apply le_of_forall_pos_le_add
  intro η hη
  let r : ℝ := (‖X‖ + 1) / 2
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hXr : ‖X‖ ≤ r := by dsimp [r]; linarith
  have hr1 : r < 1 := by dsimp [r]; linarith
  let C : ℝ :=
    2 / (1 - r ^ 2) + 4 * r ^ 2 / (1 - r ^ 2) ^ 2
  have hdenr : 0 < 1 - r ^ 2 := by nlinarith
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  let ε : ℝ := min (X.approximationNumber n / 2)
    (η / (4 * Real.sqrt (n + 1) * (C + 1)))
  by_cases ha : X.approximationNumber n = 0
  · rw [ha, DavisKahanTheory.doubleAngleTangent_zero]
    exact add_nonneg
      ((doubleAngleTangentOperator X hcontractive).approximationNumber_nonneg n)
      hη.le
  have ha0 : 0 < X.approximationNumber n :=
    lt_of_le_of_ne (X.approximationNumber_nonneg n) (Ne.symm ha)
  have hεpos : 0 < ε := by
    dsimp [ε]
    apply lt_min
    · linarith
    · positivity
  obtain ⟨F⟩ := TauCeti.DavisKahan.exists_approximateLeadingSingularFamily X (n + 1) hεpos
  rcases F with
    ⟨count, hcount_le, right, left, hrightOrtho, hleftOrtho,
      _hselected, happlyResidual, hadjointResidual, htailSmall⟩
  have hcount : count = n + 1 := by
    apply le_antisymm hcount_le
    by_contra hnot
    have hcountn : count ≤ n := by omega
    have htail := htailSmall n hcountn (Nat.lt_succ_self n)
    have hεhalf : ε ≤ X.approximationNumber n / 2 := min_le_left _ _
    linarith
  subst count
  have hlin : LinearIndependent ℂ right :=
    hrightOrtho.linearIndependent
  have hlower :
      DavisKahanTheory.doubleAngleTangent (X.approximationNumber n) - η ≤
        (doubleAngleTangentOperator X hcontractive).approximationNumber n := by
    apply ContinuousLinearMap.le_approximationNumber_of_linearIndependent
      (doubleAngleTangentOperator X hcontractive) n right hlin
    intro z hz hznorm
    -- Expand `z` in the orthonormal selected family.  The exact diagonal model
    -- has minimum coefficient `doubleAngleTangent (a_n X)`; the accumulated
    -- residual is bounded by `sqrt (n+1) * C * ε` by Cauchy--Schwarz.
    have hpair := fun i : Fin (n + 1) =>
      norm_doubleAngleTangentOperator_apply_sub_le
        X hr0 hr1 hXr (X.approximationNumber_nonneg (i : ℕ))
        ((X.approximationNumber_le_norm (i : ℕ)).trans hXr) hεpos.le
        (happlyResidual i) (hadjointResidual i)
    have hanti := X.approximationNumber_antitone
    have htanmono : ∀ i : Fin (n + 1),
        DavisKahanTheory.doubleAngleTangent (X.approximationNumber n) ≤
          DavisKahanTheory.doubleAngleTangent (X.approximationNumber i) := by
      intro i
      apply doubleAngleTangent_mono
      · exact X.approximationNumber_nonneg n
      · exact hanti (Nat.le_of_lt_succ i.isLt)
      · exact (X.approximationNumber_le_norm i).trans_lt hcontractive
    have hspanRange :
        Submodule.span ℂ (Set.range right) ≤
          LinearMap.range (familyIsometry hrightOrtho).toLinearMap := by
      refine Submodule.span_le.2 ?_
      intro y hy
      obtain ⟨i, rfl⟩ := hy
      refine ⟨EuclideanSpace.single i 1, ?_⟩
      exact familyIsometry_single hrightOrtho i
    obtain ⟨coeff, hzCoord⟩ := hspanRange hz
    have hzCoord' : familyIsometry hrightOrtho coeff = z := hzCoord
    have hcoeffNorm : ‖coeff‖ = 1 := by
      rw [← hznorm, ← hzCoord', (familyIsometry hrightOrtho).norm_map]
    have hcoeffL1 :
        (∑ i : Fin (n + 1), ‖coeff i‖) ≤ Real.sqrt (n + 1) := by
      have h := TauCeti.sum_norm_le_sqrt_card_mul_norm coeff
      rw [hcoeffNorm, mul_one] at h
      simpa using h
    let tau : Fin (n + 1) → ℝ := fun i =>
      DavisKahanTheory.doubleAngleTangent (X.approximationNumber i)
    let tau0 : ℝ :=
      DavisKahanTheory.doubleAngleTangent (X.approximationNumber n)
    have htau0 : 0 ≤ tau0 := by
      dsimp only [tau0]
      unfold DavisKahanTheory.doubleAngleTangent
      have hden : 0 < 1 - (X.approximationNumber n) ^ 2 := by
        nlinarith [X.approximationNumber_nonneg n,
          (X.approximationNumber_le_norm n).trans_lt hcontractive]
      exact div_nonneg
        (mul_nonneg (by norm_num) (X.approximationNumber_nonneg n)) hden.le
    have htauNonneg : ∀ i : Fin (n + 1), 0 ≤ tau i := by
      intro i
      dsimp only [tau]
      unfold DavisKahanTheory.doubleAngleTangent
      have hden : 0 < 1 - (X.approximationNumber i) ^ 2 := by
        nlinarith [X.approximationNumber_nonneg (i : ℕ),
          (X.approximationNumber_le_norm (i : ℕ)).trans_lt hcontractive]
      exact div_nonneg
        (mul_nonneg (by norm_num) (X.approximationNumber_nonneg (i : ℕ))) hden.le
    have htauLower : ∀ i : Fin (n + 1), tau0 ≤ tau i := by
      intro i
      exact htanmono i
    let diagonalCoeff : EuclideanSpace ℂ (Fin (n + 1)) :=
      WithLp.toLp 2 (fun i => (tau i : ℂ) * coeff i)
    let diagonal : E1 := familyIsometry hleftOrtho diagonalCoeff
    have hcoeffSq :
        (∑ i : Fin (n + 1), ‖coeff i‖ ^ 2) = 1 := by
      rw [← EuclideanSpace.norm_sq_eq, hcoeffNorm, one_pow]
    have hdiagonalCoeffSq :
        ‖diagonalCoeff‖ ^ 2 =
          ∑ i : Fin (n + 1), (tau i) ^ 2 * ‖coeff i‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      apply Finset.sum_congr rfl
      intro i _
      change ‖(tau i : ℂ) * coeff i‖ ^ 2 =
        tau i ^ 2 * ‖coeff i‖ ^ 2
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (htauNonneg i)]
      ring
    have hdiagonalLower : tau0 ≤ ‖diagonal‖ := by
      apply (sq_le_sq₀ htau0 (norm_nonneg diagonal)).mp
      calc
        tau0 ^ 2 = tau0 ^ 2 *
            (∑ i : Fin (n + 1), ‖coeff i‖ ^ 2) := by
              rw [hcoeffSq, mul_one]
        _ = ∑ i : Fin (n + 1), tau0 ^ 2 * ‖coeff i‖ ^ 2 := by
              rw [Finset.mul_sum]
        _ ≤ ∑ i : Fin (n + 1), (tau i) ^ 2 * ‖coeff i‖ ^ 2 := by
              apply Finset.sum_le_sum
              intro i _
              exact mul_le_mul_of_nonneg_right
                (pow_le_pow_left₀ htau0 (htauLower i) 2)
                (sq_nonneg ‖coeff i‖)
        _ = ‖diagonalCoeff‖ ^ 2 := hdiagonalCoeffSq.symm
        _ = ‖diagonal‖ ^ 2 := by
              dsimp only [diagonal]
              rw [(familyIsometry hleftOrtho).norm_map]
    have hresidualIdentity :
        doubleAngleTangentOperator X hcontractive z - diagonal =
          ∑ i : Fin (n + 1), coeff i •
            (doubleAngleTangentOperator X hcontractive (right i) -
              (tau i : ℂ) • left i) := by
      rw [← hzCoord']
      dsimp only [diagonal]
      rw [familyIsometry_apply, familyIsometry_apply, map_sum]
      simp only [map_smul]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      change
        coeff i • doubleAngleTangentOperator X hcontractive (right i) -
            ((tau i : ℂ) * coeff i) • left i =
          coeff i •
            (doubleAngleTangentOperator X hcontractive (right i) -
              (tau i : ℂ) • left i)
      module
    have hresidualBound :
        ‖doubleAngleTangentOperator X hcontractive z - diagonal‖ ≤
          Real.sqrt (n + 1) * (C * ε) := by
      rw [hresidualIdentity]
      calc
        ‖∑ i : Fin (n + 1), coeff i •
            (doubleAngleTangentOperator X hcontractive (right i) -
              (tau i : ℂ) • left i)‖
            ≤ ∑ i : Fin (n + 1),
                ‖coeff i •
                  (doubleAngleTangentOperator X hcontractive (right i) -
                    (tau i : ℂ) • left i)‖ := norm_sum_le _ _
        _ = ∑ i : Fin (n + 1), ‖coeff i‖ *
              ‖doubleAngleTangentOperator X hcontractive (right i) -
                (tau i : ℂ) • left i‖ := by
              apply Finset.sum_congr rfl
              intro i _
              rw [norm_smul]
        _ ≤ ∑ i : Fin (n + 1), ‖coeff i‖ * (C * ε) := by
              apply Finset.sum_le_sum
              intro i _
              exact mul_le_mul_of_nonneg_left (hpair i) (norm_nonneg _)
        _ = (∑ i : Fin (n + 1), ‖coeff i‖) * (C * ε) := by
              rw [Finset.sum_mul]
        _ ≤ Real.sqrt (n + 1) * (C * ε) :=
              mul_le_mul_of_nonneg_right hcoeffL1
                (mul_nonneg hC0 hεpos.le)
    have hresidualEta :
        ‖doubleAngleTangentOperator X hcontractive z - diagonal‖ ≤ η := by
      have hsqrtPos : 0 < Real.sqrt (n + 1) := Real.sqrt_pos.2 (by positivity)
      have hCplus : 0 < C + 1 := by linarith
      have hεEta : ε ≤
          η / (4 * Real.sqrt (n + 1) * (C + 1)) := by
        exact min_le_right _ _
      calc
        ‖doubleAngleTangentOperator X hcontractive z - diagonal‖
            ≤ Real.sqrt (n + 1) * (C * ε) := hresidualBound
        _ ≤ Real.sqrt (n + 1) * ((C + 1) * ε) := by
              gcongr
              linarith
        _ ≤ Real.sqrt (n + 1) *
              ((C + 1) *
                (η / (4 * Real.sqrt (n + 1) * (C + 1)))) := by
              gcongr
        _ = η / 4 := by
              field_simp [ne_of_gt hsqrtPos, ne_of_gt hCplus]
        _ ≤ η := by linarith
    have hreverse := norm_sub_norm_le diagonal
      (doubleAngleTangentOperator X hcontractive z)
    rw [norm_sub_rev] at hreverse
    dsimp only [tau0] at hdiagonalLower
    linarith
  linarith

/-- Approximation-number spectral mapping for the canonical double-angle
tangent operator. -/
theorem approximationNumber_doubleAngleTangentOperator
    (X : E0 →L[ℂ] E1) (hcontractive : ‖X‖ < 1) (n : ℕ) :
    (doubleAngleTangentOperator X hcontractive).approximationNumber n =
      DavisKahanTheory.doubleAngleTangent (X.approximationNumber n) := by
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨R, hRrank, hRnorm⟩ :=
      exists_rank_le_norm_doubleAngleTangent_sub_lt X hcontractive n hε
    exact ((doubleAngleTangentOperator X hcontractive).approximationNumber_le_norm_sub
      hRrank).trans hRnorm.le
  · exact doubleAngleTangent_approximationNumber_le X hcontractive n

/-- Ky Fan prefix of the canonical tangent is the transformed approximation-
number prefix. -/
theorem kyFanApproximationGauge_doubleAngleTangentOperator
    (X : E0 →L[ℂ] E1) (hcontractive : ‖X‖ < 1) (k : ℕ) :
    kyFanApproximationGauge k (doubleAngleTangentOperator X hcontractive) =
      ∑ n ∈ Finset.range k,
        DavisKahanTheory.doubleAngleTangent (X.approximationNumber n) := by
  unfold kyFanApproximationGauge
  apply Finset.sum_congr rfl
  intro n hn
  exact approximationNumber_doubleAngleTangentOperator X hcontractive n

end

end DavisKahan
end TauCeti

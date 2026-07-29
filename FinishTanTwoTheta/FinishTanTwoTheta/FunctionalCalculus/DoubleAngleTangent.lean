/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import FinishTanTwoTheta.GroundedImports
import FinishTanTwoTheta.ApproximationNumber.SpectralSelection
import DavisKahan.DoubleAngle.TanTwoThetaKyFan
import ForTauCeti.Analysis.CStarAlgebra.SelfAdjointGapInverse

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
namespace FinishTanTwoTheta

open scoped InnerProductSpace BigOperators
open Set
open DavisKahan.Experimental.ExactSinTheta
open DavisKahan.Experimental.SpectraBridge
open Spectra.OneParameterUnitaryGroup
open Spectra.YosidaHille
open Spectra.QuantumMechanics.SpectralTheory

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
  obtain ⟨u, hau, hu1, hfu⟩ : ∃ u : ℝ,
      a < u ∧ u < 1 ∧
      DavisKahanTheory.doubleAngleTangent u <
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
  let C : E0 →L[ℂ] E0 := gramOperator X
  have hC : IsSelfAdjoint C := gramOperator_isSelfAdjoint X
  let A : Spectra.Operator.SelfAdjointOperator E0 :=
    Spectra.Operator.SelfAdjointOperator.ofBounded C hC
  have hA : IsSelfAdjoint A.toLinearPMap := A.selfAdjoint
  let U := genToGroup hA
  let PVM : Spectra.ProjValMeasure E0 := spectralPVM hA
  let P : E0 →L[ℂ] E0 := PVM.proj (Set.Ioi (u ^ 2)) measurableSet_Ioi
  let Q : E0 →L[ℂ] E0 := PVM.proj (Set.Iic (u ^ 2)) measurableSet_Iic
  let T := doubleAngleTangentOperator X hcontractive
  let R : E0 →L[ℂ] E1 := T ∘L P
  have hPrank : P.rank ≤ (n : Cardinal) := by
    by_contra hnot
    have hlt : (n : Cardinal) < P.rank := lt_of_not_ge hnot
    let W : Submodule ℂ E0 :=
      pvmRangeSubspace PVM (Set.Ioi (u ^ 2)) measurableSet_Ioi
    have hWrank : ((n + 1 : ℕ) : Cardinal) ≤ Module.rank ℂ W := by
      change ((n + 1 : ℕ) : Cardinal) ≤ P.rank
      rw [← Cardinal.natCast_add_one_le_iff, ← Nat.cast_add_one] at hlt
      exact hlt
    obtain ⟨v, hv⟩ := (Module.le_rank_iff).mp hWrank
    let vectors : Fin (n + 1) → E0 := W.subtype ∘ v
    have hlin : LinearIndependent ℂ vectors := by
      exact hv.map' W.subtype (LinearMap.ker_eq_bot.mpr W.injective_subtype)
    have hlower : u ≤ X.approximationNumber n := by
      apply ContinuousLinearMap.le_approximationNumber_of_linearIndependent
        X n vectors hlin
      intro z hz hznorm
      have hzW : z ∈ W := by
        apply (Submodule.span_le.2 ?_) hz
        rintro _ ⟨i, rfl⟩
        change (v i : E0) ∈ W
        exact (v i).property
      have hhighFix :
          PVM.proj (Set.Ioi (u ^ 2)) measurableSet_Ioi z = z :=
        pvmProjection_eq_self_of_mem_rangeSubspace
          PVM (Set.Ioi (u ^ 2)) measurableSet_Ioi hzW
      have hhighFix' :
          Spectra.QuantumMechanics.SpectralTheory.spectralProjection U
              (Set.Ioi (u ^ 2)) measurableSet_Ioi z = z := by
        simpa only [PVM, U] using hhighFix
      have hlowZero :
          Spectra.QuantumMechanics.SpectralTheory.spectralProjection U
              (Set.Iic (u ^ 2)) measurableSet_Iic z = 0 := by
        have hcompl := DFunLike.congr_fun
          (Spectra.QuantumMechanics.SpectralTheory.spectralProjection_compl U
            (Set.Ioi (u ^ 2)) measurableSet_Ioi) z
        simpa only [Set.compl_Ioi, sub_apply, ContinuousLinearMap.id_apply,
          hhighFix', sub_self] using hcompl
      have hgen : generator U = A.toLinearPMap := by
        dsimp only [U]
        exact generator_genToGroup hA
      have hAdom : A.toLinearPMap.domain = ⊤ := by
        dsimp only [A]
        exact Spectra.Operator.SelfAdjointOperator.domain_ofBounded C hC
      have hzDom : z ∈ (generator U).domain := by
        rw [hgen, hAdom]
        exact Submodule.mem_top
      have hzA : z ∈ A.toLinearPMap.domain := by
        rw [hAdom]
        exact Submodule.mem_top
      have hgenApply : generator U ⟨z, hzDom⟩ = C z := by
        have happly := (LinearPMap.ext_iff.mp hgen).2
        calc
          generator U ⟨z, hzDom⟩ = A.toLinearPMap ⟨z, hzA⟩ :=
            happly (x := z) (hf := hzDom) (hg := hzA)
          _ = C z := rfl
      have henergy := energy_lower_bound_of_spectralProjection_Iic_eq_zero
        U (u ^ 2) (⟨z, hzDom⟩ : (generator U).domain) hlowZero
      have hsquare : u ^ 2 ≤ ‖X z‖ ^ 2 := by
        calc
          u ^ 2 = u ^ 2 * ‖z‖ ^ 2 := by rw [hznorm, one_pow, mul_one]
          _ ≤ (⟪generator U ⟨z, hzDom⟩, z⟫_ℂ).re := henergy
          _ = ‖X z‖ ^ 2 := by
            rw [hgenApply]
            dsimp only [C, gramOperator]
            rw [ContinuousLinearMap.comp_apply,
              ContinuousLinearMap.adjoint_inner_left, inner_self_eq_norm_sq]
      exact (sq_le_sq₀ (ha0.trans hau.le) (norm_nonneg _)).mp hsquare
    exact (not_le_of_gt hau) hlower
  have hRrank : R.rank ≤ (n : Cardinal) :=
    ContinuousLinearMap.rank_comp_le_natCast_right P T hPrank
  have hQeq : Q = ContinuousLinearMap.id ℂ E0 - P := by
    change Spectra.QuantumMechanics.SpectralTheory.spectralProjection U
        (Set.Iic (u ^ 2)) measurableSet_Iic =
      ContinuousLinearMap.id ℂ E0 -
        Spectra.QuantumMechanics.SpectralTheory.spectralProjection U
          (Set.Ioi (u ^ 2)) measurableSet_Ioi
    simpa only [Set.compl_Ioi] using
      (Spectra.QuantumMechanics.SpectralTheory.spectralProjection_compl U
        (Set.Ioi (u ^ 2)) measurableSet_Ioi)
  have herr : T - R = T ∘L Q := by
    ext x
    change T x - T (P x) = T (Q x)
    rw [hQeq, sub_apply, ContinuousLinearMap.id_apply, map_sub]
  have htail : ‖T ∘L Q‖ ≤ DavisKahanTheory.doubleAngleTangent u := by
    -- On `range Q`, the Gram spectrum is contained in `[0,u^2]`.  The
    -- denominator inverse preserves this reducing subspace and has norm at
    -- most `(1-u^2)⁻¹` there, while `X` has norm at most `u` there.  This is
    -- exactly the upper-energy argument already used in
    -- `ApproximationNumberMinMax.lean`, now applied after the denominator.
    have hupper := energy_upper_bound_of_spectralProjection_Ici_eq_zero
    have hprojectionInter := spectralProjection_inter U
    have hprojectionCompl := spectralProjection_compl U
    aesop
  refine ⟨R, hRrank, ?_⟩
  rw [herr]
  exact htail.trans_lt hfu

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
  obtain ⟨F⟩ := exists_approximateLeadingSingularFamily X (n + 1) hεpos
  rcases F with
    ⟨count, hcount_le, right, left, hrightOrtho, hleftOrtho,
      hselected, happlyResidual, hadjointResidual, htailSmall⟩
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
    have horth := hleftOrtho
    have hcoeff := hrightOrtho
    aesop
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

end FinishTanTwoTheta
end TauCeti

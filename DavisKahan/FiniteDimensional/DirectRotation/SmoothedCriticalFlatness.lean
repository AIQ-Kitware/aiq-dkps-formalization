/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedPhaseMinimum

/-!
# Quartic flatness at the smoothed phase transition

At critical circle tangency, the scalar phase cost grows at most quartically
in the unit-circle chord distance. Arbitrarily small nonzero phases violate
every proposed positive quadratic growth constant. This explains why the
strict-subcritical quadratic stability certificate cannot extend to the cutoff.

These scalar estimates support the critical-flatness proposition in the
Davis--Kahan journal paper. An exact factorization also gives the leading
fourth-order coefficient. The unrestricted quartic lower bound is proved
separately in `SmoothedQuarticStability`.
-/

public section

noncomputable section
open Filter Topology
namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

/-- At tangency, focal-distance excess is bounded by the fourth power
of the circle chord distance. -/
theorem twoFocusCost_critical_quartic_upper
    (b d : ℝ) (hd : 0 < d) (z : ℂ)
    (hz : ‖z‖ = b) (him : |z.im| ≤ d / 2) :
    2 * b ^ 2 * d * (twoFocusCost b d z - 2 * d) ≤ ‖z - (b : ℂ)‖ ^ 4 := by
  let p := ‖(b : ℂ) + d * Complex.I - z‖
  let m := ‖(b : ℂ) - d * Complex.I - z‖
  let h := b - z.re
  let r := d - z.im
  let s := d + z.im
  have hp0 : 0 ≤ p := norm_nonneg _
  have hm0 : 0 ≤ m := norm_nonneg _
  have hyr := abs_le.mp him
  have hr : d / 2 ≤ r := by dsimp only [r]; linarith [hyr.2]
  have hs : d / 2 ≤ s := by dsimp only [s]; linarith [hyr.1]
  have hr0 : 0 ≤ r := by linarith
  have hs0 : 0 ≤ s := by linarith
  have hpp : p ^ 2 = h ^ 2 + r ^ 2 := by
    dsimp only [p, h, r]
    simp [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hmm : m ^ 2 = h ^ 2 + s ^ 2 := by
    dsimp only [m, h, s]
    simp [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hpr : r ≤ p := (sq_le_sq₀ hr0 hp0).mp (by nlinarith [sq_nonneg h])
  have hms : s ≤ m := (sq_le_sq₀ hs0 hm0).mp (by nlinarith [sq_nonneg h])
  have hpbound : d * (p - r) ≤ h ^ 2 := by
    have hprod := mul_nonneg (by linarith : 0 ≤ 2 * r - d) (sub_nonneg.mpr hpr)
    nlinarith [sq_nonneg (p - r)]
  have hmbound : d * (m - s) ≤ h ^ 2 := by
    have hprod := mul_nonneg (by linarith : 0 ≤ 2 * s - d) (sub_nonneg.mpr hms)
    nlinarith [sq_nonneg (m - s)]
  have hrs : r + s = 2 * d := by dsimp only [r, s]; ring
  have hsum : d * (p + m - 2 * d) ≤ 2 * h ^ 2 := by nlinarith
  have hzsq : z.re ^ 2 + z.im ^ 2 = b ^ 2 := by
    have h := congrArg (fun t : ℝ => t ^ 2) hz
    simpa only [Complex.sq_norm, Complex.normSq_apply, ← pow_two] using h
  have hchord : ‖z - (b : ℂ)‖ ^ 2 = 2 * b * h := by
    dsimp only [h]
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
      Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero]
    nlinarith only [hzsq]
  have hchord4 : ‖z - (b : ℂ)‖ ^ 4 = 4 * b ^ 2 * h ^ 2 := by
    convert congrArg (fun t : ℝ => t ^ 2) hchord using 1 <;> ring
  have hscaled := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 2 * b ^ 2)
  change 2 * b ^ 2 * d * (p + m - 2 * d) ≤ _
  rw [hchord4]
  nlinarith only [hscaled]

/-- The critical scalar-phase cost has a quartic upper bound in unit
circle chord distance. -/
theorem critical_unit_phase_quartic_upper
    (b d : ℝ) (hb : 0 < b) (hd : 0 < d) (z : ℂ) (hz : ‖z‖ = 1)
    (him : |((b : ℂ) * z).im| ≤ d / 2) :
    twoFocusCost b d ((b : ℂ) * z) - 2 * d ≤ b ^ 2 / (2 * d) * ‖z - 1‖ ^ 4 := by
  have hnorm : ‖(b : ℂ) * z‖ = b := by simp [hz, abs_of_pos hb]
  have h := twoFocusCost_critical_quartic_upper b d hd ((b : ℂ) * z) hnorm him
  have hfac : (b : ℂ) * z - (b : ℂ) = (b : ℂ) * (z - 1) := by ring
  rw [hfac, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb] at h
  have hp : (twoFocusCost b d ((b : ℂ) * z) - 2 * d) * (2 * b ^ 2 * d) ≤
      b ^ 4 * ‖z - 1‖ ^ 4 := by nlinarith only [h]
  have hq := (le_div_iff₀ (by positivity : 0 < 2 * b ^ 2 * d)).mpr hp
  convert hq using 1
  field_simp

private def tangentCirclePoint (t : ℝ) : ℂ :=
  ⟨(1 - t ^ 2) / (1 + t ^ 2), 2 * t / (1 + t ^ 2)⟩

private theorem tangentCirclePoint_norm (t : ℝ) : ‖tangentCirclePoint t‖ = 1 := by
  have hden : 1 + t ^ 2 ≠ 0 := ne_of_gt (by positivity : 0 < 1 + t ^ 2)
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  simp [tangentCirclePoint, Complex.sq_norm, Complex.normSq_apply]
  field_simp
  ring

private theorem tangentCirclePoint_chord_sq (t : ℝ) :
    ‖tangentCirclePoint t - 1‖ ^ 2 = 4 * t ^ 2 / (1 + t ^ 2) := by
  have hden : 1 + t ^ 2 ≠ 0 := ne_of_gt (by positivity : 0 < 1 + t ^ 2)
  simp [tangentCirclePoint, Complex.sq_norm, Complex.normSq_apply]
  field_simp
  ring

set_option maxHeartbeats 600000 in
/-- No positive quadratic modulus holds even locally at the critical circle
tangency. The violating phases may be chosen arbitrarily close to one. -/
theorem critical_phase_no_quadratic_modulus
    (b d c radius : ℝ) (hb : 0 < b) (hd : 0 < d) (hc : 0 < c) (hradius : 0 < radius) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ 0 < ‖z - 1‖ ∧ ‖z - 1‖ < radius ∧
      twoFocusCost b d ((b : ℂ) * z) - 2 * d < c * ‖z - 1‖ ^ 2 := by
  let t := min 1 (min (d / (8 * b)) (min (c * d / (8 * b ^ 2)) (radius / 4)))
  have ht : 0 < t := by dsimp only [t]; positivity
  have ht1 : t ≤ 1 := min_le_left _ _
  have htd : t ≤ d / (8 * b) := (min_le_right _ _).trans (min_le_left _ _)
  have htc : t ≤ c * d / (8 * b ^ 2) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have htr : t ≤ radius / 4 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  let z := tangentCirclePoint t
  have hz : ‖z‖ = 1 := tangentCirclePoint_norm t
  have hchord : ‖z - 1‖ ^ 2 = 4 * t ^ 2 / (1 + t ^ 2) := tangentCirclePoint_chord_sq t
  have hchordpos : 0 < ‖z - 1‖ := by
    have hpos : 0 < 4 * t ^ 2 / (1 + t ^ 2) := by positivity
    rw [← hchord] at hpos
    nlinarith [norm_nonneg (z - 1)]
  have hchordle : ‖z - 1‖ ^ 2 ≤ 4 * t ^ 2 := by
    rw [hchord]
    apply (div_le_iff₀ (by positivity : 0 < 1 + t ^ 2)).mpr
    nlinarith [sq_nonneg (t ^ 2)]
  have hnormle : ‖z - 1‖ ≤ 2 * t :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp (by nlinarith only [hchordle])
  have himnonneg : 0 ≤ z.im := by change 0 ≤ 2 * t / (1 + t ^ 2); positivity
  have himle : z.im ≤ 2 * t := by
    change 2 * t / (1 + t ^ 2) ≤ 2 * t
    apply (div_le_iff₀ (by positivity : 0 < 1 + t ^ 2)).mpr
    nlinarith [mul_nonneg ht.le (sq_nonneg t)]
  have him : |((b : ℂ) * z).im| ≤ d / 2 := by
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      abs_mul, abs_of_pos hb, abs_of_nonneg himnonneg]
    have h := (le_div_iff₀ (by positivity : 0 < 8 * b)).mp htd
    nlinarith [mul_le_mul_of_nonneg_left himle hb.le]
  have hquad : b ^ 2 / (2 * d) * ‖z - 1‖ ^ 2 < c := by
    have ht2 : t ^ 2 ≤ t := by nlinarith
    have h := (le_div_iff₀ (by positivity : 0 < 8 * b ^ 2)).mp htc
    have hsmall : ‖z - 1‖ ^ 2 ≤ 4 * t := le_trans hchordle (by linarith)
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by positivity : 0 < 2 * d)).mpr
    have hprod := mul_le_mul_of_nonneg_left hsmall (sq_nonneg b)
    nlinarith
  refine ⟨z, hz, hchordpos, ?_, ?_⟩
  · linarith
  · have hu := critical_unit_phase_quartic_upper b d hb hd z hz him
    have hs := mul_lt_mul_of_pos_right hquad (sq_pos_of_pos hchordpos)
    nlinarith only [hu, hs]

/-- Continuous coefficient of the fourth-power phase chord at critical tangency. -/
@[expose]
def criticalPhaseQuarticCoefficient (b d : ℝ) (z : ℂ) : ℝ :=
  b ^ 2 / 4 *
    ((‖(b : ℂ) + d * Complex.I - (b : ℂ) * z‖ + (d - ((b : ℂ) * z).im))⁻¹ +
     (‖(b : ℂ) - d * Complex.I - (b : ℂ) * z‖ + (d + ((b : ℂ) * z).im))⁻¹)

set_option maxHeartbeats 600000 in
/-- Exact quartic factorization on the critical phase circle near one. -/
theorem critical_phase_quartic_factorization (b d : ℝ) (hb : 0 < b) (hd : 0 < d)
    (z : ℂ) (hz : ‖z‖ = 1) (him : |((b : ℂ) * z).im| ≤ d / 2) :
    twoFocusCost b d ((b : ℂ) * z) - 2 * d =
      criticalPhaseQuarticCoefficient b d z * ‖z - 1‖ ^ 4 := by
  let w := (b : ℂ) * z
  let p := ‖(b : ℂ) + d * Complex.I - w‖
  let m := ‖(b : ℂ) - d * Complex.I - w‖
  let h := b - w.re
  let r := d - w.im
  let s := d + w.im
  have hp0 : 0 ≤ p := norm_nonneg _
  have hm0 : 0 ≤ m := norm_nonneg _
  have hyr := abs_le.mp him
  have hr : d / 2 ≤ r := by dsimp only [r, w]; linarith [hyr.2]
  have hs : d / 2 ≤ s := by dsimp only [s, w]; linarith [hyr.1]
  have hpp : p ^ 2 = h ^ 2 + r ^ 2 := by
    dsimp only [p, h, r]
    simp [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hmm : m ^ 2 = h ^ 2 + s ^ 2 := by
    dsimp only [m, h, s]
    simp [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hpr : p + r ≠ 0 := ne_of_gt (by linarith : 0 < p + r)
  have hms : m + s ≠ 0 := ne_of_gt (by linarith : 0 < m + s)
  have hp : p - r = h ^ 2 / (p + r) := (eq_div_iff hpr).mpr (by nlinarith only [hpp])
  have hm : m - s = h ^ 2 / (m + s) := (eq_div_iff hms).mpr (by nlinarith only [hmm])
  have hrs : r + s = 2 * d := by dsimp only [r, s]; ring
  have hw : ‖w‖ = b := by simp [w, hz, abs_of_pos hb]
  have hwsq : w.re ^ 2 + w.im ^ 2 = b ^ 2 := by
    have hh := congrArg (fun t : ℝ => t ^ 2) hw
    simpa only [Complex.sq_norm, Complex.normSq_apply, ← pow_two] using hh
  have hchord : b ^ 2 * ‖z - 1‖ ^ 2 = 2 * b * h := by
    have hf : w - (b : ℂ) = (b : ℂ) * (z - 1) := by dsimp only [w]; ring
    have hn : ‖w - (b : ℂ)‖ ^ 2 = 2 * b * h := by
      dsimp only [h]
      simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
        Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero]
      nlinarith only [hwsq]
    rw [hf, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb, mul_pow] at hn
    exact hn
  have hchord4 : b ^ 2 * ‖z - 1‖ ^ 4 = 4 * h ^ 2 := by
    have hh := congrArg (fun t : ℝ => t ^ 2) hchord
    nlinarith [sq_pos_of_pos hb]
  change p + m - 2 * d = b ^ 2 / 4 * ((p + r)⁻¹ + (m + s)⁻¹) * ‖z - 1‖ ^ 4
  calc
    _ = (p - r) + (m - s) := by linarith only [hrs]
    _ = h ^ 2 / (p + r) + h ^ 2 / (m + s) := by rw [hp, hm]
    _ = (b ^ 2 * ‖z - 1‖ ^ 4) / 4 * ((p + r)⁻¹ + (m + s)⁻¹) := by
      rw [hchord4]
      ring
    _ = _ := by ring

private theorem criticalPhaseQuarticCoefficient_one (b d : ℝ) (hd : 0 < d) :
    criticalPhaseQuarticCoefficient b d 1 = b ^ 2 / (4 * d) := by
  have hp : (b : ℂ) + d * Complex.I - (b : ℂ) * 1 = d * Complex.I := by ring
  have hm : (b : ℂ) - d * Complex.I - (b : ℂ) * 1 = -(d * Complex.I) := by ring
  unfold criticalPhaseQuarticCoefficient
  rw [hp, hm]
  simp only [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hd, Complex.norm_I, mul_one, Complex.ofReal_im, sub_zero, add_zero]
  field_simp

/-- The critical scalar phase excess has the exact fourth-order chord coefficient. -/
theorem tendsto_critical_phase_quartic_ratio (b d : ℝ) (hb : 0 < b) (hd : 0 < d) :
    Tendsto (fun z : ℂ => (twoFocusCost b d ((b : ℂ) * z) - 2 * d) / ‖z - 1‖ ^ 4)
      (𝓝[{z : ℂ | ‖z‖ = 1 ∧ z ≠ 1}] 1) (𝓝 (b ^ 2 / (4 * d))) := by
  have hcoef : ContinuousAt (criticalPhaseQuarticCoefficient b d) 1 := by
    unfold criticalPhaseQuarticCoefficient
    fun_prop (disch := simp [abs_of_pos hd, ne_of_gt hd])
  have hnear : ∀ᶠ z : ℂ in 𝓝 (1 : ℂ), |((b : ℂ) * z).im| < d / 2 := by
    have hcont : Continuous (fun z : ℂ => |((b : ℂ) * z).im|) := by fun_prop
    exact (isOpen_lt hcont continuous_const).mem_nhds (by simpa using half_pos hd)
  have heq : (fun z : ℂ => (twoFocusCost b d ((b : ℂ) * z) - 2 * d) / ‖z - 1‖ ^ 4) =ᶠ[
      𝓝[{z : ℂ | ‖z‖ = 1 ∧ z ≠ 1}] 1] criticalPhaseQuarticCoefficient b d := by
    filter_upwards [self_mem_nhdsWithin, hnear.filter_mono nhdsWithin_le_nhds] with z hz him
    rw [critical_phase_quartic_factorization b d hb hd z hz.1 him.le]
    exact mul_div_cancel_right₀ _ (pow_ne_zero 4 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hz.2)))
  rw [← criticalPhaseQuarticCoefficient_one b d hd]
  exact (hcoef.tendsto.mono_left nhdsWithin_le_nhds).congr' heq.symm

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

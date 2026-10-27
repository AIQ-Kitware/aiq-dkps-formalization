/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SchattenPhaseCriticalAngle
public import Mathlib.Analysis.Calculus.LHopital

/-!
# Exact critical Schatten phase growth

At the critical angle the second variation vanishes, but the fourth
variation is positive. This identifies the local phase conditioning
at the closed canonical threshold; a quadratic error bound cannot
extend through that threshold.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open Filter Set
open scoped Topology

private def chordPowerSecond (p t : ℝ) : ℝ :=
  p / 2 * phaseChord t ^ (p - 2) * (p * Real.cos t - (2 - p))

private def chordPowerThird (p t : ℝ) : ℝ :=
  p / 2 * ((p - 2) * Real.cos (t / 2) * phaseChord t ^ (p - 3) *
    (p * Real.cos t - (2 - p)) - p * Real.sin t * phaseChord t ^ (p - 2))

private def chordPowerFourth (p t : ℝ) : ℝ :=
  p / 2 * (((p - 2) * (p - 3) * Real.cos (t / 2) ^ 2 * phaseChord t ^ (p - 4) -
      (p - 2) / 2 * Real.sin (t / 2) * phaseChord t ^ (p - 3)) *
      (p * Real.cos t - (2 - p)) -
    2 * p * (p - 2) * Real.cos (t / 2) * Real.sin t * phaseChord t ^ (p - 3) -
      p * Real.cos t * phaseChord t ^ (p - 2))

private theorem cos_half_hasDerivAt (t : ℝ) :
    HasDerivAt (fun x : ℝ => Real.cos (x / 2)) (-Real.sin (t / 2) / 2) t := by
  simpa only [id_eq, div_eq_mul_inv, one_mul] using ((hasDerivAt_id t).div_const 2).cos

private theorem chordPowerSecond_hasDerivAt (p t : ℝ) (ht : 0 < phaseChord t) :
    HasDerivAt (chordPowerSecond p) (chordPowerThird p t) t := by
  have hpow := chord_rpow_hasDerivAt (p - 2) t ht
  simp only [show p - 2 - 1 = p - 3 by ring] at hpow
  have hB := ((Real.hasDerivAt_cos t).const_mul p).sub_const (2 - p)
  have h := (hpow.const_mul (p / 2)).mul hB
  convert h using 1
  · rfl
  · dsimp only [chordPowerThird]
    ring

private theorem chordPowerThird_hasDerivAt (p t : ℝ) (ht : 0 < phaseChord t) :
    HasDerivAt (chordPowerThird p) (chordPowerFourth p t) t := by
  have hpow2 := chord_rpow_hasDerivAt (p - 2) t ht
  have hpow3 := chord_rpow_hasDerivAt (p - 3) t ht
  simp only [show p - 2 - 1 = p - 3 by ring] at hpow2
  simp only [show p - 3 - 1 = p - 4 by ring] at hpow3
  have hB := ((Real.hasDerivAt_cos t).const_mul p).sub_const (2 - p)
  have hleft := (((cos_half_hasDerivAt t).const_mul (p - 2)).mul hpow3).mul hB
  have hright := ((Real.hasDerivAt_sin t).const_mul p).mul hpow2
  have h := (hleft.sub hright).const_mul (p / 2)
  convert h using 1
  · rfl
  · dsimp only [chordPowerFourth, Pi.mul_apply]
    ring

private def phaseSecond (p theta delta : ℝ) : ℝ :=
  chordPowerSecond p (theta + delta) + chordPowerSecond p (theta - delta)

private def phaseThird (p theta delta : ℝ) : ℝ :=
  chordPowerThird p (theta + delta) - chordPowerThird p (theta - delta)

private def phaseFourth (p theta delta : ℝ) : ℝ :=
  chordPowerFourth p (theta + delta) + chordPowerFourth p (theta - delta)

private theorem phaseSlope_hasDerivAt (p theta delta : ℝ) (hp : p ≠ 0)
    (hplus : 0 < phaseChord (theta + delta)) (hminus : 0 < phaseChord (theta - delta)) :
    HasDerivAt (phaseSlope p theta) (phaseSecond p theta delta) delta := by
  have ha := (phaseAmplitude_hasDerivAt p (theta + delta) hplus).comp delta
    ((hasDerivAt_id delta).const_add theta)
  have hb := (phaseAmplitude_hasDerivAt p (theta - delta) hminus).comp delta
    ((hasDerivAt_id delta).const_sub theta)
  have h := (ha.sub hb).const_mul p
  convert h using 1
  · funext x
    simp only [phaseSlope, Function.comp_apply, Pi.sub_apply]
  · rw [amplitudeDerivative_eq_critical p _ hp hplus,
      amplitudeDerivative_eq_critical p _ hp hminus]
    dsimp only [phaseSecond, chordPowerSecond]
    ring

private theorem phaseSecond_hasDerivAt (p theta delta : ℝ)
    (hplus : 0 < phaseChord (theta + delta)) (hminus : 0 < phaseChord (theta - delta)) :
    HasDerivAt (phaseSecond p theta) (phaseThird p theta delta) delta := by
  have ha := (chordPowerSecond_hasDerivAt p (theta + delta) hplus).comp delta
    ((hasDerivAt_id delta).const_add theta)
  have hb := (chordPowerSecond_hasDerivAt p (theta - delta) hminus).comp delta
    ((hasDerivAt_id delta).const_sub theta)
  convert ha.add hb using 1
  · rfl
  · dsimp only [phaseThird]
    ring

private theorem phaseThird_hasDerivAt (p theta delta : ℝ)
    (hplus : 0 < phaseChord (theta + delta)) (hminus : 0 < phaseChord (theta - delta)) :
    HasDerivAt (phaseThird p theta) (phaseFourth p theta delta) delta := by
  have ha := (chordPowerThird_hasDerivAt p (theta + delta) hplus).comp delta
    ((hasDerivAt_id delta).const_add theta)
  have hb := (chordPowerThird_hasDerivAt p (theta - delta) hminus).comp delta
    ((hasDerivAt_id delta).const_sub theta)
  convert ha.sub hb using 1
  · rfl
  · dsimp only [phaseFourth]
    ring

private theorem chordPowerFourth_critical (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    chordPowerFourth p (criticalAngle p) =
      p * (2 - p) / 2 * phaseChord (criticalAngle p) ^ (p - 2) := by
  let t := criticalAngle p
  have hp : p ≠ 0 := by linarith
  have ht := criticalAngle_mem p hp1 hp2
  have hpos : 0 < phaseChord t := phaseChord_pos ht.1 (by linarith [ht.2, Real.pi_pos])
  have hB : p * Real.cos t - (2 - p) = 0 := by
    rw [show Real.cos t = (2 - p) / p from cos_criticalAngle p hp1 hp2]
    field_simp
    ring
  have hcos : p * Real.cos (t / 2) ^ 2 = 1 := by
    have h := Real.cos_two_mul (t / 2)
    rw [show 2 * (t / 2) = t by ring] at h
    nlinarith
  have hsin : Real.sin t = 2 * Real.sin (t / 2) * Real.cos (t / 2) := by
    simpa only [show 2 * (t / 2) = t by ring] using Real.sin_two_mul (t / 2)
  have hpow : phaseChord t ^ (p - 2) = phaseChord t ^ (p - 3) * phaseChord t := by
    calc
      _ = phaseChord t ^ ((p - 3) + 1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hpos, Real.rpow_one]
  have hbracket : 2 * (p - 2) * Real.cos (t / 2) ^ 2 + Real.cos t = (p - 2) / p := by
    apply (eq_div_iff hp).mpr
    nlinarith
  change chordPowerFourth p t = _
  calc
    _ = -(p ^ 2 / 2) * phaseChord t ^ (p - 2) *
        (2 * (p - 2) * Real.cos (t / 2) ^ 2 + Real.cos t) := by
      dsimp only [chordPowerFourth]
      rw [hB, mul_zero, hsin, hpow]
      dsimp only [phaseChord]
      ring
    _ = _ := by
      rw [hbracket]
      field_simp
      ring

/-- The fourth phase variation at the critical angle is strictly
positive, with its exact coefficient. -/
private theorem phaseFourth_critical (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    HasDerivAt (phaseThird p (criticalAngle p))
      (p * (2 - p) * phaseChord (criticalAngle p) ^ (p - 2)) 0 := by
  have ht := criticalAngle_mem p hp1 hp2
  have hpos := phaseChord_pos ht.1 (by linarith [ht.2, Real.pi_pos])
  have h := phaseThird_hasDerivAt p (criticalAngle p) 0 (by simpa using hpos)
    (by simpa using hpos)
  convert h using 1
  dsimp only [phaseFourth]
  rw [add_zero, sub_zero, chordPowerFourth_critical p hp1 hp2]
  ring

private theorem tendsto_div_pow_succ (n : ℕ) (f g : ℝ → ℝ) (l : ℝ)
    (hd : ∀ᶠ x in 𝓝[≠] (0 : ℝ), HasDerivAt f (g x) x)
    (hf : Tendsto f (𝓝[≠] 0) (𝓝 0))
    (hg : Tendsto (fun x => g x / x ^ n) (𝓝[≠] 0) (𝓝 l)) :
    Tendsto (fun x => f x / x ^ (n + 1)) (𝓝[≠] 0) (𝓝 (l / (n + 1))) := by
  have hp (x : ℝ) : HasDerivAt (fun y : ℝ => y ^ (n + 1))
      ((n + 1 : ℝ) * x ^ n) x := by
    convert (hasDerivAt_id x).pow (n + 1) using 1
    · funext y
      simp only [Pi.pow_apply, id_eq]
    · simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, mul_one, id_eq]
  have hne : ∀ᶠ x in 𝓝[≠] (0 : ℝ), (n + 1 : ℝ) * x ^ n ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact mul_ne_zero (by positivity) (pow_ne_zero n hx)
  have hzero : Tendsto (fun x : ℝ => x ^ (n + 1)) (𝓝[≠] 0) (𝓝 0) := by
    have hc : Continuous (fun x : ℝ => x ^ (n + 1)) := continuous_id.pow (n + 1)
    simpa only [zero_pow (Nat.succ_ne_zero n)] using
      ((hc.tendsto 0).mono_left nhdsWithin_le_nhds)
  apply HasDerivAt.lhopital_zero_nhdsNE hd (Eventually.of_forall hp) hne hf hzero
  simpa only [div_div, mul_comm] using hg.div_const (n + 1 : ℝ)

/-- The exact fourth-order phase law at the Schatten transition.
The limit is two-sided; the positive coefficient is therefore also the
sharp local phase growth coefficient on the feasible positive phases. -/
theorem tendsto_critical_phase_quartic_ratio (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    Tendsto (fun delta : ℝ =>
      (phasePower p (criticalAngle p) delta - phasePower p (criticalAngle p) 0) / delta ^ 4)
      (𝓝[≠] 0)
      (𝓝 (p * (2 - p) * phaseChord (criticalAngle p) ^ (p - 2) / 24)) := by
  let theta := criticalAngle p
  have ht := criticalAngle_mem p hp1 hp2
  have hp : p ≠ 0 := by linarith
  have hpos : 0 < phaseChord theta := phaseChord_pos ht.1 (by linarith [ht.2, Real.pi_pos])
  have hc : Continuous phaseChord := by unfold phaseChord; fun_prop
  have hplus : Tendsto (fun d : ℝ => phaseChord (theta + d)) (𝓝 0) (𝓝 (phaseChord theta)) := by
    have hcont : Continuous (fun d : ℝ => phaseChord (theta + d)) :=
      hc.comp (continuous_const.add continuous_id)
    simpa only [add_zero] using hcont.tendsto 0
  have hminus : Tendsto (fun d : ℝ => phaseChord (theta - d)) (𝓝 0) (𝓝 (phaseChord theta)) := by
    have hcont : Continuous (fun d : ℝ => phaseChord (theta - d)) :=
      hc.comp (continuous_const.sub continuous_id)
    simpa only [sub_zero] using hcont.tendsto 0
  have hnear : ∀ᶠ d in 𝓝[≠] (0 : ℝ),
      0 < phaseChord (theta + d) ∧ 0 < phaseChord (theta - d) :=
    ((hplus.eventually (Ioi_mem_nhds hpos)).and
    (hminus.eventually (Ioi_mem_nhds hpos))).filter_mono nhdsWithin_le_nhds
  have hd0 := hnear.mono fun d hd =>
    (phasePower_hasDerivAt p theta d hd.1 hd.2).sub_const (phasePower p theta 0)
  have hd1 := hnear.mono fun d hd => phaseSlope_hasDerivAt p theta d hp hd.1 hd.2
  have hd2 := hnear.mono fun d hd => phaseSecond_hasDerivAt p theta d hd.1 hd.2
  have hB : p * Real.cos theta - (2 - p) = 0 := by
    rw [show Real.cos theta = (2 - p) / p from cos_criticalAngle p hp1 hp2]
    field_simp
    ring
  have hz1 : phaseSlope p theta 0 = 0 := by simp [phaseSlope]
  have hz2 : phaseSecond p theta 0 = 0 := by simp [phaseSecond, chordPowerSecond, hB]
  have hz3 : phaseThird p theta 0 = 0 := by simp [phaseThird]
  have hf0 : Tendsto (fun d => phasePower p theta d - phasePower p theta 0)
      (𝓝[≠] 0) (𝓝 0) := by
    simpa only [sub_self] using
      (((phasePower_hasDerivAt_zero p theta ht.1 ht.2).continuousAt.tendsto.sub_const
        (phasePower p theta 0)).mono_left nhdsWithin_le_nhds)
  have hf1 : Tendsto (phaseSlope p theta) (𝓝[≠] 0) (𝓝 0) := by
    simpa only [hz1] using
      ((phaseSlope_hasDerivAt p theta 0 hp (by simpa using hpos) (by simpa using hpos)).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds)
  have hf2 : Tendsto (phaseSecond p theta) (𝓝[≠] 0) (𝓝 0) := by
    simpa only [hz2] using
      ((phaseSecond_hasDerivAt p theta 0 (by simpa using hpos) (by simpa using hpos)).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds)
  have h3 : Tendsto (fun d => phaseThird p theta d / d ^ 1) (𝓝[≠] 0)
      (𝓝 (p * (2 - p) * phaseChord theta ^ (p - 2))) := by
    have hd3 : HasDerivAt (phaseThird p theta)
        (p * (2 - p) * phaseChord theta ^ (p - 2)) 0 := phaseFourth_critical p hp1 hp2
    simpa only [zero_add, hz3, sub_zero, smul_eq_mul, pow_one, div_eq_mul_inv, mul_comm] using
      hd3.tendsto_slope_zero
  have h2 := tendsto_div_pow_succ 1 _ _ _ hd2 hf2 h3
  have h1 := tendsto_div_pow_succ 2 _ _ _ hd1 hf1 h2
  have h0 := tendsto_div_pow_succ 3 _ _ _ hd0 hf0 h1
  convert h0 using 1
  congr 1
  ring

/-- The critical fourth-order coefficient is positive throughout the
strict intermediate-exponent regime. -/
theorem critical_phase_quartic_coefficient_pos (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    0 < p * (2 - p) * phaseChord (criticalAngle p) ^ (p - 2) / 24 := by
  have ht := criticalAngle_mem p hp1 hp2
  have hc := phaseChord_pos ht.1 (by linarith [ht.2, Real.pi_pos])
  exact div_pos (mul_pos (mul_pos (by linarith) (by linarith))
    (Real.rpow_pos_of_pos hc _)) (by norm_num)

/-- Two-sided quartic growth on an actual feasible phase neighborhood,
with constants controlled by the exact limiting coefficient. -/
theorem critical_phase_quartic_growth (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    let a := p * (2 - p) * phaseChord (criticalAngle p) ^ (p - 2) / 24
    ∃ radius ∈ Ioo 0 (criticalAngle p), ∀ delta ∈ Icc 0 radius,
      a / 2 * delta ^ 4 ≤ phasePower p (criticalAngle p) delta -
          phasePower p (criticalAngle p) 0 ∧
        phasePower p (criticalAngle p) delta - phasePower p (criticalAngle p) 0 ≤
          2 * a * delta ^ 4 := by
  let a := p * (2 - p) * phaseChord (criticalAngle p) ^ (p - 2) / 24
  have ha : 0 < a := critical_phase_quartic_coefficient_pos p hp1 hp2
  obtain ⟨d, hd, hbound⟩ := Metric.tendsto_nhdsWithin_nhds.mp
    (tendsto_critical_phase_quartic_ratio p hp1 hp2) (a / 2) (by positivity)
  have ht := criticalAngle_mem p hp1 hp2
  refine ⟨min (d / 2) (criticalAngle p / 2),
    ⟨lt_min (half_pos hd) (half_pos ht.1),
      (min_le_right _ _).trans_lt (by linarith [ht.1])⟩, ?_⟩
  intro delta hdelta
  rcases eq_or_lt_of_le hdelta.1 with heq | hpos
  · subst delta
    simp only [zero_pow (by norm_num : 4 ≠ 0), mul_zero, sub_self, le_refl, and_self]
  have hsmall : dist delta (0 : ℝ) < d := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hpos]
    exact hdelta.2.trans_lt ((min_le_left _ _).trans_lt (by linarith))
  have h := hbound (show delta ∈ ({0}ᶜ : Set ℝ) from hpos.ne') hsmall
  rw [Real.dist_eq] at h
  change |(phasePower p (criticalAngle p) delta - phasePower p (criticalAngle p) 0) /
    delta ^ 4 - a| < a / 2 at h
  have hlo : a / 2 < (phasePower p (criticalAngle p) delta -
      phasePower p (criticalAngle p) 0) / delta ^ 4 := by linarith [(abs_lt.mp h).1]
  have hhi : (phasePower p (criticalAngle p) delta -
      phasePower p (criticalAngle p) 0) / delta ^ 4 < 2 * a := by linarith [(abs_lt.mp h).2]
  exact ⟨((lt_div_iff₀ (pow_pos hpos 4)).mp hlo).le,
    ((div_lt_iff₀ (pow_pos hpos 4)).mp hhi).le⟩

/-- Critical excess is smaller than every positive quadratic multiple
as the phase tends to zero, despite the unique global optimum. -/
theorem tendsto_critical_phase_quadratic_ratio (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    Tendsto (fun delta : ℝ =>
      (phasePower p (criticalAngle p) delta - phasePower p (criticalAngle p) 0) / delta ^ 2)
      (𝓝[≠] 0) (𝓝 0) := by
  have hc : Tendsto (fun delta : ℝ => delta ^ 2) (𝓝[≠] 0) (𝓝 0) := by
    have hcont : Continuous (fun delta : ℝ => delta ^ 2) := continuous_id.pow 2
    simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have h := (tendsto_critical_phase_quartic_ratio p hp1 hp2).mul hc
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with delta hdelta
  have hne : delta ≠ 0 := hdelta
  field_simp

/-- Every phase neighborhood contains a feasible nonzero competitor
violating any proposed positive quadratic growth coefficient. -/
theorem critical_phase_no_quadratic_modulus (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2)
    (c radius : ℝ) (hc : 0 < c) (hradius : 0 < radius) :
    ∃ delta ∈ Ioo 0 (criticalAngle p), delta < radius ∧
      phasePower p (criticalAngle p) delta - phasePower p (criticalAngle p) 0 <
        c * delta ^ 2 := by
  have ht := criticalAngle_mem p hp1 hp2
  have hlim := (tendsto_critical_phase_quadratic_ratio p hp1 hp2).mono_left
    (nhdsGT_le_nhdsNE (0 : ℝ))
  have hsmall : ∀ᶠ delta : ℝ in 𝓝[>] 0, delta ∈ Ioo 0 (min radius (criticalAngle p)) :=
    Ioo_mem_nhdsGT (lt_min hradius ht.1)
  obtain ⟨delta, hdelta, hcost⟩ := (hsmall.and (hlim.eventually (Iio_mem_nhds hc))).exists
  exact ⟨delta, ⟨hdelta.1, hdelta.2.trans_le (min_le_right _ _)⟩,
    hdelta.2.trans_le (min_le_left _ _), (div_lt_iff₀ (pow_pos hdelta.1 2)).mp hcost⟩

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

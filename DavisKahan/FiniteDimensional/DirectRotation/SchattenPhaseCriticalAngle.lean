/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SchattenPhaseMinimum
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# The critical angle and the two amplitude branches

For `1 < p < 2`, the auxiliary amplitude increases up to the critical angle
`arccos ((2-p)/p)` and decreases afterward. These branches organize the
stationary spectra in the unrestricted Schatten optimization problem.
-/

public section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open Set

noncomputable section

/-- The sharp angle at which canonical scalar-phase optimality changes. -/
@[expose]
def criticalAngle (p : ℝ) : ℝ := Real.arccos ((2 - p) / p)

private theorem critical_cos_mem (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    (2 - p) / p ∈ Ioo 0 1 := by
  constructor
  · exact div_pos (by linarith) (by linarith)
  · exact (div_lt_one (by linarith : 0 < p)).2 (by linarith)

/-- The transition occurs strictly between zero and a right angle. -/
theorem criticalAngle_mem (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    criticalAngle p ∈ Ioo 0 (Real.pi / 2) := by
  have hc := critical_cos_mem p hp1 hp2
  exact ⟨Real.arccos_pos.2 hc.2, Real.arccos_lt_pi_div_two.2 hc.1⟩

/-- The cosine of the critical angle is the exponent-dependent threshold. -/
theorem cos_criticalAngle (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    Real.cos (criticalAngle p) = (2 - p) / p := by
  have hc := critical_cos_mem p hp1 hp2
  exact Real.cos_arccos (by linarith [hc.1]) hc.2.le

/-- The algebraic threshold is equivalent to the explicit angle cutoff. -/
theorem critical_inequality_iff (p theta : ℝ) (hp1 : 1 < p) (hp2 : p < 2)
    (hθ : theta ∈ Icc 0 Real.pi) :
    2 - p ≤ p * Real.cos theta ↔ theta ≤ criticalAngle p := by
  have hc := criticalAngle_mem p hp1 hp2
  have hcπ : criticalAngle p ∈ Icc 0 Real.pi :=
    ⟨hc.1.le, by linarith [hc.2, Real.pi_pos]⟩
  rw [mul_comm p (Real.cos theta), ← div_le_iff₀ (by linarith : 0 < p),
    ← cos_criticalAngle p hp1 hp2]
  exact (Real.strictAntiOn_cos.le_iff_ge hcπ hθ)

/-- A canonical scalar phase is globally optimal precisely below the
critical angle, including the zero-curvature transition itself. -/
theorem canonical_phase_isMinOn_iff_le_criticalAngle
    (p theta : ℝ) (hp1 : 1 < p) (hp2 : p < 2)
    (h0 : 0 < theta) (hπ : theta < Real.pi / 2) :
    IsMinOn (phasePower p theta) (Icc 0 theta) 0 ↔ theta ≤ criticalAngle p := by
  rw [canonical_phase_isMinOn_iff p theta hp1 hp2 h0 hπ]
  exact critical_inequality_iff p theta hp1 hp2
    ⟨h0.le, by linarith [Real.pi_pos]⟩

private theorem chord_pos_on_angle {t : ℝ} (ht : t ∈ Ioo 0 Real.pi) :
    0 < phaseChord t := by
  exact mul_pos (by norm_num) (Real.sin_pos_of_pos_of_lt_pi
    (by linarith [ht.1]) (by linarith [ht.2, Real.pi_pos]))

/-- The amplitude derivative is positive on the small-angle branch. -/
theorem amplitudeDerivative_pos_of_lt_criticalAngle
    (p t : ℝ) (hp1 : 1 < p) (hp2 : p < 2)
    (h0 : 0 < t) (hc : t < criticalAngle p) :
    0 < amplitudeDerivative p t := by
  have hcrit := criticalAngle_mem p hp1 hp2
  have ht : t ∈ Ioo 0 Real.pi := ⟨h0, by linarith [hcrit.2, Real.pi_pos]⟩
  rw [amplitudeDerivative_eq_critical p t (by linarith) (chord_pos_on_angle ht)]
  apply div_pos _ (by norm_num)
  apply mul_pos (Real.rpow_pos_of_pos (chord_pos_on_angle ht) _)
  have hcos := Real.strictAntiOn_cos
    ⟨h0.le, ht.2.le⟩ ⟨hcrit.1.le, by linarith [hcrit.2, Real.pi_pos]⟩ hc
  rw [cos_criticalAngle p hp1 hp2] at hcos
  have := (div_lt_iff₀ (by linarith : 0 < p)).1 hcos
  nlinarith

/-- The amplitude is continuous through both endpoint phases for `p > 1`. -/
theorem continuous_phaseAmplitude (p : ℝ) (hp1 : 1 < p) :
    Continuous (phaseAmplitude p) := by
  have hc : Continuous phaseChord := by unfold phaseChord; fun_prop
  exact (Real.continuous_cos.comp (continuous_id.div_const 2)).mul
    ((Real.continuous_rpow_const (by linarith : 0 ≤ p - 1)).comp hc)

/-- The small-angle amplitude branch is strictly increasing, including its
zero endpoint and its critical maximum. -/
theorem phaseAmplitude_strictMonoOn (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    StrictMonoOn (phaseAmplitude p) (Icc 0 (criticalAngle p)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    (continuous_phaseAmplitude p hp1).continuousOn
  intro t ht
  rw [interior_Icc] at ht
  have hcrit := criticalAngle_mem p hp1 hp2
  have hchord := chord_pos_on_angle
    (show t ∈ Ioo 0 Real.pi from ⟨ht.1, by linarith [hcrit.2, ht.2, Real.pi_pos]⟩)
  rw [(phaseAmplitude_hasDerivAt p t hchord).deriv]
  exact amplitudeDerivative_pos_of_lt_criticalAngle p t hp1 hp2 ht.1 ht.2

/-- The amplitude derivative is negative on the large-angle branch. -/
theorem amplitudeDerivative_neg_of_criticalAngle_lt
    (p t : ℝ) (hp1 : 1 < p) (hp2 : p < 2)
    (hc : criticalAngle p < t) (hπ : t < Real.pi) :
    amplitudeDerivative p t < 0 := by
  have hcrit := criticalAngle_mem p hp1 hp2
  have ht : t ∈ Ioo 0 Real.pi := ⟨hcrit.1.trans hc, hπ⟩
  rw [amplitudeDerivative_eq_critical p t (by linarith) (chord_pos_on_angle ht)]
  apply div_neg_of_neg_of_pos _ (by norm_num)
  apply mul_neg_of_pos_of_neg (Real.rpow_pos_of_pos (chord_pos_on_angle ht) _)
  have hcos := Real.strictAntiOn_cos
    ⟨hcrit.1.le, by linarith [hcrit.2, Real.pi_pos]⟩ ⟨ht.1.le, hπ.le⟩ hc
  rw [cos_criticalAngle p hp1 hp2] at hcos
  have := (lt_div_iff₀ (by linarith : 0 < p)).1 hcos
  nlinarith

/-- The large-angle amplitude branch is strictly decreasing through its
zero value at `pi`. -/
theorem phaseAmplitude_strictAntiOn (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    StrictAntiOn (phaseAmplitude p) (Icc (criticalAngle p) Real.pi) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    (continuous_phaseAmplitude p hp1).continuousOn
  intro t ht
  rw [interior_Icc] at ht
  have hcrit := criticalAngle_mem p hp1 hp2
  have hchord := chord_pos_on_angle
    (show t ∈ Ioo 0 Real.pi from ⟨hcrit.1.trans ht.1, ht.2⟩)
  rw [(phaseAmplitude_hasDerivAt p t hchord).deriv]
  exact amplitudeDerivative_neg_of_criticalAngle_lt p t hp1 hp2 ht.1 ht.2

/-- The auxiliary amplitude vanishes at phase zero. -/
theorem phaseAmplitude_zero (p : ℝ) (hp1 : 1 < p) : phaseAmplitude p 0 = 0 := by
  simp [phaseAmplitude, phaseChord, Real.zero_rpow (by linarith : p - 1 ≠ 0)]

/-- The auxiliary amplitude vanishes at phase `pi`. -/
theorem phaseAmplitude_pi (p : ℝ) : phaseAmplitude p Real.pi = 0 := by
  simp [phaseAmplitude, Real.cos_pi_div_two]

/-- Every positive amplitude below the maximum has exactly one phase on
each side of the critical angle. -/
theorem phaseAmplitude_two_roots (p g : ℝ) (hp1 : 1 < p) (hp2 : p < 2)
    (hg0 : 0 < g) (hgm : g < phaseAmplitude p (criticalAngle p)) :
    (∃! a, a ∈ Ioo 0 (criticalAngle p) ∧ phaseAmplitude p a = g) ∧
      (∃! b, b ∈ Ioo (criticalAngle p) Real.pi ∧ phaseAmplitude p b = g) := by
  have hcrit := criticalAngle_mem p hp1 hp2
  have ha := intermediate_value_Ioo hcrit.1.le
    (continuous_phaseAmplitude p hp1).continuousOn
    (show g ∈ Ioo (phaseAmplitude p 0) (phaseAmplitude p (criticalAngle p)) by
      rw [phaseAmplitude_zero p hp1]; exact ⟨hg0, hgm⟩)
  have hb := intermediate_value_Ioo' (by linarith [hcrit.2, Real.pi_pos] :
      criticalAngle p ≤ Real.pi) (continuous_phaseAmplitude p hp1).continuousOn
    (show g ∈ Ioo (phaseAmplitude p Real.pi) (phaseAmplitude p (criticalAngle p)) by
      rw [phaseAmplitude_pi]; exact ⟨hg0, hgm⟩)
  obtain ⟨a, ha, hag⟩ := ha
  obtain ⟨b, hb, hbg⟩ := hb
  constructor
  · refine ⟨a, ⟨ha, hag⟩, ?_⟩
    intro x hx
    exact (phaseAmplitude_strictMonoOn p hp1 hp2).injOn
      ⟨hx.1.1.le, hx.1.2.le⟩ ⟨ha.1.le, ha.2.le⟩ (hx.2.trans hag.symm)
  · refine ⟨b, ⟨hb, hbg⟩, ?_⟩
    intro x hx
    exact (phaseAmplitude_strictAntiOn p hp1 hp2).injOn
      ⟨hx.1.1.le, hx.1.2.le⟩ ⟨hb.1.le, hb.2.le⟩ (hx.2.trans hbg.symm)

/-- Reflecting a small phase about `pi/2` strictly lowers its amplitude
when the exponent is below two. -/
theorem phaseAmplitude_pi_sub_lt (p a : ℝ) (hp2 : p < 2)
    (ha0 : 0 < a) (haπ : a < Real.pi / 2) :
    phaseAmplitude p (Real.pi - a) < phaseAmplitude p a := by
  let u := a / 2
  have hs : 0 < Real.sin u :=
    Real.sin_pos_of_pos_of_lt_pi (by dsimp [u]; linarith)
      (by dsimp [u]; linarith [Real.pi_pos])
  have hc : 0 < Real.cos u :=
    Real.cos_pos_of_mem_Ioo ⟨by dsimp [u]; linarith [Real.pi_pos],
      by dsimp [u]; linarith [Real.pi_pos]⟩
  have hsc : Real.sin u < Real.cos u := by
    rw [← Real.sin_pi_div_two_sub]
    apply Real.strictMonoOn_sin
      ⟨by dsimp [u]; linarith [Real.pi_pos], by dsimp [u]; linarith [Real.pi_pos]⟩
      ⟨by dsimp [u]; linarith [Real.pi_pos], by dsimp [u]; linarith⟩
    dsimp [u]
    linarith
  have hfactor (x : ℝ) (hx : 0 < x) : x ^ (p - 1) * x ^ (2 - p) = x := by
    rw [← Real.rpow_add hx, show p - 1 + (2 - p) = 1 by ring, Real.rpow_one]
  have hcmp : Real.sin u * Real.cos u ^ (p - 1) <
      Real.cos u * Real.sin u ^ (p - 1) := by
    calc
      Real.sin u * Real.cos u ^ (p - 1) =
          (Real.sin u ^ (p - 1) * Real.sin u ^ (2 - p)) * Real.cos u ^ (p - 1) := by
        rw [hfactor (Real.sin u) hs]
      _ = (Real.sin u ^ (p - 1) * Real.cos u ^ (p - 1)) * Real.sin u ^ (2 - p) := by ring
      _ < (Real.sin u ^ (p - 1) * Real.cos u ^ (p - 1)) * Real.cos u ^ (2 - p) :=
        mul_lt_mul_of_pos_left (Real.rpow_lt_rpow hs.le hsc (by linarith))
          (mul_pos (Real.rpow_pos_of_pos hs _) (Real.rpow_pos_of_pos hc _))
      _ = Real.cos u * Real.sin u ^ (p - 1) := by
        calc
          _ = (Real.cos u ^ (p - 1) * Real.cos u ^ (2 - p)) * Real.sin u ^ (p - 1) := by ring
          _ = _ := by rw [hfactor (Real.cos u) hc]
  unfold phaseAmplitude phaseChord
  rw [show (Real.pi - a) / 2 = Real.pi / 2 - u by dsimp [u]; ring,
    Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
  change Real.sin u * (2 * Real.cos u) ^ (p - 1) <
    Real.cos u * (2 * Real.sin u) ^ (p - 1)
  rw [Real.mul_rpow (by norm_num) hc.le, Real.mul_rpow (by norm_num) hs.le]
  nlinarith [mul_pos (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (p - 1))
    (sub_pos.2 hcmp)]

/-- Equal amplitudes on the two branches have total angle strictly below
`pi`. Thus their associated geometric principal angle is acute. -/
theorem balanced_roots_sum_lt_pi (p a b : ℝ) (hp1 : 1 < p) (hp2 : p < 2)
    (ha : a ∈ Ioo 0 (criticalAngle p)) (hb : b ∈ Ioo (criticalAngle p) Real.pi)
    (hab : phaseAmplitude p a = phaseAmplitude p b) : a + b < Real.pi := by
  have hcrit := criticalAngle_mem p hp1 hp2
  have hcomp := phaseAmplitude_pi_sub_lt p a hp2 ha.1 (ha.2.trans hcrit.2)
  by_contra hsum
  have hπa : Real.pi - a ∈ Icc (criticalAngle p) Real.pi :=
    ⟨by linarith [ha.2, hcrit.2], by linarith [ha.1]⟩
  have hle := (phaseAmplitude_strictAntiOn p hp1 hp2).antitoneOn hπa
    ⟨hb.1.le, hb.2.le⟩ (by linarith)
  rw [← hab] at hle
  exact (not_lt_of_ge hle) hcomp

/-- Every positive interior stationary phase is the global scalar
minimizer, and its principal angle lies strictly above the transition. -/
theorem stationary_phase_isMinOn (p theta delta : ℝ) (hp1 : 1 < p) (hp2 : p < 2)
    (h0 : 0 < theta) (hπ : theta < Real.pi / 2) (hδ : delta ∈ Ioo 0 theta)
    (hstat : deriv (phasePower p theta) delta = 0) :
    IsMinOn (phasePower p theta) (Icc 0 theta) delta ∧ criticalAngle p < theta := by
  have hcrit : p * Real.cos theta < 2 - p := by
    by_contra h
    have hpos := phasePower_deriv_pos_of_subcritical p theta delta (by linarith) hp2 h0 hπ
      (le_of_not_gt h) hδ.1 hδ.2
    rw [hstat] at hpos
    exact (lt_irrefl 0) hpos
  have hcθ : criticalAngle p < theta := by
    by_contra h
    have hle := (critical_inequality_iff p theta hp1 hp2
      ⟨h0.le, by linarith [Real.pi_pos]⟩).2 (le_of_not_gt h)
    exact (not_lt_of_ge hle) hcrit
  obtain ⟨eta, hη, hstatη, hmin⟩ :=
    exists_unique_phase_minimizer_of_supercritical p theta hp1 hp2 h0 hπ hcrit
  have heq := phasePower_stationary_unique p theta (by linarith) hp2 h0 hπ hδ hη hstat hstatη
  subst eta
  exact ⟨fun x hx => (hmin x hx).1, hcθ⟩

/-- A pair of distinct balanced amplitude roots determines an acute
supercritical principal angle and attains exactly its scalar minimum. -/
theorem balanced_roots_phase_minimum (p a b : ℝ) (hp1 : 1 < p) (hp2 : p < 2)
    (ha : a ∈ Ioo 0 (criticalAngle p)) (hb : b ∈ Ioo (criticalAngle p) Real.pi)
    (hab : phaseAmplitude p a = phaseAmplitude p b) :
    criticalAngle p < (a + b) / 2 ∧ (a + b) / 2 < Real.pi / 2 ∧
      phaseMinimum p ((a + b) / 2) = phaseChord a ^ p + phaseChord b ^ p := by
  let theta := (a + b) / 2
  let delta := (b - a) / 2
  have hsum := balanced_roots_sum_lt_pi p a b hp1 hp2 ha hb hab
  have hcrit := criticalAngle_mem p hp1 hp2
  have hθ0 : 0 < theta := by dsimp [theta]; linarith [ha.1, hb.1, hcrit.1]
  have hθπ : theta < Real.pi / 2 := by dsimp [theta]; linarith
  have hδ : delta ∈ Ioo 0 theta := by dsimp [delta, theta]; constructor <;> linarith [ha.1, ha.2, hb.1]
  have hplus : theta + delta = b := by dsimp [theta, delta]; ring
  have hminus : theta - delta = a := by dsimp [theta, delta]; ring
  have hstat : deriv (phasePower p theta) delta = 0 := by
    apply (phasePower_stationary_iff p theta delta (by linarith)
      (by rw [hplus]; exact chord_pos_on_angle ⟨hcrit.1.trans hb.1, hb.2⟩)
      (by rw [hminus]; exact chord_pos_on_angle ⟨ha.1, by linarith [ha.2, hcrit.2, Real.pi_pos]⟩)).2
    rw [hplus, hminus]
    exact hab.symm
  obtain ⟨hmin, hc⟩ := stationary_phase_isMinOn p theta delta hp1 hp2 hθ0 hθπ hδ hstat
  refine ⟨hc, hθπ, ?_⟩
  rw [phaseMinimum_eq_of_isMinOn p theta delta ⟨hδ.1.le, hδ.2.le⟩ hmin,
    phasePower, hplus, hminus, add_comm]

/-- Every acute supercritical angle comes from a balanced pair with one
phase on each amplitude branch. -/
theorem exists_balanced_roots_of_supercritical_angle (p theta : ℝ)
    (hp1 : 1 < p) (hp2 : p < 2) (hcrit : criticalAngle p < theta)
    (hπ : theta < Real.pi / 2) :
    ∃ a ∈ Ioo 0 (criticalAngle p), ∃ b ∈ Ioo (criticalAngle p) Real.pi,
      theta = (a + b) / 2 ∧ phaseAmplitude p a = phaseAmplitude p b := by
  have hc := criticalAngle_mem p hp1 hp2
  have h0 : 0 < theta := hc.1.trans hcrit
  have hcrit' : p * Real.cos theta < 2 - p := by
    by_contra h
    have hle := (critical_inequality_iff p theta hp1 hp2
      ⟨h0.le, by linarith [Real.pi_pos]⟩).1 (le_of_not_gt h)
    exact (not_le_of_gt hcrit) hle
  obtain ⟨delta, hδ, hstat, _⟩ :=
    exists_unique_phase_minimizer_of_supercritical p theta hp1 hp2 h0 hπ hcrit'
  have ha0 : 0 < theta - delta := by linarith [hδ.2]
  have hbπ : theta + delta < Real.pi := by linarith [hδ.2]
  have hbal := (phasePower_stationary_iff p theta delta (by linarith)
    (phaseChord_pos (by linarith [hδ.1]) hbπ)
    (phaseChord_pos ha0 (by linarith [hδ.1, Real.pi_pos]))).1 hstat
  have hac : theta - delta < criticalAngle p := by
    by_contra h
    have hlt := phaseAmplitude_strictAntiOn p hp1 hp2
      ⟨le_of_not_gt h, by linarith [hδ.1, Real.pi_pos]⟩
      ⟨by linarith [hδ.1], hbπ.le⟩ (by linarith [hδ.1])
    exact hlt.ne hbal
  have hcb : criticalAngle p < theta + delta := by
    by_contra h
    have hlt := phaseAmplitude_strictMonoOn p hp1 hp2
      ⟨ha0.le, by linarith [hδ.1]⟩
      ⟨by linarith [hδ.1], le_of_not_gt h⟩ (by linarith [hδ.1])
    exact hlt.ne hbal.symm
  refine ⟨theta - delta, ⟨ha0, hac⟩, theta + delta, ⟨hcb, hbπ⟩, ?_, hbal.symm⟩
  ring

end
end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

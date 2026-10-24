/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.SchattenPhaseMinimum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# The critical angle and the two amplitude branches

For `1 < p < 2`, the auxiliary amplitude increases up to the critical angle
`arccos ((2-p)/p)` and decreases afterward. These branches organize the
stationary spectra in the unrestricted Schatten optimization problem.
-/

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open Set

noncomputable section

/-- The sharp angle at which canonical scalar-phase optimality changes. -/
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

end
end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

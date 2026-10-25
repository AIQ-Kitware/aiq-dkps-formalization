/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedGradientSpectrum
public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedPhaseCurvature
public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedCriticalAngle
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# The two angular branches of a Charbonnier gradient level

Every positive level below the sharp maximum has exactly one phase on
each side of the critical angle. The classification covers the whole
principal-phase interval, and signed maximal levels have a single phase.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

open Set

/-- The critical phase attains the sharp positive gradient maximum. -/
theorem smoothedPhaseDerivative_critical (tau : ℝ) (htau : 0 < tau) :
    smoothedPhaseDerivative tau
      (Complex.exp ((smoothedCriticalAngle tau : ℂ) * Complex.I)) =
        (smoothingRadius tau)⁻¹ := by
  have hc := smoothedCriticalAngle_mem tau htau
  have hpos : 0 < smoothedPhaseDerivative tau
      (Complex.exp ((smoothedCriticalAngle tau : ℂ) * Complex.I)) := by
    rw [smoothedPhaseDerivative_exp]
    apply div_pos (Real.sin_pos_of_pos_of_lt_pi hc.1 (by linarith [hc.2, Real.pi_pos]))
    apply Real.sqrt_pos.mpr
    nlinarith [Real.cos_le_one (smoothedCriticalAngle tau), sq_pos_of_pos htau]
  have h := (abs_smoothedPhaseDerivative_eq_iff tau htau _
    (Complex.norm_exp_ofReal_mul_I _)).mpr (by
      rw [Complex.exp_ofReal_mul_I_re, cos_smoothedCriticalAngle tau htau])
  rwa [abs_of_pos hpos] at h

private theorem continuous_gradient_phase (tau : ℝ) (htau : 0 < tau) :
    Continuous (fun t : ℝ => smoothedPhaseDerivative tau (Complex.exp ((t : ℂ) * Complex.I))) :=
  continuous_iff_continuousAt.mpr fun t =>
    (hasDerivAt_smoothedPhaseDerivative_exp tau t htau).continuousAt

/-- The small-angle gradient branch is strictly increasing through its maximum. -/
theorem smoothedPhaseDerivative_strictMonoOn (tau : ℝ) (htau : 0 < tau) :
    StrictMonoOn (fun t : ℝ => smoothedPhaseDerivative tau (Complex.exp ((t : ℂ) * Complex.I)))
      (Icc 0 (smoothedCriticalAngle tau)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (continuous_gradient_phase tau htau).continuousOn
  intro t ht
  rw [interior_Icc] at ht
  rw [(hasDerivAt_smoothedPhaseDerivative_exp tau t htau).deriv,
    smoothedPhaseCurvature_pos_iff tau t htau, ← cos_smoothedCriticalAngle tau htau]
  have hc := smoothedCriticalAngle_mem tau htau
  exact Real.strictAntiOn_cos ⟨ht.1.le, by linarith [hc.2, ht.2, Real.pi_pos]⟩
    ⟨hc.1.le, by linarith [hc.2, Real.pi_pos]⟩ ht.2

/-- The large-angle gradient branch decreases strictly to zero at `pi`. -/
theorem smoothedPhaseDerivative_strictAntiOn (tau : ℝ) (htau : 0 < tau) :
    StrictAntiOn (fun t : ℝ => smoothedPhaseDerivative tau (Complex.exp ((t : ℂ) * Complex.I)))
      (Icc (smoothedCriticalAngle tau) Real.pi) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (continuous_gradient_phase tau htau).continuousOn
  intro t ht
  rw [interior_Icc] at ht
  rw [(hasDerivAt_smoothedPhaseDerivative_exp tau t htau).deriv,
    smoothedPhaseCurvature_neg_iff tau t htau, ← cos_smoothedCriticalAngle tau htau]
  have hc := smoothedCriticalAngle_mem tau htau
  exact Real.strictAntiOn_cos ⟨hc.1.le, by linarith [hc.2, Real.pi_pos]⟩
    ⟨by linarith [hc.1, ht.1], ht.2.le⟩ ht.1

/-- Two roots with uniqueness on each of the two open phase branches. -/
theorem smoothedPhaseDerivative_two_roots (tau g : ℝ) (htau : 0 < tau)
    (hg0 : 0 < g) (hgm : g < (smoothingRadius tau)⁻¹) :
    (∃! a, a ∈ Ioo 0 (smoothedCriticalAngle tau) ∧
      smoothedPhaseDerivative tau (Complex.exp ((a : ℂ) * Complex.I)) = g) ∧
    (∃! b, b ∈ Ioo (smoothedCriticalAngle tau) Real.pi ∧
      smoothedPhaseDerivative tau (Complex.exp ((b : ℂ) * Complex.I)) = g) := by
  let f := fun t : ℝ => smoothedPhaseDerivative tau (Complex.exp ((t : ℂ) * Complex.I))
  have hc := smoothedCriticalAngle_mem tau htau
  have hf0 : f 0 = 0 := by simp [f, smoothedPhaseDerivative_exp]
  have hfpi : f Real.pi = 0 := by simp [f, smoothedPhaseDerivative_exp]
  have hfc : f (smoothedCriticalAngle tau) = (smoothingRadius tau)⁻¹ :=
    smoothedPhaseDerivative_critical tau htau
  obtain ⟨a, ha, hag⟩ := intermediate_value_Ioo hc.1.le
    (continuous_gradient_phase tau htau).continuousOn
    (show g ∈ Ioo (f 0) (f (smoothedCriticalAngle tau)) by rw [hf0, hfc]; exact ⟨hg0, hgm⟩)
  obtain ⟨b, hb, hbg⟩ := intermediate_value_Ioo'
    (by linarith [hc.2, Real.pi_pos] : smoothedCriticalAngle tau ≤ Real.pi)
    (continuous_gradient_phase tau htau).continuousOn
    (show g ∈ Ioo (f Real.pi) (f (smoothedCriticalAngle tau)) by
      rw [hfpi, hfc]; exact ⟨hg0, hgm⟩)
  constructor
  · refine ⟨a, ⟨ha, hag⟩, ?_⟩
    intro t ht
    exact (smoothedPhaseDerivative_strictMonoOn tau htau).injOn
      ⟨ht.1.1.le, ht.1.2.le⟩ ⟨ha.1.le, ha.2.le⟩ (ht.2.trans hag.symm)
  · refine ⟨b, ⟨hb, hbg⟩, ?_⟩
    intro t ht
    exact (smoothedPhaseDerivative_strictAntiOn tau htau).injOn
      ⟨ht.1.1.le, ht.1.2.le⟩ ⟨hb.1.le, hb.2.le⟩ (ht.2.trans hbg.symm)

private theorem principal_phase_pos_of_gradient_pos (tau t : ℝ) (htau : 0 < tau)
    (ht : |t| ≤ Real.pi)
    (hg : 0 < smoothedPhaseDerivative tau (Complex.exp ((t : ℂ) * Complex.I))) :
    t ∈ Ioo 0 Real.pi := by
  rw [smoothedPhaseDerivative_exp] at hg
  have hrad : 0 < tau ^ 2 + 2 - 2 * Real.cos t := by
    nlinarith [Real.cos_le_one t, sq_pos_of_pos htau]
  have hsin : 0 < Real.sin t := (div_pos_iff_of_pos_right (Real.sqrt_pos.mpr hrad)).mp hg
  have ht0 : 0 < t := by
    by_contra h
    exact (not_lt_of_ge (Real.sin_nonpos_of_nonpos_of_neg_pi_le (le_of_not_gt h)
      (by linarith [neg_abs_le t]))) hsin
  refine ⟨ht0, lt_of_le_of_ne ((le_abs_self t).trans ht) ?_⟩
  intro heq
  rw [heq, Real.sin_pi] at hsin
  exact lt_irrefl 0 hsin

/-- The two positive roots exhaust the complete principal-phase interval. -/
theorem smoothedPhaseDerivative_level_set (tau g : ℝ) (htau : 0 < tau)
    (hg0 : 0 < g) (hgm : g < (smoothingRadius tau)⁻¹) :
    ∃ a ∈ Ioo 0 (smoothedCriticalAngle tau), ∃ b ∈ Ioo (smoothedCriticalAngle tau) Real.pi,
      ∀ t : ℝ, |t| ≤ Real.pi →
        (smoothedPhaseDerivative tau (Complex.exp ((t : ℂ) * Complex.I)) = g ↔
          t = a ∨ t = b) := by
  obtain ⟨⟨a, ha, huniq_a⟩, ⟨b, hb, huniq_b⟩⟩ :=
    smoothedPhaseDerivative_two_roots tau g htau hg0 hgm
  refine ⟨a, ha.1, b, hb.1, ?_⟩
  intro t ht
  constructor
  · intro hlevel
    have hpos := principal_phase_pos_of_gradient_pos tau t htau ht (hlevel ▸ hg0)
    rcases lt_trichotomy t (smoothedCriticalAngle tau) with hlt | heq | hgt
    · exact Or.inl (huniq_a t ⟨⟨hpos.1, hlt⟩, hlevel⟩)
    · rw [heq, smoothedPhaseDerivative_critical tau htau] at hlevel
      exact False.elim (hgm.ne hlevel.symm)
    · exact Or.inr (huniq_b t ⟨⟨hgt, hpos.2⟩, hlevel⟩)
  · rintro (rfl | rfl)
    · exact ha.2
    · exact hb.2

/-- The negative level has the same two roots with opposite signs. -/
theorem smoothedPhaseDerivative_signed_level_sets (tau g : ℝ) (htau : 0 < tau)
    (hg0 : 0 < g) (hgm : g < (smoothingRadius tau)⁻¹) :
    ∃ a ∈ Ioo 0 (smoothedCriticalAngle tau), ∃ b ∈ Ioo (smoothedCriticalAngle tau) Real.pi,
      (∀ t : ℝ, |t| ≤ Real.pi →
        (smoothedPhaseDerivative tau (Complex.exp ((t : ℂ) * Complex.I)) = g ↔
          t = a ∨ t = b)) ∧
      (∀ t : ℝ, |t| ≤ Real.pi →
        (smoothedPhaseDerivative tau (Complex.exp ((t : ℂ) * Complex.I)) = -g ↔
          t = -a ∨ t = -b)) := by
  obtain ⟨a, ha, b, hb, hlevel⟩ := smoothedPhaseDerivative_level_set tau g htau hg0 hgm
  refine ⟨a, ha, b, hb, hlevel, ?_⟩
  intro t ht
  calc
    _ ↔ smoothedPhaseDerivative tau (Complex.exp (((-t : ℝ) : ℂ) * Complex.I)) = g := by
      rw [smoothedPhaseDerivative_exp_neg, neg_eq_iff_eq_neg]
    _ ↔ -t = a ∨ -t = b := hlevel (-t) (by simpa only [abs_neg] using ht)
    _ ↔ t = -a ∨ t = -b := by simp only [neg_eq_iff_eq_neg]

/-- The maximal positive gradient has a single principal phase. -/
theorem smoothedPhaseDerivative_max_level_set (tau t : ℝ) (htau : 0 < tau)
    (ht : |t| ≤ Real.pi) :
    smoothedPhaseDerivative tau (Complex.exp ((t : ℂ) * Complex.I)) =
      (smoothingRadius tau)⁻¹ ↔ t = smoothedCriticalAngle tau := by
  constructor
  · intro hlevel
    have hg : 0 < (smoothingRadius tau)⁻¹ :=
      inv_pos.mpr (zero_lt_one.trans (one_lt_smoothingRadius tau htau))
    have hpos := principal_phase_pos_of_gradient_pos tau t htau ht (hlevel ▸ hg)
    have hc := smoothedCriticalAngle_mem tau htau
    have heq : |smoothedPhaseDerivative tau (Complex.exp ((t : ℂ) * Complex.I))| =
        (smoothingRadius tau)⁻¹ := by rw [hlevel, abs_of_pos hg]
    have hre := (abs_smoothedPhaseDerivative_eq_iff tau htau _
      (Complex.norm_exp_ofReal_mul_I t)).mp heq
    rw [Complex.exp_ofReal_mul_I_re, ← cos_smoothedCriticalAngle tau htau] at hre
    exact Real.strictAntiOn_cos.injOn ⟨hpos.1.le, hpos.2.le⟩
      ⟨hc.1.le, by linarith [hc.2, Real.pi_pos]⟩ hre
  · rintro rfl
    exact smoothedPhaseDerivative_critical tau htau

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

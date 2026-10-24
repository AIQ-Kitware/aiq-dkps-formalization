/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.SchattenPhaseCriticalAngle
import DavisKahan.FiniteDimensional.DirectRotation.SchattenStationarity

/-!
# The two spectral roots of the Schatten unitary gradient

The argument-free unitary gradient symbol agrees with `p * phaseAmplitude`
on positive principal phases. Thus its positive spectral levels have two
branches, separated by the scalar critical angle. This connects the compiled
stationarity identity to the scalar optimization calculus.
-/

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open Set

noncomputable section

/-- On positive principal phases, the matrix-gradient symbol is exactly
the amplitude already used in scalar phase optimization. -/
theorem schattenPhaseDerivative_exp_eq_amplitude (p t : ℝ)
    (ht : t ∈ Ioo 0 Real.pi) :
    schattenPhaseDerivative p (Complex.exp ((t : ℂ) * Complex.I)) =
      p * phaseAmplitude p t := by
  have hs : 0 < Real.sin (t / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1]) (by linarith [ht.2, Real.pi_pos])
  have hc := phaseChord_pos ht.1 ht.2
  have hpow : phaseChord t ^ (p - 2) * phaseChord t = phaseChord t ^ (p - 1) := by
    rw [← Real.rpow_add_one hc.ne']
    congr 1
    ring
  rw [schattenPhaseDerivative_exp, abs_of_pos hs]
  change p * phaseChord t ^ (p - 2) * Real.sin t = _
  have hsin : Real.sin t = phaseChord t * Real.cos (t / 2) := by
    calc
      Real.sin t = Real.sin (2 * (t / 2)) := by congr 1; ring
      _ = 2 * Real.sin (t / 2) * Real.cos (t / 2) := Real.sin_two_mul _
      _ = _ := rfl
  rw [hsin, phaseAmplitude]
  calc
    _ = p * Real.cos (t / 2) * (phaseChord t ^ (p - 2) * phaseChord t) := by ring
    _ = _ := by rw [hpow]; ring

/-- A positive gradient level can only come from a positive interior
principal phase. The endpoint phases `0` and `pi` have zero symbol. -/
theorem principal_phase_pos_of_schattenPhaseDerivative_pos
    (p t : ℝ) (hp : 0 < p) (ht : |t| ≤ Real.pi)
    (hg : 0 < schattenPhaseDerivative p (Complex.exp ((t : ℂ) * Complex.I))) :
    t ∈ Ioo 0 Real.pi := by
  rw [schattenPhaseDerivative_exp] at hg
  have hcoef : 0 ≤ p * (2 * |Real.sin (t / 2)|) ^ (p - 2) :=
    mul_nonneg hp.le (Real.rpow_nonneg (by positivity) _)
  have hsin : 0 < Real.sin t := by
    by_contra h
    exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hcoef (le_of_not_gt h))) hg
  have ht0 : 0 < t := by
    by_contra h
    have hs := Real.sin_nonpos_of_nonpos_of_neg_pi_le (le_of_not_gt h)
      (by linarith [neg_abs_le t])
    exact (not_lt_of_ge hs) hsin
  refine ⟨ht0, lt_of_le_of_ne (le_trans (le_abs_self t) ht) ?_⟩
  intro heq
  rw [heq, Real.sin_pi] at hsin
  exact lt_irrefl 0 hsin

/-- Every positive gradient level below its maximum has exactly one
positive phase on each side of the critical angle. -/
theorem schattenPhaseDerivative_two_roots (p g : ℝ)
    (hp1 : 1 < p) (hp2 : p < 2) (hg0 : 0 < g)
    (hgm : g < p * phaseAmplitude p (criticalAngle p)) :
    (∃! a, a ∈ Ioo 0 (criticalAngle p) ∧
      schattenPhaseDerivative p (Complex.exp ((a : ℂ) * Complex.I)) = g) ∧
    (∃! b, b ∈ Ioo (criticalAngle p) Real.pi ∧
      schattenPhaseDerivative p (Complex.exp ((b : ℂ) * Complex.I)) = g) := by
  have hp0 : 0 < p := by linarith
  have hcrit := criticalAngle_mem p hp1 hp2
  obtain ⟨ha, hb⟩ := phaseAmplitude_two_roots p (g / p) hp1 hp2
    (div_pos hg0 hp0) ((div_lt_iff₀ hp0).2 (by simpa only [mul_comm] using hgm))
  have heq (t : ℝ) (ht : t ∈ Ioo 0 Real.pi) :
      schattenPhaseDerivative p (Complex.exp ((t : ℂ) * Complex.I)) = g ↔
        phaseAmplitude p t = g / p := by
    rw [schattenPhaseDerivative_exp_eq_amplitude p t ht,
      eq_div_iff hp0.ne', mul_comm]
  constructor
  · obtain ⟨a, ha, huniq⟩ := ha
    refine ⟨a, ⟨ha.1, (heq a ⟨ha.1.1, by linarith [ha.1.2, hcrit.2, Real.pi_pos]⟩).2 ha.2⟩, ?_⟩
    intro t ht
    exact huniq t ⟨ht.1, (heq t ⟨ht.1.1, by linarith [ht.1.2, hcrit.2, Real.pi_pos]⟩).1 ht.2⟩
  · obtain ⟨b, hb, huniq⟩ := hb
    refine ⟨b, ⟨hb.1, (heq b ⟨by linarith [hb.1.1, hcrit.1], hb.1.2⟩).2 hb.2⟩, ?_⟩
    intro t ht
    exact huniq t ⟨ht.1, (heq t ⟨by linarith [ht.1.1, hcrit.1], ht.1.2⟩).1 ht.2⟩

/-- The two branches exhaust a positive gradient level in the full
principal-phase range, including negative phases and the endpoints. -/
theorem schattenPhaseDerivative_level_set (p g : ℝ)
    (hp1 : 1 < p) (hp2 : p < 2) (hg0 : 0 < g)
    (hgm : g < p * phaseAmplitude p (criticalAngle p)) :
    ∃ a ∈ Ioo 0 (criticalAngle p), ∃ b ∈ Ioo (criticalAngle p) Real.pi,
      ∀ t : ℝ, |t| ≤ Real.pi →
        (schattenPhaseDerivative p (Complex.exp ((t : ℂ) * Complex.I)) = g ↔
          t = a ∨ t = b) := by
  obtain ⟨⟨a, ha, huniq_a⟩, ⟨b, hb, huniq_b⟩⟩ :=
    schattenPhaseDerivative_two_roots p g hp1 hp2 hg0 hgm
  refine ⟨a, ha.1, b, hb.1, ?_⟩
  intro t ht
  constructor
  · intro hlevel
    have hpos := principal_phase_pos_of_schattenPhaseDerivative_pos p t
      (by linarith : 0 < p) ht (by rw [hlevel]; exact hg0)
    rcases lt_trichotomy t (criticalAngle p) with hlt | heq | hgt
    · exact Or.inl (huniq_a t ⟨⟨hpos.1, hlt⟩, hlevel⟩)
    · have hcrit := criticalAngle_mem p hp1 hp2
      rw [heq, schattenPhaseDerivative_exp_eq_amplitude p (criticalAngle p)
        ⟨hcrit.1, by linarith [hcrit.2, Real.pi_pos]⟩] at hlevel
      exact False.elim (hgm.ne hlevel.symm)
    · exact Or.inr (huniq_b t ⟨⟨hgt, hpos.2⟩, hlevel⟩)
  · rintro (rfl | rfl)
    · exact ha.2
    · exact hb.2

/-- The amplitude reaches its maximum precisely at the critical angle. -/
theorem phaseAmplitude_le_criticalAngle (p t : ℝ) (hp1 : 1 < p) (hp2 : p < 2)
    (ht : t ∈ Icc 0 Real.pi) :
    phaseAmplitude p t ≤ phaseAmplitude p (criticalAngle p) := by
  have hcrit := criticalAngle_mem p hp1 hp2
  rcases le_total t (criticalAngle p) with hle | hle
  · exact (phaseAmplitude_strictMonoOn p hp1 hp2).monotoneOn
      ⟨ht.1, hle⟩ ⟨hcrit.1.le, le_rfl⟩ hle
  · exact (phaseAmplitude_strictAntiOn p hp1 hp2).antitoneOn
      ⟨le_rfl, by linarith [hcrit.2, Real.pi_pos]⟩ ⟨hle, ht.2⟩ hle

/-- On a positive submaximal gradient eigenspace, all principal eigenphases
of the unitary lie in the same pair of scalar roots. The unitary is arbitrary;
the stationarity identity will subsequently pair its opposite gradient levels. -/
theorem gradient_eigenphases_have_two_roots
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [CompleteSpace E]
    (p g : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (hg0 : 0 < g)
    (hgm : g < p * phaseAmplitude p (criticalAngle p))
    (U : E →L[ℂ] E) [IsStarNormal U] :
    ∃ a ∈ Ioo 0 (criticalAngle p), ∃ b ∈ Ioo (criticalAngle p) Real.pi,
      ∀ (x : E) (t : ℝ), x ≠ 0 → |t| ≤ Real.pi →
        U x = Complex.exp ((t : ℂ) * Complex.I) • x →
        schattenUnitaryGradient p U x = (g : ℂ) • x → t = a ∨ t = b := by
  obtain ⟨a, ha, b, hb, hlevel⟩ := schattenPhaseDerivative_level_set p g hp1 hp2 hg0 hgm
  refine ⟨a, ha, b, hb, ?_⟩
  intro x t hx ht hU hG
  have hcalc := schattenUnitaryGradient_apply_of_apply_eq_smul p U x _ hU
  rw [hG] at hcalc
  have hscalar := smul_left_injective ℂ hx hcalc
  have hreal : schattenPhaseDerivative p (Complex.exp ((t : ℂ) * Complex.I)) = g := by
    exact_mod_cast hscalar.symm
  exact (hlevel t ht).1 hreal

end

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SchattenRealAngleCosts

/-!
# Exact one-angle real versus complex equality and strict field gap

For a real rank-one problem in dimension two, the exact optimum power is
`realSingleSchattenCost p theta`. For its complex one-angle problem the
corresponding optimum is `phaseMinimum p theta`. The real value is strictly
larger precisely at the supercritical acute angles. Both endpoints and the
critical angle are included in the equality classification.

The comparison uses actual attained optimum values, rather than a cost
comparison of a prescribed pair of competitors. It is a one-angle result;
different real principal planes can interact in higher rank.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.RealTransport

open SchattenPhaseTransition

private theorem phaseMinimum_le_canonical (p theta : ℝ) (hp : 1 ≤ p) (htheta : 0 ≤ theta) :
    phaseMinimum p theta ≤ 2 * phaseChord theta^p := by
  simpa only [phasePower, add_zero, sub_zero, two_mul] using
    phaseMinimum_le_phasePower p theta hp htheta ⟨le_rfl, htheta⟩

/-- The exact complex one-angle minimum never exceeds the real minimum. -/
theorem phaseMinimum_le_realSingleSchattenCost (p theta : ℝ)
    (hp : 1 ≤ p) (htheta : theta ∈ Set.Icc 0 (Real.pi/2)) :
    phaseMinimum p theta ≤ realSingleSchattenCost p theta := by
  exact le_min (phaseMinimum_le_canonical p theta hp htheta.1)
    (phaseMinimum_le_two_rpow p theta hp htheta)

private theorem phaseMinimum_lt_two_rpow_of_acute (p theta : ℝ)
    (hp : 1 ≤ p) (htheta : 0 ≤ theta) (hacute : theta < Real.pi/2) :
    phaseMinimum p theta < (2 : ℝ)^p := by
  have hsin : Real.sin theta < 1 := by
    simpa only [Real.sin_pi_div_two] using Real.sin_lt_sin_of_lt_of_le_pi_div_two
      (show -(Real.pi/2) ≤ theta by linarith [Real.pi_pos]) le_rfl hacute
  have hsin0 : 0 ≤ Real.sin theta :=
    Real.sin_nonneg_of_nonneg_of_le_pi htheta (by linarith [Real.pi_pos])
  exact (phaseMinimum_le_endpoint p theta hp htheta).trans_lt
    (Real.rpow_lt_rpow (by positivity) (by linarith) (by linarith))

/-- At acute positive angles, the field gap starts at the complex
phase transition and remains strictly positive up to the right endpoint. -/
theorem phaseMinimum_lt_realSingleSchattenCost_iff_of_acute (p theta : ℝ)
    (hp1 : 1 < p) (hp2 : p < 2) (htheta : 0 < theta) (hacute : theta < Real.pi/2) :
    phaseMinimum p theta < realSingleSchattenCost p theta ↔ criticalAngle p < theta := by
  constructor
  · intro hgap
    by_contra hnot
    have hcan := (canonical_phase_isMinOn_iff_le_criticalAngle p theta hp1 hp2 htheta hacute).mpr
      (le_of_not_gt hnot)
    have hvalue := phaseMinimum_eq_of_isMinOn p theta 0 ⟨le_rfl, htheta.le⟩ hcan
    have heq : phaseMinimum p theta = 2 * phaseChord theta^p := by
      simpa only [phasePower, add_zero, sub_zero, two_mul] using hvalue
    exact (not_lt_of_ge (min_le_left _ _)) (heq ▸ hgap)
  · intro hcrit
    have hneq : phaseMinimum p theta ≠ 2 * phaseChord theta^p := by
      intro heq
      have hvalue : phasePower p theta 0 = phaseMinimum p theta := by
        simpa only [phasePower, add_zero, sub_zero, two_mul] using heq.symm
      have hzero := (phasePower_eq_phaseMinimum_iff_eq_optimalPhase
        p theta hp1 hp2 htheta hacute ⟨le_rfl, htheta.le⟩).mp hvalue
      have hle := (optimalPhase_eq_zero_iff_le_criticalAngle p theta hp1 hp2 htheta hacute).mp
        hzero.symm
      exact (not_le_of_gt hcrit) hle
    exact lt_min ((lt_or_eq_of_le (phaseMinimum_le_canonical p theta hp1.le htheta.le)).resolve_right hneq)
      (phaseMinimum_lt_two_rpow_of_acute p theta hp1.le htheta.le hacute)

/-- At the right angle both fields have the reflection value, despite
the strict gap at all acute angles above the transition. -/
theorem realSingleSchattenCost_right_angle (p : ℝ) (hp1 : 1 ≤ p) (hp2 : p ≤ 2) :
    realSingleSchattenCost p (Real.pi/2) = (2 : ℝ)^p := by
  apply min_eq_right
  rw [← phaseMinimum_right_angle p hp1 hp2]
  exact phaseMinimum_le_canonical p (Real.pi/2) hp1 (by linarith [Real.pi_pos])

/-- Complete one-angle strict-gap classification, including zero, the
critical angle, and the right-angle endpoint. -/
theorem phaseMinimum_lt_realSingleSchattenCost_iff (p theta : ℝ)
    (hp1 : 1 < p) (hp2 : p < 2) (htheta : theta ∈ Set.Icc 0 (Real.pi/2)) :
    phaseMinimum p theta < realSingleSchattenCost p theta ↔
      criticalAngle p < theta ∧ theta < Real.pi/2 := by
  rcases eq_or_lt_of_le htheta.1 with hzero | hpos
  · subst theta
    simp [phaseMinimum_zero_angle p hp1.le, realSingleSchattenCost_zero p (by linarith),
      not_lt_of_ge (criticalAngle_mem p hp1 hp2).1.le]
  · rcases lt_or_eq_of_le htheta.2 with hacute | rfl
    · rw [phaseMinimum_lt_realSingleSchattenCost_iff_of_acute p theta hp1 hp2 hpos hacute]
      exact (and_iff_left hacute).symm
    · rw [realSingleSchattenCost_right_angle p hp1.le hp2.le,
        phaseMinimum_right_angle p hp1.le hp2.le]
      simp

/-- Complete one-angle equality classification for the exact optimum
powers. Repeated-angle interactions in higher rank require a separate theorem. -/
theorem phaseMinimum_eq_realSingleSchattenCost_iff (p theta : ℝ)
    (hp1 : 1 < p) (hp2 : p < 2) (htheta : theta ∈ Set.Icc 0 (Real.pi/2)) :
    phaseMinimum p theta = realSingleSchattenCost p theta ↔
      theta ≤ criticalAngle p ∨ theta = Real.pi/2 := by
  have hle := phaseMinimum_le_realSingleSchattenCost p theta hp1.le htheta
  have hstrict := phaseMinimum_lt_realSingleSchattenCost_iff p theta hp1 hp2 htheta
  constructor
  · intro heq
    by_cases hcrit : theta ≤ criticalAngle p
    · exact Or.inl hcrit
    · exact Or.inr (le_antisymm htheta.2 (le_of_not_gt (fun hacute =>
        (ne_of_lt (hstrict.mpr ⟨lt_of_not_ge hcrit, hacute⟩)) heq)))
  · intro hboundary
    apply le_antisymm hle
    apply le_of_not_gt
    intro hgap
    obtain ⟨hcrit, hacute⟩ := hstrict.mp hgap
    rcases hboundary with hsub | hright
    · exact (not_le_of_gt hcrit) hsub
    · exact (ne_of_lt hacute) hright

end TauCeti.DavisKahan.FiniteDimensional.RealTransport

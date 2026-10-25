/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6, GPT-6.1 Sol
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SchattenPhaseCriticalAngle

/-!
# The named optimal Schatten phase and every minimizing phase pair

The attaining phase exists on every nonnegative scalar interval for
`p≥1`; outside those hypotheses the named function is zero. In the acute
`1<p<2` regime its value is unique, including the critical angle.
Every nonnegative phase pair attaining the scalar minimum consequently
has precisely one of the two signed optimal-phase forms.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open Set

/-- A named attaining nonnegative phase. The default outside `p≥1,theta≥0`
is zero. On acute angles for `1<p<2` scalar uniqueness makes the choice
independent of the existence proof. -/
@[expose]
def optimalPhase (p theta : ℝ) : ℝ :=
  if h : 1 ≤ p ∧ 0 ≤ theta then
    Classical.choose (exists_attains_phaseMinimum p theta h.1 h.2)
  else 0

/-- Membership, attainment and minimality of the named scalar phase. -/
theorem optimalPhase_spec (p theta : ℝ) (hp : 1 ≤ p) (hθ : 0 ≤ theta) :
    optimalPhase p theta ∈ Icc 0 theta ∧
      phasePower p theta (optimalPhase p theta) = phaseMinimum p theta ∧
      IsMinOn (phasePower p theta) (Icc 0 theta) (optimalPhase p theta) := by
  rw [optimalPhase, dite_eq_left ⟨hp, hθ⟩]
  have h := Classical.choose_spec (exists_attains_phaseMinimum p theta hp hθ)
  exact ⟨h.1, h.2.1.symm, h.2.2⟩

/-- The zero-angle phase is zero for every Schatten exponent. -/
@[simp] theorem optimalPhase_zero (p : ℝ) (hp : 1 ≤ p) : optimalPhase p 0 = 0 :=
  le_antisymm (optimalPhase_spec p 0 hp le_rfl).1.2 (optimalPhase_spec p 0 hp le_rfl).1.1

/-- At exponent one the scalar cost is a cosine, on all real inputs. -/
theorem phasePower_one (theta delta : ℝ) :
    phasePower 1 theta delta = 4 * Real.sin (theta/2) * Real.cos (delta/2) := by
  simp only [phasePower, Real.rpow_one, phaseChord]
  rw [← mul_add, Real.sin_add_sin,
    show ((theta+delta)/2+(theta-delta)/2)/2 = theta/2 by ring,
    show ((theta+delta)/2-(theta-delta)/2)/2 = delta/2 by ring]
  ring

/-- The nuclear scalar phase is the geometric endpoint, including zero
and right angles. Strict cosine monotonicity gives uniqueness away from zero. -/
theorem optimalPhase_one (theta : ℝ) (h0 : 0 ≤ theta) (hpi : theta ≤ Real.pi/2) :
    optimalPhase 1 theta = theta := by
  obtain ⟨hmem, _, hmin⟩ := optimalPhase_spec 1 theta le_rfl h0
  apply le_antisymm hmem.2
  by_contra hnot
  have hlt : optimalPhase 1 theta < theta := lt_of_not_ge hnot
  have hs : 0 < Real.sin (theta/2) := Real.sin_pos_of_pos_of_lt_pi
    (by linarith [hmem.1]) (by linarith [Real.pi_pos])
  have hc : Real.cos (theta/2) < Real.cos (optimalPhase 1 theta/2) :=
    Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith [hmem.1])
      (by linarith [Real.pi_pos]) (by linarith)
  have hvalue := hmin ⟨h0, le_rfl⟩
  change phasePower 1 theta (optimalPhase 1 theta) ≤ phasePower 1 theta theta at hvalue
  rw [phasePower_one, phasePower_one] at hvalue
  exact (not_lt_of_ge hvalue) (mul_lt_mul_of_pos_left hc (by positivity))

/-- At a right angle, the named phase is the endpoint for `1≤p<2`. -/
theorem optimalPhase_right_angle (p : ℝ) (hp1 : 1 ≤ p) (hp2 : p < 2) :
    optimalPhase p (Real.pi / 2) = Real.pi / 2 := by
  have h := optimalPhase_spec p (Real.pi / 2) hp1 (by linarith [Real.pi_pos])
  exact (phasePower_right_angle_eq_minimum_iff p _ hp1 hp2 h.1).mp h.2.1

/-- The named phase is the unique nonnegative attaining phase on every
positive acute angle, including the critical zero-curvature case. -/
theorem phasePower_eq_phaseMinimum_iff_eq_optimalPhase
    (p theta : ℝ) (hp1 : 1 < p) (hp2 : p < 2)
    (hθ : 0 < theta) (hπ : theta < Real.pi / 2)
    {delta : ℝ} (hδ : delta ∈ Icc 0 theta) :
    phasePower p theta delta = phaseMinimum p theta ↔ delta = optimalPhase p theta := by
  obtain ⟨hopt, hatt, _⟩ := optimalPhase_spec p theta hp1.le hθ.le
  by_cases hcrit : 2 - p ≤ p * Real.cos theta
  · have hcanonical : phaseMinimum p theta = phasePower p theta 0 :=
      phaseMinimum_eq_of_isMinOn p theta 0 ⟨le_rfl, hθ.le⟩
        ((canonical_phase_isMinOn_iff p theta hp1 hp2 hθ hπ).mpr hcrit)
    have hopt0 : optimalPhase p theta = 0 :=
      (canonical_phase_unique_min_of_subcritical p theta (by linarith) hp2 hθ hπ hcrit hopt).2.mp
        (hatt.trans hcanonical)
    rw [hcanonical, hopt0]
    exact (canonical_phase_unique_min_of_subcritical p theta (by linarith) hp2 hθ hπ hcrit hδ).2
  · obtain ⟨eta, heta, _, huni⟩ := exists_unique_phase_minimizer_of_supercritical
      p theta hp1 hp2 hθ hπ (lt_of_not_ge hcrit)
    have hminimum : phaseMinimum p theta = phasePower p theta eta :=
      phaseMinimum_eq_of_isMinOn p theta eta ⟨heta.1.le, heta.2.le⟩
        (fun z hz => (huni z hz).1)
    have hopteq : optimalPhase p theta = eta :=
      (huni _ hopt).2.mp (hatt.trans hminimum)
    rw [hminimum, hopteq]
    exact (huni delta hδ).2

/-- The selected phase vanishes exactly below and at the sharp transition. -/
theorem optimalPhase_eq_zero_iff_le_criticalAngle
    (p theta : ℝ) (hp1 : 1 < p) (hp2 : p < 2)
    (hθ : 0 < theta) (hπ : theta < Real.pi / 2) :
    optimalPhase p theta = 0 ↔ theta ≤ criticalAngle p := by
  obtain ⟨_, _, hmin⟩ := optimalPhase_spec p theta hp1.le hθ.le
  constructor
  · intro hzero
    rw [hzero] at hmin
    exact (canonical_phase_isMinOn_iff_le_criticalAngle p theta hp1 hp2 hθ hπ).mp hmin
  · intro hcrit
    have hcanonical := (canonical_phase_isMinOn_iff_le_criticalAngle p theta hp1 hp2 hθ hπ).mpr hcrit
    have hcost := phaseMinimum_eq_of_isMinOn p theta 0 ⟨le_rfl, hθ.le⟩ hcanonical
    exact ((phasePower_eq_phaseMinimum_iff_eq_optimalPhase p theta hp1 hp2 hθ hπ
      ⟨le_rfl, hθ.le⟩).mp hcost.symm).symm

/-- Above the transition, the named phase lies strictly between zero and
the geometric angle. -/
theorem optimalPhase_mem_Ioo_of_supercritical
    (p theta : ℝ) (hp1 : 1 < p) (hp2 : p < 2)
    (hθ : 0 < theta) (hπ : theta < Real.pi / 2)
    (hcrit : p * Real.cos theta < 2 - p) : optimalPhase p theta ∈ Ioo 0 theta := by
  obtain ⟨eta, heta, _, huni⟩ := exists_unique_phase_minimizer_of_supercritical
    p theta hp1 hp2 hθ hπ hcrit
  have hcost := phaseMinimum_eq_of_isMinOn p theta eta ⟨heta.1.le, heta.2.le⟩
    (fun z hz => (huni z hz).1)
  have heq := (phasePower_eq_phaseMinimum_iff_eq_optimalPhase p theta hp1 hp2 hθ hπ
    ⟨heta.1.le, heta.2.le⟩).mp hcost.symm
  exact heq ▸ heta

/-- Every attaining nonnegative phase pair of a positive acute mean has
exactly one of the two signed optimal-phase forms. The two forms coincide
below and at the transition. -/
theorem chord_pair_eq_minimum_iff_optimalPhase_signs
    (p theta alpha beta : ℝ) (hp1 : 1 < p) (hp2 : p < 2)
    (hθ : 0 < theta) (hπ : theta < Real.pi / 2)
    (ha : 0 ≤ alpha) (hb : 0 ≤ beta) (hmean : alpha + beta = 2 * theta) :
    phaseChord alpha ^ p + phaseChord beta ^ p = phaseMinimum p theta ↔
      (alpha = theta + optimalPhase p theta ∧ beta = theta - optimalPhase p theta) ∨
      (alpha = theta - optimalPhase p theta ∧ beta = theta + optimalPhase p theta) := by
  let d := (alpha - beta) / 2
  have hmem : |d| ∈ Icc 0 theta := ⟨abs_nonneg _, abs_le.mpr ⟨by dsimp [d]; linarith,
    by dsimp [d]; linarith⟩⟩
  have hphase : phasePower p theta |d| = phaseChord alpha ^ p + phaseChord beta ^ p := by
    by_cases hd : 0 ≤ d
    · rw [abs_of_nonneg hd, phasePower,
        show theta + d = alpha by dsimp [d]; linarith,
        show theta - d = beta by dsimp [d]; linarith]
    · rw [abs_of_neg (lt_of_not_ge hd), phasePower,
        show theta + -d = beta by dsimp [d]; linarith,
        show theta - -d = alpha by dsimp [d]; linarith, add_comm]
  constructor
  · intro hcost
    have hopt := (phasePower_eq_phaseMinimum_iff_eq_optimalPhase
      p theta hp1 hp2 hθ hπ hmem).mp (hphase.trans hcost)
    by_cases hd : 0 ≤ d
    · rw [abs_of_nonneg hd] at hopt
      left
      constructor <;> dsimp [d] at hopt <;> linarith
    · rw [abs_of_neg (lt_of_not_ge hd)] at hopt
      right
      constructor <;> dsimp [d] at hopt <;> linarith
  · intro hsign
    have hatt := (optimalPhase_spec p theta hp1.le hθ.le).2.1
    rcases hsign with ⟨hα, hβ⟩ | ⟨hα, hβ⟩
    · rw [hα, hβ]
      exact hatt
    · rw [hα, hβ, add_comm]
      exact hatt

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.SchattenOptimalPhase

/-!
# Exact Schatten phase optimization on a truncated interval

For `1<p<2` the unique minimizer on `[d,theta]` is the larger of
`d` and the unrestricted optimal phase. This includes zero and right
angles. The argument uses compactness, the endpoint derivative and the
classification of interior stationary phases, without presupposing a
global unimodality statement.
-/

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open Set

/-- Uniqueness of the named scalar minimizer, including both geometric endpoints. -/
theorem phasePower_eq_phaseMinimum_iff_eq_optimalPhase_of_nonneg
    (p theta : ℝ) (hp1 : 1 < p) (hp2 : p < 2)
    (hθ : 0 ≤ theta) (hπ : theta ≤ Real.pi / 2)
    {delta : ℝ} (hδ : delta ∈ Icc 0 theta) :
    phasePower p theta delta = phaseMinimum p theta ↔ delta = optimalPhase p theta := by
  rcases eq_or_lt_of_le hθ with hz | hz
  · subst theta
    have hd : delta = 0 := by linarith [hδ.1, hδ.2]
    rw [hd, optimalPhase_zero p hp1.le]
    exact iff_of_true (by simpa only [optimalPhase_zero p hp1.le] using
      (optimalPhase_spec p 0 hp1.le le_rfl).2.1) (by simp)
  rcases lt_or_eq_of_le hπ with ha | ha
  · exact phasePower_eq_phaseMinimum_iff_eq_optimalPhase p theta hp1 hp2 hz ha hδ
  · subst theta
    rw [optimalPhase_right_angle p hp1.le hp2]
    exact phasePower_right_angle_eq_minimum_iff p delta hp1.le hp2 hδ

private theorem exists_phase_better_than_truncated_endpoint
    (p theta d : ℝ) (hp : 1 < p) (hθ : 0 < theta)
    (hπ : theta < Real.pi / 2) (hd : d < theta) :
    ∃ delta ∈ Ioo d theta, phasePower p theta delta < phasePower p theta theta := by
  let f : ℝ → ℝ := fun delta => phasePower p theta delta - phasePower p theta theta
  have hderiv : 0 < deriv f theta := by
    rw [((phasePower_hasDerivAt_of_one_le p theta theta hp.le).sub_const
      (phasePower p theta theta)).deriv]
    simpa only [(phasePower_hasDerivAt_of_one_le p theta theta hp.le).deriv] using
      phasePower_deriv_endpoint_pos p theta hp hθ hπ
  have hz : f theta = 0 := by simp [f]
  obtain ⟨a, b, hab, hsign⟩ :=
    (eventually_nhdsWithin_sign_eq_of_deriv_pos hderiv hz).exists_Ioo_subset
  obtain ⟨delta, hdeltaa, hdeltatheta⟩ := exists_between (max_lt hab.1 hd)
  have heq : SignType.sign (f delta) = SignType.sign (delta-theta) :=
    hsign ⟨lt_of_le_of_lt (le_max_left _ _) hdeltaa, lt_trans hdeltatheta hab.2⟩
  rw [sign_neg (sub_neg.mpr hdeltatheta)] at heq
  exact ⟨delta, ⟨lt_of_le_of_lt (le_max_right _ _) hdeltaa, hdeltatheta⟩,
    sub_neg.mp (sign_eq_neg_one_iff.mp heq)⟩

private theorem truncated_phase_minimizer_eq_left_of_optimalPhase_lt
    (p theta d delta : ℝ) (hp1 : 1 < p) (hp2 : p < 2)
    (hθ : 0 ≤ theta) (hπ : theta ≤ Real.pi / 2)
    (hopt : optimalPhase p theta < d) (hδ : delta ∈ Icc d theta)
    (hmin : IsMinOn (phasePower p theta) (Icc d theta) delta) : delta = d := by
  obtain ⟨hoptmem, _, _⟩ := optimalPhase_spec p theta hp1.le hθ
  have hθpos : 0 < theta := by linarith [hδ.1, hδ.2, hoptmem.1]
  have hπlt : theta < Real.pi / 2 := by
    rcases lt_or_eq_of_le hπ with hlt | heq
    · exact hlt
    · subst theta
      rw [optimalPhase_right_angle p hp1.le hp2] at hopt
      linarith [hδ.1, hδ.2]
  by_contra hne
  have hleft : d < delta := lt_of_le_of_ne hδ.1 (Ne.symm hne)
  have hright : delta < theta := by
    rcases lt_or_eq_of_le hδ.2 with hlt | heq
    · exact hlt
    · subst delta
      obtain ⟨eta, heta, hbetter⟩ := exists_phase_better_than_truncated_endpoint
        p theta d hp1 hθpos hπlt hleft
      exact False.elim ((not_lt_of_ge (hmin ⟨heta.1.le, heta.2.le⟩)) hbetter)
  have hstat := (hmin.isLocalMin (Icc_mem_nhds hleft hright)).deriv_eq_zero
  have hglobal := (stationary_phase_isMinOn p theta delta hp1 hp2 hθpos hπlt
    ⟨by linarith [hoptmem.1], hright⟩ hstat).1
  have hvalue := phaseMinimum_eq_of_isMinOn p theta delta
    ⟨by linarith [hoptmem.1], hδ.2⟩ hglobal
  have heq := (phasePower_eq_phaseMinimum_iff_eq_optimalPhase_of_nonneg
    p theta hp1 hp2 hθ hπ ⟨by linarith [hoptmem.1], hδ.2⟩).mp hvalue.symm
  linarith

/-- The exact unique Schatten phase minimizer on a truncated interval.
No acuteness or strict separation of the clipping point is required. -/
theorem phasePower_isMinOn_truncated_iff
    (p theta d delta : ℝ) (hp1 : 1 < p) (hp2 : p < 2)
    (hd : 0 ≤ d) (hdθ : d ≤ theta) (hπ : theta ≤ Real.pi / 2)
    (hδ : delta ∈ Icc d theta) :
    IsMinOn (phasePower p theta) (Icc d theta) delta ↔
      delta = max d (optimalPhase p theta) := by
  have hθ : 0 ≤ theta := hd.trans hdθ
  obtain ⟨hoptmem, hoptval, hoptmin⟩ := optimalPhase_spec p theta hp1.le hθ
  by_cases hclip : optimalPhase p theta < d
  · rw [max_eq_left hclip.le]
    constructor
    · exact truncated_phase_minimizer_eq_left_of_optimalPhase_lt
        p theta d delta hp1 hp2 hθ hπ hclip hδ
    · intro heq
      subst delta
      obtain ⟨eta, heta, hmin⟩ := isCompact_Icc.exists_isMinOn
        (nonempty_Icc.mpr hdθ) (continuous_phasePower p theta (by linarith)).continuousOn
      have heq := truncated_phase_minimizer_eq_left_of_optimalPhase_lt
        p theta d eta hp1 hp2 hθ hπ hclip heta hmin
      exact heq ▸ hmin
  · have hdopt : d ≤ optimalPhase p theta := le_of_not_gt hclip
    rw [max_eq_right hdopt]
    constructor
    · intro hmin
      have hle := hmin ⟨hdopt, hoptmem.2⟩
      have hge := hoptmin ⟨hd.trans hδ.1, hδ.2⟩
      exact (phasePower_eq_phaseMinimum_iff_eq_optimalPhase_of_nonneg
        p theta hp1 hp2 hθ hπ ⟨hd.trans hδ.1, hδ.2⟩).mp
          ((le_antisymm hle hge).trans hoptval)
    · intro heq
      subst delta
      exact fun eta heta => hoptmin ⟨hd.trans heta.1, heta.2⟩

/-- Attainment at the clipped phase, with membership of the exact interval. -/
theorem phasePower_clipped_optimalPhase
    (p theta d : ℝ) (hp1 : 1 < p) (hp2 : p < 2)
    (hd : 0 ≤ d) (hdθ : d ≤ theta) (hπ : theta ≤ Real.pi / 2) :
    max d (optimalPhase p theta) ∈ Icc d theta ∧
      IsMinOn (phasePower p theta) (Icc d theta) (max d (optimalPhase p theta)) := by
  have hmem : max d (optimalPhase p theta) ∈ Icc d theta :=
    ⟨le_max_left _ _, max_le hdθ (optimalPhase_spec p theta hp1.le (hd.trans hdθ)).1.2⟩
  exact ⟨hmem, (phasePower_isMinOn_truncated_iff p theta d _ hp1 hp2 hd hdθ hπ hmem).2 rfl⟩

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedPowerPhaseSelection
public import DavisKahan.FiniteDimensional.DirectRotation.SchattenOptimalPhase

/-!
# Endpoint regimes of the common phase-selection law

Positive smoothing and subquadratic powers have a unique endpoint phase at
right angles. Quadratic costs are flat there. At zero smoothing the literal
cost and its compact minimum agree with the established Schatten scalars;
the nuclear corner has a unique geometric endpoint phase. These statements
keep boundary identifications separate from the shared regular proof.

The scalar penalties are prior art, and the quadratic geometry is classical.
No novelty claim is made for endpoint formulas or for the classical calculus
used to connect the existing scalar APIs.
-/

public section
noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPowerTransport

open Set

/-- Exponent one is exactly the usual normalized Charbonnier penalty. -/
theorem penalty_one (tau s : ℝ) :
    penalty 1 tau s = Real.sqrt (tau ^ 2 + s ^ 2) - tau := by
  rw [penalty, Real.rpow_one, ← Real.sqrt_eq_rpow]

/-- Quadratic planar cost is independent of smoothing, including zero. -/
theorem phaseCost_two (tau theta delta : ℝ) :
    phaseCost 2 tau theta delta = 4 - 4 * Real.cos theta * Real.cos delta := by
  simp only [phaseCost, smoothedPowerPhaseCost, show (2 : ℝ) / 2 = 1 by norm_num,
    Real.rpow_one, Real.rpow_two, Real.cos_add, Real.cos_sub]
  ring

/-- Every right-angle phase is quadratic-optimal. This flat boundary
cannot be described by a unique positive minimizing phase. -/
theorem phaseCost_two_right_angle (tau delta : ℝ) :
    phaseCost 2 tau (Real.pi / 2) delta = 4 := by
  rw [phaseCost_two, Real.cos_pi_div_two]
  ring

/-- The exact quadratic minimum in the common compact-minimum API. -/
theorem phaseMinimum_two (tau theta : ℝ) (htau : 0 ≤ tau)
    (hθ : theta ∈ Icc 0 (Real.pi / 2)) :
    phaseMinimum 2 tau theta = 4 - 4 * Real.cos theta := by
  obtain ⟨d, hd, hv, _⟩ := exists_attains_phaseMinimum_of_nonneg 2 tau theta (by norm_num) hθ.1
  have hupper := phaseMinimum_le_cost 2 tau theta 0 (by norm_num) htau ⟨le_rfl, hθ.1⟩
  rw [phaseCost_two, Real.cos_zero, mul_one] at hupper
  refine le_antisymm hupper ?_
  rw [hv, phaseCost_two]
  have hc : 0 ≤ Real.cos theta := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hmul := mul_le_mul_of_nonneg_left (Real.cos_le_one d) hc
  nlinarith

/-- At a right angle, every positively smoothed subquadratic cost strictly
decreases to the endpoint phase. This is a common power argument. -/
theorem phaseCost_right_angle_strictAntiOn (p tau : ℝ)
    (hp : 0 < p) (hp2 : p < 2) (htau : 0 < tau) :
    StrictAntiOn (phaseCost p tau (Real.pi / 2)) (Icc 0 (Real.pi / 2)) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · exact (continuous_iff_continuousAt.mpr fun d =>
      (hasDerivAt_phaseCost p tau (Real.pi / 2) d htau).continuousAt).continuousOn
  · intro d hd
    rw [interior_Icc] at hd
    rw [(hasDerivAt_phaseCost p tau (Real.pi / 2) d htau).deriv]
    have hc : 0 < Real.cos d := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hd.1, Real.pi_pos], hd.2⟩
    have hs : 0 < Real.sin d := Real.sin_pos_of_pos_of_lt_pi hd.1
      (by linarith [hd.2, Real.pi_pos])
    have hr := smoothedPowerPhase_radicand_pos tau (Real.pi / 2 - d) htau
    rw [Real.cos_pi_div_two_sub] at hr
    have hpow := Real.rpow_lt_rpow_of_neg hr
      (by linarith : tau ^ 2 + 2 - 2 * Real.sin d < tau ^ 2 + 2 + 2 * Real.sin d)
      (by linarith : (p - 2) / 2 < 0)
    have hmul := mul_lt_mul_of_pos_left hpow (mul_pos hp hc)
    simp only [smoothedPowerPhaseSlope, Real.sin_add, Real.sin_pi_div_two,
      Real.cos_pi_div_two, one_mul, zero_mul, add_zero, Real.sin_pi_div_two_sub,
      Real.cos_add, Real.cos_pi_div_two_sub, zero_sub]
    rw [sub_neg]
    convert hmul using 1
    congr 2
    ring

/-- The right-angle minimum is uniquely attained at the endpoint when
smoothing is positive and the power is subquadratic. -/
theorem phaseCost_right_angle_unique_min (p tau : ℝ)
    (hp : 0 < p) (hp2 : p < 2) (htau : 0 < tau)
    {delta : ℝ} (hδ : delta ∈ Icc 0 (Real.pi / 2)) :
    phaseCost p tau (Real.pi / 2) (Real.pi / 2) ≤ phaseCost p tau (Real.pi / 2) delta ∧
      (phaseCost p tau (Real.pi / 2) delta = phaseCost p tau (Real.pi / 2) (Real.pi / 2) ↔
        delta = Real.pi / 2) := by
  have hm := phaseCost_right_angle_strictAntiOn p tau hp hp2 htau
  have hend : Real.pi / 2 ∈ Icc (0 : ℝ) (Real.pi / 2) := ⟨by linarith [Real.pi_pos], le_rfl⟩
  exact ⟨hm.antitoneOn hδ hend hδ.2,
    ⟨fun h => hm.injOn hδ hend h, fun h => by rw [h]⟩⟩

private theorem phase_zero_smoothing_eq_chord_power (p t : ℝ) (hp : 0 < p)
    (ht : t ∈ Icc 0 Real.pi) :
    smoothedPowerPhaseCost p 0 t = SchattenPhaseTransition.phaseChord t ^ p := by
  have hs : 0 ≤ SchattenPhaseTransition.phaseChord t := mul_nonneg (by norm_num)
    (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [ht.1])
      (by linarith [ht.2, Real.pi_pos]))
  simp only [smoothedPowerPhaseCost, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add,
    Real.zero_rpow hp.ne', sub_zero]
  rw [← SchattenPhaseTransition.phaseChord_sq]
  rw [← Real.rpow_natCast_mul hs]
  congr 1
  ring

/-- At zero smoothing the literal common cost is exactly the established
Schatten phase power on the physical interval. No ambient optimum is used. -/
theorem phaseCost_zero_smoothing_eq_phasePower (p theta delta : ℝ) (hp : 0 < p)
    (hθ : theta ∈ Icc 0 (Real.pi / 2)) (hδ : delta ∈ Icc 0 theta) :
    phaseCost p 0 theta delta = SchattenPhaseTransition.phasePower p theta delta := by
  rw [phaseCost,
    phase_zero_smoothing_eq_chord_power p (theta + delta) hp
      ⟨by linarith [hθ.1, hδ.1], by linarith [hθ.2, hδ.2]⟩,
    phase_zero_smoothing_eq_chord_power p (theta - delta) hp
      ⟨by linarith [hδ.2], by linarith [hθ.2, hδ.1, Real.pi_pos]⟩]
  rfl

/-- The compact scalar minimum agrees with the established Schatten
minimum at zero smoothing. This also identifies the nuclear corner. -/
theorem phaseMinimum_zero_smoothing_eq (p theta : ℝ) (hp : 0 < p)
    (hθ : theta ∈ Icc 0 (Real.pi / 2)) :
    phaseMinimum p 0 theta = SchattenPhaseTransition.phaseMinimum p theta := by
  unfold phaseMinimum SchattenPhaseTransition.phaseMinimum
  congr 1
  ext y
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact ⟨d, hd, (phaseCost_zero_smoothing_eq_phasePower p theta d hp hθ hd).symm⟩
  · rintro ⟨d, hd, rfl⟩
    exact ⟨d, hd, phaseCost_zero_smoothing_eq_phasePower p theta d hp hθ hd⟩

/-- The zero-smoothing strict-Schatten canonical criterion has exactly
the same critical surface as the regular smoothed family. -/
theorem canonical_phase_zero_smoothing_isMinOn_iff (p theta : ℝ)
    (hp : 1 < p) (hp2 : p < 2) (hθ : theta ∈ Ioo 0 (Real.pi / 2)) :
    IsMinOn (phaseCost p 0 theta) (Icc 0 theta) 0 ↔
      smoothedPowerCriticalCosine p 0 ≤ Real.cos theta := by
  have heq (d : ℝ) (hd : d ∈ Icc 0 theta) := phaseCost_zero_smoothing_eq_phasePower
    p theta d (by linarith) ⟨hθ.1.le, hθ.2.le⟩ hd
  have h0 := heq 0 ⟨le_rfl, hθ.1.le⟩
  have hm : IsMinOn (phaseCost p 0 theta) (Icc 0 theta) 0 ↔
      IsMinOn (SchattenPhaseTransition.phasePower p theta) (Icc 0 theta) 0 := by
    constructor
    · intro h d hd
      change SchattenPhaseTransition.phasePower p theta 0 ≤ SchattenPhaseTransition.phasePower p theta d
      rw [← h0, ← heq d hd]
      exact h hd
    · intro h d hd
      change phaseCost p 0 theta 0 ≤ phaseCost p 0 theta d
      rw [h0, heq d hd]
      exact h hd
  rw [hm, SchattenPhaseTransition.canonical_phase_isMinOn_iff p theta hp hp2 hθ.1 hθ.2,
    smoothedPowerCriticalCosine_zero p hp.le, div_le_iff₀ (by linarith : 0 < p)]
  rw [mul_comm]

/-- Nuclear minimum values at zero smoothing, in the common family API. -/
theorem phaseMinimum_nuclear (theta : ℝ) (hθ : theta ∈ Icc 0 (Real.pi / 2)) :
    phaseMinimum 1 0 theta = 2 * Real.sin theta := by
  rw [phaseMinimum_zero_smoothing_eq 1 theta (by norm_num) hθ]
  exact SchattenPhaseTransition.phaseMinimum_one theta hθ.1 hθ.2

/-- The nuclear endpoint cost is strictly decreasing on its physical
phase interval for every positive principal angle. -/
theorem phaseCost_nuclear_strictAntiOn (theta : ℝ) (hθ : theta ∈ Ioc 0 (Real.pi / 2)) :
    StrictAntiOn (phaseCost 1 0 theta) (Icc 0 theta) := by
  intro a ha b hb hab
  rw [phaseCost_zero_smoothing_eq_phasePower 1 theta a (by norm_num) ⟨hθ.1.le, hθ.2⟩ ha,
    phaseCost_zero_smoothing_eq_phasePower 1 theta b (by norm_num) ⟨hθ.1.le, hθ.2⟩ hb,
    SchattenPhaseTransition.phasePower_one, SchattenPhaseTransition.phasePower_one]
  have hs : 0 < Real.sin (theta / 2) := Real.sin_pos_of_pos_of_lt_pi
    (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  apply mul_lt_mul_of_pos_left _ (mul_pos (by norm_num) hs)
  exact Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith [ha.1])
    (by linarith [hb.2, hθ.2, Real.pi_pos]) (by linarith)

/-- Canonical quadratic phase minimizes on every physical angle. -/
theorem phaseCost_two_canonical_le (tau theta delta : ℝ)
    (hθ : theta ∈ Icc 0 (Real.pi / 2)) :
    phaseCost 2 tau theta 0 ≤ phaseCost 2 tau theta delta := by
  rw [phaseCost_two, phaseCost_two, Real.cos_zero, mul_one]
  have hc : 0 ≤ Real.cos theta := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hmul := mul_le_mul_of_nonneg_left (Real.cos_le_one delta) hc
  nlinarith

/-- **Common critical surface on the full closed parameter family.**
For every positive acute principal angle, canonical phase minimizes exactly
when its cosine lies above the critical cosine. The regular proof is shared;
zero-smoothing and the nuclear/quadratic corners are explicit boundary cases. -/
theorem canonical_phase_isMinOn_iff_of_nonneg (p tau theta : ℝ)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (htau : 0 ≤ tau) (hθ : theta ∈ Ioo 0 (Real.pi / 2)) :
    IsMinOn (phaseCost p tau theta) (Icc 0 theta) 0 ↔
      smoothedPowerCriticalCosine p tau ≤ Real.cos theta := by
  by_cases hpEq : p = 2
  · subst p
    rw [smoothedPowerCriticalCosine_two]
    refine ⟨fun _ => Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [hθ.1, Real.pi_pos], hθ.2.le⟩, ?_⟩
    intro _ d _
    exact phaseCost_two_canonical_le tau theta d ⟨hθ.1.le, hθ.2.le⟩
  have hp2' : p < 2 := lt_of_le_of_ne hp2 hpEq
  by_cases htEq : tau = 0
  · subst tau
    by_cases hpEq : p = 1
    · subst p
      have hcvalue : smoothedPowerCriticalCosine 1 0 = 1 := by
        rw [smoothedPowerCriticalCosine_zero 1 (by norm_num)]
        norm_num
      rw [hcvalue]
      have hc1 : Real.cos theta < 1 := by
        simpa only [Real.cos_zero] using Real.strictAntiOn_cos
          ⟨le_rfl, Real.pi_pos.le⟩ ⟨hθ.1.le, by linarith [hθ.2, Real.pi_pos]⟩ hθ.1
      constructor
      · intro hm
        have hlt := phaseCost_nuclear_strictAntiOn theta ⟨hθ.1, hθ.2.le⟩
          ⟨le_rfl, hθ.1.le⟩ ⟨hθ.1.le, le_rfl⟩ hθ.1
        exact False.elim ((not_lt_of_ge (hm ⟨hθ.1.le, le_rfl⟩)) hlt)
      · intro hc
        exact False.elim ((not_le_of_gt hc1) hc)
    · exact canonical_phase_zero_smoothing_isMinOn_iff p theta
        (lt_of_le_of_ne hp (Ne.symm hpEq)) hp2' hθ
  · exact canonical_phase_isMinOn_iff p tau theta hp hp2
      (lt_of_le_of_ne htau (Ne.symm htEq)) hθ

private theorem criticalCosine_pos_of_lt_two (p tau : ℝ) (hp : 1 ≤ p) (hp2 : p < 2) :
    0 < smoothedPowerCriticalCosine p tau := by
  let B := tau ^ 2 + 2
  let D := B ^ 2 - 4 * p * (2 - p)
  have hB : 2 ≤ B := by dsimp only [B]; nlinarith [sq_nonneg tau]
  have hp0 : 0 < p := by linarith
  have hprod : 0 < p * (2 - p) := mul_pos hp0 (by linarith)
  have hD : 0 ≤ D := by dsimp only [D]; nlinarith [sq_nonneg (p - 1)]
  have hs := Real.sq_sqrt hD
  have hs0 := Real.sqrt_nonneg D
  have hlt : Real.sqrt D < B := by dsimp only [D] at hs; nlinarith
  exact div_pos (sub_pos.mpr hlt) (mul_pos (by norm_num) hp0)

/-- Canonical scalar optimality on every physical angle for the full
closed family. Zero and right angles are retained explicitly. This does
not assert uniqueness at the quadratic right-angle boundary. -/
theorem canonical_phase_isMinOn_iff_on_physical_interval (p tau theta : ℝ)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (htau : 0 ≤ tau) (hθ : theta ∈ Icc 0 (Real.pi / 2)) :
    IsMinOn (phaseCost p tau theta) (Icc 0 theta) 0 ↔
      smoothedPowerCriticalCosine p tau ≤ Real.cos theta := by
  by_cases hz : theta = 0
  · subst theta
    have hc : smoothedPowerCriticalCosine p tau ≤ 1 := by
      by_cases ht : tau = 0
      · subst tau
        rw [smoothedPowerCriticalCosine_zero p hp, div_le_iff₀ (by linarith : 0 < p)]
        nlinarith
      · exact (smoothedPowerCriticalCosine_mem p tau hp hp2
          (lt_of_le_of_ne htau (Ne.symm ht))).2.le
    refine ⟨fun _ => by simpa only [Real.cos_zero] using hc, ?_⟩
    intro _ d hd
    have hd0 : d = 0 := le_antisymm hd.2 hd.1
    subst d
    exact le_rfl
  by_cases hr : theta = Real.pi / 2
  · subst theta
    by_cases hpEq : p = 2
    · subst p
      rw [smoothedPowerCriticalCosine_two, Real.cos_pi_div_two]
      refine ⟨fun _ => le_rfl, ?_⟩
      intro _ d _
      change phaseCost 2 tau (Real.pi / 2) 0 ≤ phaseCost 2 tau (Real.pi / 2) d
      rw [phaseCost_two_right_angle, phaseCost_two_right_angle]
    have hp2' : p < 2 := lt_of_le_of_ne hp2 hpEq
    have hc := criticalCosine_pos_of_lt_two p tau hp hp2'
    have hlt : phaseCost p tau (Real.pi / 2) (Real.pi / 2) < phaseCost p tau (Real.pi / 2) 0 := by
      by_cases ht : tau = 0
      · subst tau
        rw [phaseCost_zero_smoothing_eq_phasePower p _ _ (by linarith)
          ⟨by linarith [Real.pi_pos], le_rfl⟩ ⟨by linarith [Real.pi_pos], le_rfl⟩,
          phaseCost_zero_smoothing_eq_phasePower p _ _ (by linarith)
          ⟨by linarith [Real.pi_pos], le_rfl⟩ ⟨le_rfl, by linarith [Real.pi_pos]⟩]
        have hend : SchattenPhaseTransition.phasePower p (Real.pi / 2) (Real.pi / 2) = 2 ^ p := by
          simp only [SchattenPhaseTransition.phasePower, SchattenPhaseTransition.phaseChord,
            show (Real.pi / 2 + Real.pi / 2) / 2 = Real.pi / 2 by ring,
            Real.sin_pi_div_two, mul_one, sub_self, zero_div, Real.sin_zero, mul_zero,
            Real.zero_rpow (by linarith : p ≠ 0), add_zero]
        rw [hend]
        exact SchattenPhaseTransition.phasePower_right_angle_gt_endpoint p 0 hp2'
          ⟨le_rfl, by linarith [Real.pi_pos]⟩
      · exact phaseCost_right_angle_strictAntiOn p tau (by linarith) hp2'
          (lt_of_le_of_ne htau (Ne.symm ht)) ⟨le_rfl, by linarith [Real.pi_pos]⟩
          ⟨by linarith [Real.pi_pos], le_rfl⟩ (by linarith [Real.pi_pos])
    constructor
    · intro hm
      exact False.elim ((not_lt_of_ge (hm ⟨by linarith [Real.pi_pos], le_rfl⟩)) hlt)
    · intro hC
      rw [Real.cos_pi_div_two] at hC
      exact False.elim ((not_le_of_gt hc) hC)
  exact canonical_phase_isMinOn_iff_of_nonneg p tau theta hp hp2 htau
    ⟨lt_of_le_of_ne hθ.1 (Ne.symm hz), lt_of_le_of_ne hθ.2 hr⟩

/-- The compact scalar minimum equals the canonical phase value exactly
on the common closed critical regime, for all physical angles and boundaries. -/
theorem phaseMinimum_eq_canonical_iff (p tau theta : ℝ)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (htau : 0 ≤ tau) (hθ : theta ∈ Icc 0 (Real.pi / 2)) :
    phaseMinimum p tau theta = phaseCost p tau theta 0 ↔
      smoothedPowerCriticalCosine p tau ≤ Real.cos theta := by
  have hcrit := canonical_phase_isMinOn_iff_on_physical_interval p tau theta hp hp2 htau hθ
  constructor
  · intro heq
    apply hcrit.mp
    intro d hd
    change phaseCost p tau theta 0 ≤ phaseCost p tau theta d
    rw [← heq]
    exact phaseMinimum_le_cost p tau theta d (by linarith) htau hd
  · intro hc
    obtain ⟨d, hd, hv, _⟩ := exists_attains_phaseMinimum_of_nonneg p tau theta (by linarith) hθ.1
    apply le_antisymm (phaseMinimum_le_cost p tau theta 0 (by linarith) htau ⟨le_rfl, hθ.1⟩)
    rw [hv]
    exact (hcrit.mpr hc) hd

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPowerTransport

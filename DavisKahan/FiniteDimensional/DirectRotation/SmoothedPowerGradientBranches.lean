/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedPowerVariation

/-!
# Actual angular branches of smoothed-power gradient levels

The common single-peak theorem determines the complete signed phase level
sets. It supplies two roots at submaximal levels and a single root at the
peak. No explicit inverse formula for an individual branch is required.

The intermediate-value and monotonicity argument adapts
`SmoothedGradientBranches`; these are classical scalar ingredients for the
family-wide ambient spectral reduction C1, not a new historical-priority claim.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPowerTransport

open Set

/-- The common phase-gradient peak angle. -/
@[expose] def criticalAngle (p tau : ℝ) : ℝ :=
  Real.arccos (smoothedPowerCriticalCosine p tau)

/-- The positive height of the common phase-gradient peak. -/
@[expose] def peakSlope (p tau : ℝ) : ℝ :=
  smoothedPowerPhaseSlope p tau (criticalAngle p tau)

theorem criticalAngle_mem (p tau : ℝ) (hp : 1 ≤ p) (hp2 : p ≤ 2) (htau : 0 < tau) :
    criticalAngle p tau ∈ Ioo 0 Real.pi := by
  have hc := smoothedPowerCriticalCosine_mem p tau hp hp2 htau
  exact ⟨Real.arccos_pos.mpr hc.2, Real.arccos_lt_pi.mpr (by linarith [hc.1])⟩

theorem phaseSlope_odd (p tau t : ℝ) :
    smoothedPowerPhaseSlope p tau (-t) = -smoothedPowerPhaseSlope p tau t := by
  simp only [smoothedPowerPhaseSlope, Real.sin_neg, Real.cos_neg]
  ring

private theorem continuous_phaseSlope (p tau : ℝ) (htau : 0 < tau) :
    Continuous (smoothedPowerPhaseSlope p tau) :=
  continuous_iff_continuousAt.mpr fun t =>
    (hasDerivAt_smoothedPowerPhaseSlope p tau t htau).continuousAt

private theorem phaseSlope_pos (p tau t : ℝ) (hp : 1 ≤ p) (htau : 0 < tau)
    (ht : t ∈ Ioo 0 Real.pi) : 0 < smoothedPowerPhaseSlope p tau t := by
  exact mul_pos (mul_pos (by linarith) (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2))
    (Real.rpow_pos_of_pos (smoothedPowerPhase_radicand_pos tau t htau) _)

theorem peakSlope_pos (p tau : ℝ) (hp : 1 ≤ p) (hp2 : p ≤ 2) (htau : 0 < tau) :
    0 < peakSlope p tau :=
  phaseSlope_pos p tau _ hp htau (criticalAngle_mem p tau hp hp2 htau)

/-- The two roots at a positive submaximal level, unique on their respective
branches. This uses the common scalar shape rather than penalty-specific
algebraic inverse formulas. -/
theorem phaseSlope_two_roots (p tau g : ℝ)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (htau : 0 < tau)
    (hg0 : 0 < g) (hgm : g < peakSlope p tau) :
    (∃! a, a ∈ Ioo 0 (criticalAngle p tau) ∧ smoothedPowerPhaseSlope p tau a = g) ∧
    (∃! b, b ∈ Ioo (criticalAngle p tau) Real.pi ∧ smoothedPowerPhaseSlope p tau b = g) := by
  let f := smoothedPowerPhaseSlope p tau
  have hc := criticalAngle_mem p tau hp hp2 htau
  have hf0 : f 0 = 0 := by simp [f, smoothedPowerPhaseSlope]
  have hfpi : f Real.pi = 0 := by simp [f, smoothedPowerPhaseSlope]
  obtain ⟨a, ha, hag⟩ := intermediate_value_Ioo hc.1.le
    (continuous_phaseSlope p tau htau).continuousOn
    (show g ∈ Ioo (f 0) (f (criticalAngle p tau)) by
      rw [hf0]; exact ⟨hg0, hgm⟩)
  obtain ⟨b, hb, hbg⟩ := intermediate_value_Ioo' hc.2.le
    (continuous_phaseSlope p tau htau).continuousOn
    (show g ∈ Ioo (f Real.pi) (f (criticalAngle p tau)) by
      rw [hfpi]; exact ⟨hg0, hgm⟩)
  constructor
  · refine ⟨a, ⟨ha, hag⟩, ?_⟩
    intro t ht
    exact (smoothedPowerPhaseSlope_strictMonoOn p tau hp hp2 htau).injOn
      ⟨ht.1.1.le, ht.1.2.le⟩ ⟨ha.1.le, ha.2.le⟩ (ht.2.trans hag.symm)
  · refine ⟨b, ⟨hb, hbg⟩, ?_⟩
    intro t ht
    exact (smoothedPowerPhaseSlope_strictAntiOn p tau hp hp2 htau).injOn
      ⟨ht.1.1.le, ht.1.2.le⟩ ⟨hb.1.le, hb.2.le⟩ (ht.2.trans hbg.symm)

private theorem principal_phase_pos_of_gradient_pos (p tau t : ℝ)
    (hp : 1 ≤ p) (htau : 0 < tau) (ht : |t| ≤ Real.pi)
    (hg : 0 < smoothedPowerPhaseSlope p tau t) : t ∈ Ioo 0 Real.pi := by
  have hp0 : 0 < p := by linarith
  have hrad := Real.rpow_pos_of_pos (smoothedPowerPhase_radicand_pos tau t htau)
    ((p - 2) / 2)
  have hsin : 0 < Real.sin t :=
    (mul_pos_iff_of_pos_left hp0).mp ((mul_pos_iff_of_pos_right hrad).mp hg)
  have ht0 : 0 < t := by
    by_contra h
    exact (not_lt_of_ge (Real.sin_nonpos_of_nonpos_of_neg_pi_le (le_of_not_gt h)
      (by linarith [neg_abs_le t]))) hsin
  refine ⟨ht0, lt_of_le_of_ne ((le_abs_self t).trans ht) ?_⟩
  intro heq
  rw [heq, Real.sin_pi] at hsin
  exact lt_irrefl 0 hsin

/-- Exact signed level sets over the complete principal-phase interval. -/
theorem phaseSlope_signed_level_sets (p tau g : ℝ)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (htau : 0 < tau)
    (hg0 : 0 < g) (hgm : g < peakSlope p tau) :
    ∃ a ∈ Ioo 0 (criticalAngle p tau), ∃ b ∈ Ioo (criticalAngle p tau) Real.pi,
      (∀ t : ℝ, |t| ≤ Real.pi → (smoothedPowerPhaseSlope p tau t = g ↔ t = a ∨ t = b)) ∧
      (∀ t : ℝ, |t| ≤ Real.pi → (smoothedPowerPhaseSlope p tau t = -g ↔ t = -a ∨ t = -b)) := by
  obtain ⟨⟨a, ha, huniq_a⟩, ⟨b, hb, huniq_b⟩⟩ :=
    phaseSlope_two_roots p tau g hp hp2 htau hg0 hgm
  have hlevel (t : ℝ) (ht : |t| ≤ Real.pi) :
      smoothedPowerPhaseSlope p tau t = g ↔ t = a ∨ t = b := by
    constructor
    · intro hg
      have hpos := principal_phase_pos_of_gradient_pos p tau t hp htau ht (hg ▸ hg0)
      rcases lt_trichotomy t (criticalAngle p tau) with hlt | heq | hgt
      · exact Or.inl (huniq_a t ⟨⟨hpos.1, hlt⟩, hg⟩)
      · exact False.elim (hgm.ne (heq ▸ hg).symm)
      · exact Or.inr (huniq_b t ⟨⟨hgt, hpos.2⟩, hg⟩)
    · rintro (rfl | rfl)
      · exact ha.2
      · exact hb.2
  refine ⟨a, ha.1, b, hb.1, hlevel, ?_⟩
  intro t ht
  calc
    _ ↔ smoothedPowerPhaseSlope p tau (-t) = g := by
      rw [phaseSlope_odd, neg_eq_iff_eq_neg]
    _ ↔ -t = a ∨ -t = b := hlevel (-t) (by simpa only [abs_neg] using ht)
    _ ↔ t = -a ∨ t = -b := by simp only [neg_eq_iff_eq_neg]

/-- The maximum level has exactly one principal phase. -/
theorem phaseSlope_max_level_set (p tau t : ℝ)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (htau : 0 < tau) (ht : |t| ≤ Real.pi) :
    smoothedPowerPhaseSlope p tau t = peakSlope p tau ↔ t = criticalAngle p tau := by
  constructor
  · intro hg
    have hpos := principal_phase_pos_of_gradient_pos p tau t hp htau ht
      (hg ▸ peakSlope_pos p tau hp hp2 htau)
    have hc := criticalAngle_mem p tau hp hp2 htau
    rcases le_total t (criticalAngle p tau) with h | h
    · exact (smoothedPowerPhaseSlope_strictMonoOn p tau hp hp2 htau).injOn
        ⟨hpos.1.le, h⟩ ⟨hc.1.le, le_rfl⟩ hg
    · exact (smoothedPowerPhaseSlope_strictAntiOn p tau hp hp2 htau).injOn
        ⟨h, hpos.2.le⟩ ⟨le_rfl, hc.2.le⟩ hg
  · rintro rfl
    rfl

/-- Balanced opposite branches have an acute or right physical mean.
This uses the decreasing radial weight for `p<=2`; single-peak shape alone
would not imply the angle budget. -/
theorem balanced_phase_sum_le_pi (p tau a b : ℝ)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (htau : 0 < tau)
    (ha : a ∈ Ioo 0 (criticalAngle p tau))
    (hb : b ∈ Ioo (criticalAngle p tau) Real.pi)
    (hbalance : smoothedPowerPhaseSlope p tau a = smoothedPowerPhaseSlope p tau b) :
    a + b ≤ Real.pi := by
  have hc := criticalAngle_mem p tau hp hp2 htau
  have hC := smoothedPowerCriticalCosine_mem p tau hp hp2 htau
  have hchalf : criticalAngle p tau ≤ Real.pi / 2 := Real.arccos_le_pi_div_two.mpr hC.1
  have hp0 : 0 < p := by linarith
  let wa := (tau ^ 2 + 2 - 2 * Real.cos a) ^ ((p - 2) / 2)
  let wb := (tau ^ 2 + 2 - 2 * Real.cos b) ^ ((p - 2) / 2)
  have hwb : 0 < wb := Real.rpow_pos_of_pos (smoothedPowerPhase_radicand_pos tau b htau) _
  have hcos : Real.cos b < Real.cos a :=
    Real.cos_lt_cos_of_nonneg_of_le_pi ha.1.le hb.2.le (ha.2.trans hb.1)
  have hw : wb ≤ wa := Real.rpow_le_rpow_of_nonpos
    (smoothedPowerPhase_radicand_pos tau a htau) (by linarith) (by linarith)
  have hbal : Real.sin a * wa = Real.sin b * wb := by
    apply mul_left_cancel₀ hp0.ne'
    simpa only [smoothedPowerPhaseSlope, mul_assoc] using hbalance
  have hsina := Real.sin_pos_of_pos_of_lt_pi ha.1 (ha.2.trans hc.2)
  have hcompare : Real.sin a * wb ≤ Real.sin b * wb :=
    (mul_le_mul_of_nonneg_left hw hsina.le).trans_eq hbal
  have hsin : Real.sin a ≤ Real.sin b := (mul_le_mul_iff_left₀ hwb).mp hcompare
  by_contra hsum
  have hlt : Real.pi - b < a := by linarith
  have hltSin := Real.sin_lt_sin_of_lt_of_le_pi_div_two
    (by linarith [hb.2, Real.pi_pos] : -(Real.pi / 2) ≤ Real.pi - b)
    (ha.2.le.trans hchalf) hlt
  rw [Real.sin_pi_sub] at hltSin
  exact (not_lt_of_ge hsin) hltSin

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPowerTransport

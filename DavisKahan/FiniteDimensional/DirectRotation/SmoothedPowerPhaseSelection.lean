/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedPowerScalarMinimum
public import ForTauCeti.Analysis.InnerProductSpace.SmoothedPowerPhaseLogRatio
public import ForTauCeti.Analysis.Calculus.SingleCrossingMinimum

/-!
# A common phase-selection law for positively smoothed convex powers

The normalized logarithmic-curvature control is strictly increasing in phase.
The scalar minimum principle therefore gives a unique canonical phase up to
and including the critical angle, and one positive interior phase beyond it.
This is one family-wide argument for Schatten/Charbonnier interpolation,
not an assumption of scalar optimality or of ambient plane preservation.

The scalar penalty and calculus principles are classical ingredients; the
precise transport extension remains potentially novel with unresolved priority.
The unrestricted value theorem is separately proved in `SmoothedPowerBoundary`.
-/

public section
noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPowerTransport

open Set

/-- The actual derivative of the literal planar family cost. -/
theorem hasDerivAt_phaseCost (p tau theta delta : ℝ) (htau : 0 < tau) :
    HasDerivAt (phaseCost p tau theta)
      (smoothedPowerPhaseSlope p tau (theta + delta) -
        smoothedPowerPhaseSlope p tau (theta - delta)) delta := by
  have hplus : HasDerivAt (fun x : ℝ => theta + x) 1 delta := by
    simpa only [id_eq] using (hasDerivAt_id delta).const_add theta
  have hminus : HasDerivAt (fun x : ℝ => theta - x) (-1) delta := by
    simpa only [id_eq] using HasDerivAt.const_sub theta (hasDerivAt_id delta)
  have h := ((hasDerivAt_smoothedPowerPhaseCost p tau _ htau).comp delta hplus).add
    ((hasDerivAt_smoothedPowerPhaseCost p tau _ htau).comp delta hminus)
  change HasDerivAt (phaseCost p tau theta) _ delta at h
  apply h.congr_deriv
  ring

private theorem phaseCost_continuous (p tau theta : ℝ) (htau : 0 < tau) :
    Continuous (phaseCost p tau theta) :=
  continuous_iff_continuousAt.mpr fun d => (hasDerivAt_phaseCost p tau theta d htau).continuousAt

/-- The actual cost derivative has precisely the log ratio's sign.
All three alternatives are retained for minimum and stationary-point results. -/
theorem phaseCost_deriv_log_sign (p tau theta delta : ℝ)
    (hp : 0 < p) (htau : 0 < tau) (hθ : theta ∈ Ioo 0 (Real.pi / 2))
    (hδ : delta ∈ Ico 0 theta) :
    (0 < deriv (phaseCost p tau theta) delta ↔ 0 < smoothedPowerPhaseLogRatio p tau theta delta) ∧
    (deriv (phaseCost p tau theta) delta < 0 ↔ smoothedPowerPhaseLogRatio p tau theta delta < 0) ∧
    (deriv (phaseCost p tau theta) delta = 0 ↔ smoothedPowerPhaseLogRatio p tau theta delta = 0) := by
  have hp' := smoothedPowerPhaseSlope_pos p tau (theta + delta) hp htau
    ⟨by linarith [hθ.1, hδ.1], by linarith [hθ.2, hδ.2]⟩
  have hm' := smoothedPowerPhaseSlope_pos p tau (theta - delta) hp htau
    ⟨by linarith [hδ.2], by linarith [hθ.2, hδ.1, Real.pi_pos]⟩
  rw [(hasDerivAt_phaseCost p tau theta delta htau).deriv,
    smoothedPowerPhaseLogRatio_eq_log_slope p tau theta delta hp htau hθ hδ]
  refine ⟨?_, ?_, ?_⟩
  · rw [sub_pos, sub_pos, Real.log_lt_log_iff hm' hp']
  · rw [sub_neg, sub_neg, Real.log_lt_log_iff hp' hm']
  · rw [sub_eq_zero, sub_eq_zero]
    exact ⟨congrArg Real.log, Real.log_injOn_pos hp' hm'⟩

/-- The normalized log-curvature control is strictly increasing in phase.
The raw cubic is not required to be monotone. -/
theorem phaseLogControl_strictMonoOn (p tau theta : ℝ)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (htau : 0 < tau) (hθ : theta ∈ Ioo 0 (Real.pi / 2)) :
    StrictMonoOn (fun d => smoothedPowerPhaseRatioControl p tau (Real.cos theta) (Real.cos d))
      (Ico 0 theta) := by
  have hc0 : 0 < Real.cos theta :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hc1 : Real.cos theta < 1 := by
    simpa only [Real.cos_zero] using Real.strictAntiOn_cos
      ⟨le_rfl, Real.pi_pos.le⟩ ⟨hθ.1.le, by linarith [hθ.2, Real.pi_pos]⟩ hθ.1
  have hK := smoothedPowerPhaseRatioControl_strictAntiOn p tau (Real.cos theta)
    hp hp2 htau ⟨hc0, hc1⟩
  have hmem (d : ℝ) (hd : d ∈ Ico 0 theta) : Real.cos d ∈ Ioc (Real.cos theta) 1 :=
    ⟨Real.strictAntiOn_cos ⟨hd.1, by linarith [hd.2, hθ.2, Real.pi_pos]⟩
      ⟨hθ.1.le, by linarith [hθ.2, Real.pi_pos]⟩ hd.2, Real.cos_le_one d⟩
  intro a ha b hb hab
  exact hK (hmem b hb) (hmem a ha) (Real.strictAntiOn_cos
    ⟨ha.1, by linarith [ha.2, hθ.2, Real.pi_pos]⟩
    ⟨hb.1, by linarith [hb.2, hθ.2, Real.pi_pos]⟩ hab)

/-- The initial control sign is exactly the proposed critical surface. -/
theorem phaseLogControl_initial_nonneg_iff (p tau theta : ℝ)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (htau : 0 < tau) (hθ : theta ∈ Ioo 0 (Real.pi / 2)) :
    0 ≤ smoothedPowerPhaseRatioControl p tau (Real.cos theta) (Real.cos 0) ↔
      smoothedPowerCriticalCosine p tau ≤ Real.cos theta := by
  have hc1 : Real.cos theta < 1 := by
    simpa only [Real.cos_zero] using Real.strictAntiOn_cos
      ⟨le_rfl, Real.pi_pos.le⟩ ⟨hθ.1.le, by linarith [hθ.2, Real.pi_pos]⟩ hθ.1
  have hfactor := smoothedPowerPhaseRatioControl_one_mul_sq p tau (Real.cos theta) hc1.ne
  have hsq : 0 < (1 - Real.cos theta) ^ 2 := sq_pos_of_pos (sub_pos.mpr hc1)
  have hrad := smoothedPowerPhase_radicand_pos tau theta htau
  have hsign : smoothedPowerPhaseRatioControl p tau (Real.cos theta) 1 < 0 ↔
      p - 2 + (tau ^ 2 + 2) * Real.cos theta - p * Real.cos theta ^ 2 < 0 := by
    constructor
    · intro hK
      by_contra hn
      have h1 := mul_neg_of_neg_of_pos hK hsq
      have h2 := mul_nonneg hrad.le (le_of_not_gt hn)
      nlinarith [hfactor]
    · intro hP
      by_contra hn
      have h1 := mul_nonneg (le_of_not_gt hn) hsq.le
      have h2 := mul_neg_of_pos_of_neg hrad hP
      nlinarith [hfactor]
  have hcrit := hsign.trans
    ((smoothedPowerPhaseCurvature_neg_iff p tau theta (by linarith) htau).symm.trans
      (smoothedPowerPhaseCurvature_neg_iff_cos_lt_critical p tau theta hp hp2 htau))
  simpa only [Real.cos_zero, not_lt] using not_congr hcrit

/-- The negative-control side is the strict supercritical inequality. -/
theorem phaseLogControl_initial_neg_iff (p tau theta : ℝ)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (htau : 0 < tau) (hθ : theta ∈ Ioo 0 (Real.pi / 2)) :
    smoothedPowerPhaseRatioControl p tau (Real.cos theta) (Real.cos 0) < 0 ↔
      Real.cos theta < smoothedPowerCriticalCosine p tau := by
  simpa only [not_le] using not_congr (phaseLogControl_initial_nonneg_iff p tau theta hp hp2 htau hθ)

/-- Canonical phase is the unique global scalar minimizer below and at the
critical angle. Equality of the curvature threshold is included. -/
theorem canonical_phase_unique_min_of_subcritical (p tau theta : ℝ)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (htau : 0 < tau) (hθ : theta ∈ Ioo 0 (Real.pi / 2))
    (hcrit : smoothedPowerCriticalCosine p tau ≤ Real.cos theta)
    {delta : ℝ} (hδ : delta ∈ Icc 0 theta) :
    phaseCost p tau theta 0 ≤ phaseCost p tau theta delta ∧
      (phaseCost p tau theta delta = phaseCost p tau theta 0 ↔ delta = 0) := by
  have hm := SingleCrossingMinimum.strictMonoOn_of_initial_nonneg
    (phaseCost_continuous p tau theta htau).continuousOn
    (smoothedPowerPhaseLogRatio_zero p tau theta)
    (fun d hd => hasDerivAt_smoothedPowerPhaseLogRatio p tau theta d htau hθ hd)
    (phaseLogControl_strictMonoOn p tau theta hp hp2 htau hθ)
    (fun d hd => (phaseCost_deriv_log_sign p tau theta d (by linarith) htau hθ ⟨hd.1.le, hd.2⟩).1)
    ((phaseLogControl_initial_nonneg_iff p tau theta hp hp2 htau hθ).mpr hcrit)
  have hz : (0 : ℝ) ∈ Icc 0 theta := ⟨le_rfl, hθ.1.le⟩
  exact ⟨hm.monotoneOn hz hδ hδ.1,
    ⟨fun h => hm.injOn hδ hz h, fun h => by rw [h]⟩⟩

/-- There is at most one positive stationary phase, independently of
which side of the transition the principal angle lies on. -/
theorem phaseCost_stationary_unique (p tau theta : ℝ)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (htau : 0 < tau) (hθ : theta ∈ Ioo 0 (Real.pi / 2))
    {a b : ℝ} (ha : a ∈ Ioo 0 theta) (hb : b ∈ Ioo 0 theta)
    (hDa : deriv (phaseCost p tau theta) a = 0)
    (hDb : deriv (phaseCost p tau theta) b = 0) : a = b := by
  apply SingleCrossingMinimum.positive_roots_eq (smoothedPowerPhaseLogRatio_zero p tau theta)
    (fun d hd => hasDerivAt_smoothedPowerPhaseLogRatio p tau theta d htau hθ hd)
    (phaseLogControl_strictMonoOn p tau theta hp hp2 htau hθ) ha hb
  · exact (phaseCost_deriv_log_sign p tau theta a (by linarith) htau hθ ⟨ha.1.le, ha.2⟩).2.2.mp hDa
  · exact (phaseCost_deriv_log_sign p tau theta b (by linarith) htau hθ ⟨hb.1.le, hb.2⟩).2.2.mp hDb

/-- Beyond the critical angle there is one positive interior minimizing
phase, characterized by equality of the opposite phase slopes. The minimum
is unique on the full closed interval. -/
theorem exists_unique_phase_minimizer_of_supercritical (p tau theta : ℝ)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (htau : 0 < tau) (hθ : theta ∈ Ioo 0 (Real.pi / 2))
    (hcrit : Real.cos theta < smoothedPowerCriticalCosine p tau) :
    ∃ delta ∈ Ioo 0 theta, deriv (phaseCost p tau theta) delta = 0 ∧
      ∀ eta ∈ Icc 0 theta,
        phaseCost p tau theta delta ≤ phaseCost p tau theta eta ∧
          (phaseCost p tau theta eta = phaseCost p tau theta delta ↔ eta = delta) := by
  have hend := hasDerivAt_phaseCost p tau theta theta htau
  have hv : 0 < smoothedPowerPhaseSlope p tau (theta + theta) -
      smoothedPowerPhaseSlope p tau (theta - theta) := by
    simp only [sub_self, smoothedPowerPhaseSlope, Real.sin_zero, mul_zero, zero_mul, sub_zero]
    exact smoothedPowerPhaseSlope_pos p tau (theta + theta) (by linarith) htau
      ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  exact SingleCrossingMinimum.exists_unique_minimizer_of_initial_neg hθ.1
    (phaseCost_continuous p tau theta htau).continuousOn
    (smoothedPowerPhaseLogRatio_zero p tau theta)
    (fun d hd => hasDerivAt_smoothedPowerPhaseLogRatio p tau theta d htau hθ hd)
    (phaseLogControl_strictMonoOn p tau theta hp hp2 htau hθ)
    (fun d hd => (phaseCost_deriv_log_sign p tau theta d (by linarith) htau hθ ⟨hd.1.le, hd.2⟩).2.1)
    (fun d hd => (phaseCost_deriv_log_sign p tau theta d (by linarith) htau hθ ⟨hd.1.le, hd.2⟩).2.2)
    hend hv ((phaseLogControl_initial_neg_iff p tau theta hp hp2 htau hθ).mpr hcrit)

/-- Every positive stationary phase is the unique global scalar minimizer.
This certifies balanced phase pairs without confusing stationarity and
optimality for a general penalty. The log-curvature hypotheses are essential. -/
theorem positive_stationary_isMinOn (p tau theta delta : ℝ)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (htau : 0 < tau) (hθ : theta ∈ Ioo 0 (Real.pi / 2))
    (hδ : delta ∈ Ioo 0 theta) (hstationary : deriv (phaseCost p tau theta) delta = 0) :
    IsMinOn (phaseCost p tau theta) (Icc 0 theta) delta ∧
      ∀ eta ∈ Icc 0 theta,
        phaseCost p tau theta eta = phaseCost p tau theta delta ↔ eta = delta := by
  have hroot := (phaseCost_deriv_log_sign p tau theta delta (by linarith)
    htau hθ ⟨hδ.1.le, hδ.2⟩).2.2.mp hstationary
  have hinit := SingleCrossingMinimum.initial_neg_of_positive_root
    (smoothedPowerPhaseLogRatio_zero p tau theta)
    (fun d hd => hasDerivAt_smoothedPowerPhaseLogRatio p tau theta d htau hθ hd)
    (phaseLogControl_strictMonoOn p tau theta hp hp2 htau hθ) hδ hroot
  have hcrit := (phaseLogControl_initial_neg_iff p tau theta hp hp2 htau hθ).mp hinit
  obtain ⟨d, hd, hDd, hmin⟩ := exists_unique_phase_minimizer_of_supercritical
    p tau theta hp hp2 htau hθ hcrit
  have heq := phaseCost_stationary_unique p tau theta hp hp2 htau hθ hδ hd hstationary hDd
  subst d
  exact ⟨fun eta heta => (hmin eta heta).1, fun eta heta => (hmin eta heta).2⟩

/-- Exact canonical-optimality criterion for the whole regular family. -/
theorem canonical_phase_isMinOn_iff (p tau theta : ℝ)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (htau : 0 < tau) (hθ : theta ∈ Ioo 0 (Real.pi / 2)) :
    IsMinOn (phaseCost p tau theta) (Icc 0 theta) 0 ↔
      smoothedPowerCriticalCosine p tau ≤ Real.cos theta := by
  constructor
  · intro hm
    by_contra hc
    obtain ⟨d, hd, _, hmin⟩ := exists_unique_phase_minimizer_of_supercritical
      p tau theta hp hp2 htau hθ (lt_of_not_ge hc)
    have hzero : (0 : ℝ) ∈ Icc 0 theta := ⟨le_rfl, hθ.1.le⟩
    have heq := le_antisymm (hm ⟨hd.1.le, hd.2.le⟩) (hmin 0 hzero).1
    have hz := (hmin 0 hzero).2.mp heq
    linarith [hd.1]
  · intro hc d hd
    exact (canonical_phase_unique_min_of_subcritical p tau theta hp hp2 htau hθ hc hd).1

/-- The implicit compact scalar minimum equals the canonical value in
exactly the proved canonical regime, including its critical boundary. -/
theorem phaseMinimum_eq_canonical_of_le_critical (p tau theta : ℝ)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (htau : 0 < tau) (hθ : theta ∈ Ioo 0 (Real.pi / 2))
    (hcrit : smoothedPowerCriticalCosine p tau ≤ Real.cos theta) :
    phaseMinimum p tau theta = phaseCost p tau theta 0 := by
  obtain ⟨d, hd, hvalue, _⟩ := exists_attains_phaseMinimum p tau theta htau hθ.1.le
  apply le_antisymm (phaseMinimum_le_cost p tau theta 0 (by linarith) htau.le ⟨le_rfl, hθ.1.le⟩)
  rw [hvalue]
  exact (canonical_phase_unique_min_of_subcritical p tau theta hp hp2 htau hθ hcrit hd).1

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPowerTransport

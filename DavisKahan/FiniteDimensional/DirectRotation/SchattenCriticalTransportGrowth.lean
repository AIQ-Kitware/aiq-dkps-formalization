/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SchattenCriticalGrowth
public import DavisKahan.FiniteDimensional.DirectRotation.SchattenPhaseTransport

/-!
# Critical growth in actual unitary transport distance

The critical Schatten phase law is realized by the literal Schatten
power cost of feasible complex planar unitary transporters and their
operator-norm distance. Thus uniqueness at the critical threshold does
not imply a positive quadratic growth modulus, even on a single plane.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open TauCeti.DavisKahan1970.Section4Examples Filter Set
open scoped ENNReal Topology

/-- Actual Schatten power cost on the complete feasible phase interval. -/
theorem scalarPhaseTransport_schattenPower
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (theta : ℝ) (hθ : theta ∈ Icc 0 (Real.pi / 2))
    (delta : ℝ) (hδ : delta ∈ Icc 0 theta) :
    UnitarilyInvariantSeminorm.schatten ℂ ComplexPlane ComplexPlane p
        (LinearMap.id - (scalarPhaseTransport theta delta).toLinearMap) ^ p.toReal =
      phasePower p.toReal theta delta := by
  have hp1 : 1 ≤ p.toReal := by
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono hp (Fact.out : 1 ≤ p)
  have hp0 : p.toReal ≠ 0 := by linarith
  have hnonneg : 0 ≤ phasePower p.toReal theta delta :=
    (phaseMinimum_nonneg p.toReal theta hp1 hθ).trans
      (phaseMinimum_le_phasePower p.toReal theta hp1 hθ.1 hδ)
  rw [scalarPhaseTransport_schatten p hp theta delta hδ.1 hδ.2 hθ.2,
    one_div, Real.rpow_inv_rpow hnonneg hp0]

/-- The exact operator-norm distance between any two scalar phases of
the same planar transport is the distance between their unit phases. -/
theorem scalarPhaseTransport_norm_sub (theta delta eta : ℝ) :
    ‖(scalarPhaseTransport theta delta : ComplexPlane →L[ℂ] ComplexPlane) -
        (scalarPhaseTransport theta eta : ComplexPlane →L[ℂ] ComplexPlane)‖ =
      ‖example42Phase delta - example42Phase eta‖ := by
  have hlin : (scalarPhaseTransport theta delta).toLinearMap -
      (scalarPhaseTransport theta eta).toLinearMap =
      (example42Phase delta - example42Phase eta) • (scalarPhaseTransport theta 0).toLinearMap := by
    simp only [scalarPhaseTransport_toLinearMap, example42Competitor_eq_phase_smul,
      example42Phase_zero, one_smul, sub_smul]
  have hfactor : (scalarPhaseTransport theta delta : ComplexPlane →L[ℂ] ComplexPlane) -
      (scalarPhaseTransport theta eta : ComplexPlane →L[ℂ] ComplexPlane) =
      (example42Phase delta - example42Phase eta) •
        (scalarPhaseTransport theta 0 : ComplexPlane →L[ℂ] ComplexPlane) := by
    apply ContinuousLinearMap.ext
    intro x
    exact congrArg (fun A : ComplexPlane →ₗ[ℂ] ComplexPlane => A x) hlin
  rw [hfactor, norm_smul, (scalarPhaseTransport theta 0).norm_toContinuousLinearMap, mul_one]

/-- The actual displacement from the canonical phase is the scalar chord. -/
theorem scalarPhaseTransport_norm_sub_zero (theta delta : ℝ) :
    ‖(scalarPhaseTransport theta delta : ComplexPlane →L[ℂ] ComplexPlane) -
        (scalarPhaseTransport theta 0 : ComplexPlane →L[ℂ] ComplexPlane)‖ = |phaseChord delta| := by
  rw [scalarPhaseTransport_norm_sub, example42Phase_zero, norm_sub_rev,
    norm_one_sub_example42Phase]
  simp only [phaseChord, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]

/-- Scalar phases approach the actual canonical transporter in operator norm. -/
theorem tendsto_scalarPhaseTransport_norm_sub_zero (theta : ℝ) :
    Tendsto (fun delta : ℝ =>
      ‖(scalarPhaseTransport theta delta : ComplexPlane →L[ℂ] ComplexPlane) -
        (scalarPhaseTransport theta 0 : ComplexPlane →L[ℂ] ComplexPlane)‖)
      (𝓝 0) (𝓝 0) := by
  simp_rw [scalarPhaseTransport_norm_sub_zero]
  have hc : Continuous (fun delta : ℝ => |phaseChord delta|) := by unfold phaseChord; fun_prop
  simpa only [phaseChord, zero_div, Real.sin_zero, mul_zero, abs_zero] using hc.tendsto 0

private theorem tendsto_phaseChord_div_self :
    Tendsto (fun delta : ℝ => phaseChord delta / delta) (𝓝[>] 0) (𝓝 1) := by
  simpa only [phaseChord, zero_add, zero_div, Real.cos_zero, Real.sin_zero, mul_zero, zero_mul,
    sub_zero, smul_eq_mul, div_eq_mul_inv, mul_comm] using
    (phaseChord_hasDerivAt 0).tendsto_slope_zero_right

/-- The exact critical coefficient is unchanged when phase is replaced
by actual operator-norm distance between the feasible unitary transports. -/
theorem tendsto_critical_planar_transport_quartic_ratio
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2) :
    Tendsto (fun delta : ℝ =>
      (UnitarilyInvariantSeminorm.schatten ℂ ComplexPlane ComplexPlane p
          (LinearMap.id - (scalarPhaseTransport (criticalAngle p.toReal) delta).toLinearMap) ^ p.toReal -
        UnitarilyInvariantSeminorm.schatten ℂ ComplexPlane ComplexPlane p
          (LinearMap.id - (scalarPhaseTransport (criticalAngle p.toReal) 0).toLinearMap) ^ p.toReal) /
        ‖(scalarPhaseTransport (criticalAngle p.toReal) delta : ComplexPlane →L[ℂ] ComplexPlane) -
          (scalarPhaseTransport (criticalAngle p.toReal) 0 : ComplexPlane →L[ℂ] ComplexPlane)‖ ^ 4)
      (𝓝[>] 0)
      (𝓝 (p.toReal * (2 - p.toReal) * phaseChord (criticalAngle p.toReal) ^ (p.toReal - 2) / 24)) := by
  have ht := criticalAngle_mem p.toReal hp1 hp2
  have hphase := (tendsto_critical_phase_quartic_ratio p.toReal hp1 hp2).mono_left
    (nhdsGT_le_nhdsNE (0 : ℝ))
  have h := hphase.div (tendsto_phaseChord_div_self.pow 4) (by norm_num : (1 : ℝ) ^ 4 ≠ 0)
  simp only [one_pow, div_one] at h
  apply h.congr'
  filter_upwards [Ioo_mem_nhdsGT ht.1] with delta hdelta
  rw [scalarPhaseTransport_schattenPower p hp _ ⟨ht.1.le, ht.2.le⟩ delta
      ⟨hdelta.1.le, hdelta.2.le⟩,
    scalarPhaseTransport_schattenPower p hp _ ⟨ht.1.le, ht.2.le⟩ 0 ⟨le_rfl, ht.1.le⟩,
    scalarPhaseTransport_norm_sub_zero]
  have hchord : 0 < phaseChord delta := phaseChord_pos hdelta.1 (by linarith [hdelta.2, ht.2, Real.pi_pos])
  rw [abs_of_pos hchord]
  simp only [Pi.div_apply]
  field_simp [hdelta.1.ne', hchord.ne']

/-- Critical excess divided by the square of the actual operator-norm
distance tends to zero along feasible unitary transporters. -/
theorem tendsto_critical_planar_transport_quadratic_ratio
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2) :
    Tendsto (fun delta : ℝ =>
      (UnitarilyInvariantSeminorm.schatten ℂ ComplexPlane ComplexPlane p
          (LinearMap.id - (scalarPhaseTransport (criticalAngle p.toReal) delta).toLinearMap) ^ p.toReal -
        UnitarilyInvariantSeminorm.schatten ℂ ComplexPlane ComplexPlane p
          (LinearMap.id - (scalarPhaseTransport (criticalAngle p.toReal) 0).toLinearMap) ^ p.toReal) /
        ‖(scalarPhaseTransport (criticalAngle p.toReal) delta : ComplexPlane →L[ℂ] ComplexPlane) -
          (scalarPhaseTransport (criticalAngle p.toReal) 0 : ComplexPlane →L[ℂ] ComplexPlane)‖ ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
  let theta := criticalAngle p.toReal
  let D (delta : ℝ) :=
    ‖(scalarPhaseTransport theta delta : ComplexPlane →L[ℂ] ComplexPlane) -
      (scalarPhaseTransport theta 0 : ComplexPlane →L[ℂ] ComplexPlane)‖
  have hD : Tendsto (fun delta => D delta ^ 2) (𝓝[>] 0) (𝓝 0) := by
    simpa only [zero_pow (by norm_num : 2 ≠ 0)] using
      ((tendsto_scalarPhaseTransport_norm_sub_zero theta).mono_left nhdsWithin_le_nhds).pow 2
  have h := (tendsto_critical_planar_transport_quartic_ratio p hp hp1 hp2).mul hD
  simp only [mul_zero] at h
  apply h.congr'
  have ht := criticalAngle_mem p.toReal hp1 hp2
  filter_upwards [Ioo_mem_nhdsGT ht.1] with delta hdelta
  have hchord : 0 < phaseChord delta := phaseChord_pos hdelta.1 (by linarith [hdelta.2, ht.2, Real.pi_pos])
  have hDpos : 0 < D delta := by
    dsimp only [D]
    rw [scalarPhaseTransport_norm_sub_zero]
    exact abs_pos.mpr hchord.ne'
  change (_ / D delta ^ 4) * D delta ^ 2 = _ / D delta ^ 2
  field_simp [hDpos.ne']

/-- Every operator-norm neighborhood of the critical planar optimizer
contains a feasible nonzero competitor violating any positive quadratic
Schatten-power growth bound. This refutes a bound over all ambient
unitary transporters. -/
theorem critical_planar_transport_no_quadratic_modulus
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (c radius : ℝ) (hc : 0 < c) (hradius : 0 < radius) :
    ∃ W : ComplexPlane ≃ₗᵢ[ℂ] ComplexPlane,
      ComplexTraceOptimality.sourceLine.map W.toLinearMap =
          ComplexTraceOptimality.targetLine (criticalAngle p.toReal) ∧
        0 < ‖(W : ComplexPlane →L[ℂ] ComplexPlane) -
          (scalarPhaseTransport (criticalAngle p.toReal) 0 : ComplexPlane →L[ℂ] ComplexPlane)‖ ∧
        ‖(W : ComplexPlane →L[ℂ] ComplexPlane) -
          (scalarPhaseTransport (criticalAngle p.toReal) 0 : ComplexPlane →L[ℂ] ComplexPlane)‖ < radius ∧
        UnitarilyInvariantSeminorm.schatten ℂ ComplexPlane ComplexPlane p
            (LinearMap.id - W.toLinearMap) ^ p.toReal -
          UnitarilyInvariantSeminorm.schatten ℂ ComplexPlane ComplexPlane p
            (LinearMap.id - (scalarPhaseTransport (criticalAngle p.toReal) 0).toLinearMap) ^ p.toReal <
          c * ‖(W : ComplexPlane →L[ℂ] ComplexPlane) -
            (scalarPhaseTransport (criticalAngle p.toReal) 0 : ComplexPlane →L[ℂ] ComplexPlane)‖ ^ 2 := by
  let theta := criticalAngle p.toReal
  let D (delta : ℝ) :=
    ‖(scalarPhaseTransport theta delta : ComplexPlane →L[ℂ] ComplexPlane) -
      (scalarPhaseTransport theta 0 : ComplexPlane →L[ℂ] ComplexPlane)‖
  let F (delta : ℝ) := UnitarilyInvariantSeminorm.schatten ℂ ComplexPlane ComplexPlane p
    (LinearMap.id - (scalarPhaseTransport theta delta).toLinearMap) ^ p.toReal
  have ht := criticalAngle_mem p.toReal hp1 hp2
  have hDlim : Tendsto D (𝓝[>] 0) (𝓝 0) :=
    (tendsto_scalarPhaseTransport_norm_sub_zero theta).mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun delta => (F delta - F 0) / D delta ^ 2)
      (𝓝[>] 0) (𝓝 0) := tendsto_critical_planar_transport_quadratic_ratio p hp hp1 hp2
  have hnear : ∀ᶠ delta : ℝ in 𝓝[>] 0, delta ∈ Ioo 0 (criticalAngle p.toReal) :=
    Ioo_mem_nhdsGT ht.1
  obtain ⟨delta, hdelta, hsmall, hcost⟩ :=
    (hnear.and ((hDlim.eventually (Iio_mem_nhds hradius)).and
      (hlim.eventually (Iio_mem_nhds hc)))).exists
  have hchord : 0 < phaseChord delta := phaseChord_pos hdelta.1 (by linarith [hdelta.2, ht.2, Real.pi_pos])
  have hDpos : 0 < D delta := by
    dsimp only [D]
    rw [scalarPhaseTransport_norm_sub_zero]
    exact abs_pos.mpr hchord.ne'
  exact ⟨scalarPhaseTransport theta delta, scalarPhaseTransport_transports theta delta,
    hDpos, hsmall, (div_lt_iff₀ (pow_pos hDpos 2)).mp hcost⟩

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

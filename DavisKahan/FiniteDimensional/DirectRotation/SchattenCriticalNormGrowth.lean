/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SchattenCriticalTransportGrowth
public import Mathlib.Analysis.Calculus.DSlope

/-!
# Critical conditioning of the original Schatten norm objective

Taking the positive `p`-th root preserves the quartic critical exponent
and gives an explicit sharp coefficient. The norm objective itself has
no positive quadratic growth modulus on ambient feasible transporters.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open TauCeti.DavisKahan1970.Section4Examples Filter Set
open scoped ENNReal Topology

private theorem critical_root_coefficient (p x : ℝ) (hp : p ≠ 0) (hx : 0 < x) :
    (p * (2 - p) * x ^ (p - 2) / 24) *
        ((1 / p) * (2 * x ^ p) ^ (1 / p - 1)) =
      (2 - p) * (2 : ℝ) ^ (1 / p - 1) / (24 * x) := by
  have hxp : 0 ≤ x ^ p := Real.rpow_nonneg hx.le _
  have hmul : p * (1 / p - 1) = 1 - p := by field_simp
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hxp,
    ← Real.rpow_mul hx.le, hmul]
  calc
    _ = (2 - p) * (2 : ℝ) ^ (1 / p - 1) / 24 *
        (x ^ (p - 2) * x ^ (1 - p)) := by field_simp
    _ = _ := by
      rw [← Real.rpow_add hx, show p - 2 + (1 - p) = -1 by ring, Real.rpow_neg_one]
      ring

/-- Exact critical quartic coefficient for the original Schatten norm
excess and actual operator-norm distance, along feasible planar transporters. -/
theorem tendsto_critical_planar_schatten_norm_quartic_ratio
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2) :
    Tendsto (fun delta : ℝ =>
      (UnitarilyInvariantSeminorm.schatten ℂ ComplexPlane ComplexPlane p
          (LinearMap.id - (scalarPhaseTransport (criticalAngle p.toReal) delta).toLinearMap) -
        UnitarilyInvariantSeminorm.schatten ℂ ComplexPlane ComplexPlane p
          (LinearMap.id - (scalarPhaseTransport (criticalAngle p.toReal) 0).toLinearMap)) /
        ‖(scalarPhaseTransport (criticalAngle p.toReal) delta : ComplexPlane →L[ℂ] ComplexPlane) -
          (scalarPhaseTransport (criticalAngle p.toReal) 0 : ComplexPlane →L[ℂ] ComplexPlane)‖ ^ 4)
      (𝓝[>] 0)
      (𝓝 ((2 - p.toReal) * (2 : ℝ) ^ (1 / p.toReal - 1) /
        (24 * phaseChord (criticalAngle p.toReal)))) := by
  let theta := criticalAngle p.toReal
  let N (delta : ℝ) := UnitarilyInvariantSeminorm.schatten ℂ ComplexPlane ComplexPlane p
    (LinearMap.id - (scalarPhaseTransport theta delta).toLinearMap)
  let F (delta : ℝ) := N delta ^ p.toReal
  let g (x : ℝ) := x ^ (1 / p.toReal)
  let D (delta : ℝ) :=
    ‖(scalarPhaseTransport theta delta : ComplexPlane →L[ℂ] ComplexPlane) -
      (scalarPhaseTransport theta 0 : ComplexPlane →L[ℂ] ComplexPlane)‖
  have ht := criticalAngle_mem p.toReal hp1 hp2
  have hp0 : p.toReal ≠ 0 := by linarith
  have hchord : 0 < phaseChord theta := phaseChord_pos ht.1 (by linarith [ht.2, Real.pi_pos])
  have hFzero : F 0 = 2 * phaseChord theta ^ p.toReal := by
    change N 0 ^ p.toReal = _
    rw [scalarPhaseTransport_schattenPower p hp theta ⟨ht.1.le, ht.2.le⟩ 0 ⟨le_rfl, ht.1.le⟩]
    simp only [phasePower, add_zero, sub_zero, two_mul]
  have hFpos : 0 < F 0 := by rw [hFzero]; exact mul_pos (by norm_num) (Real.rpow_pos_of_pos hchord _)
  have hroot (delta : ℝ) : g (F delta) = N delta := by
    dsimp only [g, F]
    rw [one_div, Real.rpow_rpow_inv (apply_nonneg _ _) hp0]
  have hg : HasDerivAt g ((1 / p.toReal) * (F 0) ^ (1 / p.toReal - 1)) (F 0) :=
    Real.hasDerivAt_rpow_const (Or.inl hFpos.ne')
  have hnear : ∀ᶠ delta : ℝ in 𝓝[>] 0, delta ∈ Ioo 0 theta := Ioo_mem_nhdsGT ht.1
  have hFlim : Tendsto F (𝓝[>] 0) (𝓝 (F 0)) := by
    have hcont := (continuous_phasePower p.toReal theta (by linarith : 0 ≤ p.toReal)).tendsto 0
    have hzero : phasePower p.toReal theta 0 = F 0 := by
      rw [hFzero]
      simp only [phasePower, add_zero, sub_zero, two_mul]
    rw [hzero] at hcont
    apply (hcont.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [hnear] with delta hdelta
    exact (scalarPhaseTransport_schattenPower p hp theta ⟨ht.1.le, ht.2.le⟩ delta
      ⟨hdelta.1.le, hdelta.2.le⟩).symm
  have hslope := (continuousAt_dslope_same.mpr hg.differentiableAt).tendsto.comp hFlim
  rw [dslope_same, hg.deriv] at hslope
  have hpower : Tendsto (fun delta => (F delta - F 0) / D delta ^ 4) (𝓝[>] 0)
      (𝓝 (p.toReal * (2 - p.toReal) * phaseChord theta ^ (p.toReal - 2) / 24)) :=
    tendsto_critical_planar_transport_quartic_ratio p hp hp1 hp2
  have h := hpower.mul hslope
  have hcoef : (p.toReal * (2 - p.toReal) * phaseChord theta ^ (p.toReal - 2) / 24) *
      ((1 / p.toReal) * (F 0) ^ (1 / p.toReal - 1)) =
        (2 - p.toReal) * (2 : ℝ) ^ (1 / p.toReal - 1) / (24 * phaseChord theta) := by
    rw [hFzero, critical_root_coefficient p.toReal (phaseChord theta) hp0 hchord]
  rw [hcoef] at h
  apply h.congr'
  filter_upwards [] with delta
  simp only [Function.comp_apply]
  have he := sub_smul_dslope g (F 0) (F delta)
  rw [smul_eq_mul, hroot, hroot] at he
  change ((F delta - F 0) / D delta ^ 4) * dslope g (F 0) (F delta) =
    (N delta - N 0) / D delta ^ 4
  rw [← he]
  ring

/-- The sharp critical norm-growth coefficient is strictly positive. -/
theorem critical_schatten_norm_quartic_coefficient_pos
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    0 < (2 - p) * (2 : ℝ) ^ (1 / p - 1) / (24 * phaseChord (criticalAngle p)) := by
  have ht := criticalAngle_mem p hp1 hp2
  have hc := phaseChord_pos ht.1 (by linarith [ht.2, Real.pi_pos])
  exact div_pos (mul_pos (by linarith) (Real.rpow_pos_of_pos (by norm_num) _))
    (mul_pos (by norm_num) hc)

/-- The original norm excess has no positive quadratic scale at the
critical optimizer, measured in actual operator distance. -/
theorem tendsto_critical_planar_schatten_norm_quadratic_ratio
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2) :
    Tendsto (fun delta : ℝ =>
      (UnitarilyInvariantSeminorm.schatten ℂ ComplexPlane ComplexPlane p
          (LinearMap.id - (scalarPhaseTransport (criticalAngle p.toReal) delta).toLinearMap) -
        UnitarilyInvariantSeminorm.schatten ℂ ComplexPlane ComplexPlane p
          (LinearMap.id - (scalarPhaseTransport (criticalAngle p.toReal) 0).toLinearMap)) /
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
  have h := (tendsto_critical_planar_schatten_norm_quartic_ratio p hp hp1 hp2).mul hD
  simp only [mul_zero] at h
  apply h.congr'
  have ht := criticalAngle_mem p.toReal hp1 hp2
  filter_upwards [Ioo_mem_nhdsGT ht.1] with delta hdelta
  have hc : 0 < phaseChord delta := phaseChord_pos hdelta.1 (by linarith [hdelta.2, ht.2, Real.pi_pos])
  have hDpos : 0 < D delta := by
    dsimp only [D]
    rw [scalarPhaseTransport_norm_sub_zero]
    exact abs_pos.mpr hc.ne'
  change (_ / D delta ^ 4) * D delta ^ 2 = _ / D delta ^ 2
  field_simp [hDpos.ne']

/-- Every actual neighborhood of the canonical critical transporter
contains a feasible unitary violating any proposed positive quadratic
growth bound for the original Schatten norm objective. -/
theorem critical_planar_schatten_norm_no_quadratic_modulus
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
            (LinearMap.id - W.toLinearMap) -
          UnitarilyInvariantSeminorm.schatten ℂ ComplexPlane ComplexPlane p
            (LinearMap.id - (scalarPhaseTransport (criticalAngle p.toReal) 0).toLinearMap) <
          c * ‖(W : ComplexPlane →L[ℂ] ComplexPlane) -
            (scalarPhaseTransport (criticalAngle p.toReal) 0 : ComplexPlane →L[ℂ] ComplexPlane)‖ ^ 2 := by
  let theta := criticalAngle p.toReal
  let D (delta : ℝ) :=
    ‖(scalarPhaseTransport theta delta : ComplexPlane →L[ℂ] ComplexPlane) -
      (scalarPhaseTransport theta 0 : ComplexPlane →L[ℂ] ComplexPlane)‖
  let N (delta : ℝ) := UnitarilyInvariantSeminorm.schatten ℂ ComplexPlane ComplexPlane p
    (LinearMap.id - (scalarPhaseTransport theta delta).toLinearMap)
  have ht := criticalAngle_mem p.toReal hp1 hp2
  have hDlim : Tendsto D (𝓝[>] 0) (𝓝 0) :=
    (tendsto_scalarPhaseTransport_norm_sub_zero theta).mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun delta => (N delta - N 0) / D delta ^ 2)
      (𝓝[>] 0) (𝓝 0) := tendsto_critical_planar_schatten_norm_quadratic_ratio p hp hp1 hp2
  have hnear : ∀ᶠ delta : ℝ in 𝓝[>] 0, delta ∈ Ioo 0 theta := Ioo_mem_nhdsGT ht.1
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

/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.SchattenGlobalAttainment

/-!
# The exact higher-rank canonical-rotation cutoff

For `1 < p < 2`, the completed canonical rotation minimizes Schatten
displacement precisely when every principal angle is at most
`arccos ((2-p)/p)`. This includes the critical equality and all zero
angles. A right-angle plane always excludes canonical optimality.
The comparison is with all admissible complex unitary transports.
-/

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open Set
open scoped ENNReal BigOperators

/-- On the closed physical angle interval, the scalar minimum equals the
canonical cost exactly below and at the critical angle. -/
theorem phaseMinimum_eq_canonical_iff_le_criticalAngle
    (p theta : ℝ) (hp1 : 1 < p) (hp2 : p < 2)
    (hθ : theta ∈ Icc 0 (Real.pi / 2)) :
    phaseMinimum p theta = phasePower p theta 0 ↔ theta ≤ criticalAngle p := by
  have hc := criticalAngle_mem p hp1 hp2
  by_cases hz : theta = 0
  · subst theta
    have hF : phasePower p 0 0 = 0 := by
      simp [phasePower, phaseChord, Real.zero_rpow (show p ≠ 0 by linarith)]
    rw [phaseMinimum_zero_angle p hp1.le, hF]
    exact iff_of_true rfl hc.1.le
  by_cases hr : theta = Real.pi / 2
  · subst theta
    have hn : phaseMinimum p (Real.pi / 2) ≠ phasePower p (Real.pi / 2) 0 := by
      intro heq
      have hzero := (phasePower_right_angle_eq_minimum_iff p 0 hp1.le hp2
        ⟨le_rfl, by positivity⟩).mp heq.symm
      linarith [Real.pi_pos]
    exact iff_of_false hn (not_le.mpr hc.2)
  have ht0 : 0 < theta := lt_of_le_of_ne hθ.1 (Ne.symm hz)
  have htp : theta < Real.pi / 2 := lt_of_le_of_ne hθ.2 hr
  constructor
  · intro heq
    apply (canonical_phase_isMinOn_iff_le_criticalAngle p theta hp1 hp2 ht0 htp).mp
    intro delta hδ
    rw [← heq]
    exact phaseMinimum_le_phasePower p theta hp1.le hθ.1 hδ
  · intro hcrit
    exact phaseMinimum_eq_of_isMinOn p theta 0 ⟨le_rfl, hθ.1⟩
      ((canonical_phase_isMinOn_iff_le_criticalAngle p theta hp1 hp2 ht0 htp).mpr hcrit)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- The displacement power of the completed canonical rotation is the
sum of the canonical scalar costs over the accepted principal angles. -/
theorem nonacuteDirectRotation_schatten_rpow_eq_sum_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L) :
    UnitarilyInvariantSeminorm.schatten ℂ E E p
      (LinearMap.id - (nonacuteDirectRotation K L
        (finiteCrossedDefectEquiv K L hKL)).toLinearMap) ^ p.toReal =
      ∑ i : Fin (Module.finrank ℂ K), phasePower p.toReal (K.principalAngles L i) 0 := by
  have hp0 : p.toReal ≠ 0 :=
    (ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hp).ne'
  let D := finiteCrossedDefectEquiv K L hKL
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L D, nonacuteDirectRotation_mem_unitary K L D⟩ :
      unitary (E →L[ℂ] E))
  obtain ⟨n, m, e, theta, hθ, hC0, hC1, hCf, hR0, hR1, hRf, hJ0⟩ :=
    SmoothedPhaseTransition.exists_subspace_paired_rotation_basis K L hKL
  have hcost := schatten_paired_phase_transport_eq_sum_complex p hp e theta (fun _ => 0)
    (fun i => ⟨(hθ i).1.le, (hθ i).2⟩) (fun i => ⟨le_rfl, (hθ i).1.le⟩)
    R (LinearIsometryEquiv.refl ℂ E) hR0 hR1 hRf (by simp) (by simp)
  have hsum := SmoothedPhaseTransition.sum_principalAngles_eq_paired_sum K L e theta hθ
    hC0 hC1 hCf hJ0 (fun t => phasePower p.toReal t 0)
    (by simp [phasePower, phaseChord, Real.zero_rpow hp0])
  exact hcost.trans hsum.symm

/-- **The exact canonical cutoff at arbitrary rank.** The completed
canonical rotation is globally Schatten-optimal if and only if every
principal angle lies below or at the scalar critical angle. -/
theorem nonacuteDirectRotation_schatten_minimal_iff_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L) :
    (∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
      UnitarilyInvariantSeminorm.schatten ℂ E E p
          (LinearMap.id - (nonacuteDirectRotation K L
            (finiteCrossedDefectEquiv K L hKL)).toLinearMap) ^ p.toReal ≤
        UnitarilyInvariantSeminorm.schatten ℂ E E p
          (LinearMap.id - T.toLinearMap) ^ p.toReal) ↔
      ∀ i : Fin (Module.finrank ℂ K), K.principalAngles L i ≤ criticalAngle p.toReal := by
  classical
  have hθ (i : Fin (Module.finrank ℂ K)) : K.principalAngles L i ∈ Icc 0 (Real.pi / 2) :=
    ⟨K.principalAngles_nonneg L i, K.principalAngles_le_pi_div_two L i⟩
  have hle (i : Fin (Module.finrank ℂ K)) :
      phaseMinimum p.toReal (K.principalAngles L i) ≤
        phasePower p.toReal (K.principalAngles L i) 0 :=
    phaseMinimum_le_phasePower p.toReal _ hp1.le (hθ i).1 ⟨le_rfl, (hθ i).1⟩
  obtain ⟨W, hW, hcost, hbound⟩ :=
    exists_unitary_minimizing_schatten_transport_principalAngles_complex p hp hp1 hp2 K L hKL
  constructor
  · intro hmin
    have hc := hmin W hW
    rw [hcost, nonacuteDirectRotation_schatten_rpow_eq_sum_complex p hp K L hKL] at hc
    have heq := le_antisymm (Finset.sum_le_sum (fun i _ => hle i)) hc
    intro i
    have hi := (Finset.sum_eq_sum_iff_of_le (fun i _ => hle i)).mp heq i (Finset.mem_univ i)
    exact (phaseMinimum_eq_canonical_iff_le_criticalAngle p.toReal _ hp1 hp2 (hθ i)).mp hi
  · intro hcrit T hT
    rw [nonacuteDirectRotation_schatten_rpow_eq_sum_complex p hp K L hKL]
    have heq (i : Fin (Module.finrank ℂ K)) :
        phasePower p.toReal (K.principalAngles L i) 0 =
          phaseMinimum p.toReal (K.principalAngles L i) :=
      ((phaseMinimum_eq_canonical_iff_le_criticalAngle p.toReal _ hp1 hp2 (hθ i)).mpr
        (hcrit i)).symm
    simp only [heq]
    exact hbound T hT

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

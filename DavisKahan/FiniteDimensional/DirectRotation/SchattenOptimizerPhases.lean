/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.SchattenOptimizerAngles
import DavisKahan.FiniteDimensional.DirectRotation.SchattenOptimalPhase

/-!
# Every optimizer's positive-angle signed phases

The actual positive-gradient space has a complete reflection-paired basis
whose geometric angles lie strictly between zero and a right angle.
Each pair carries exactly the two optimal signed scalar phase choices.
The individual phase bounds exclude phase windings before scalar
uniqueness is applied. Critical angles and repeated levels are included.
-/

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open Set
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- Every local minimizing transporter has a complete signed optimal-phase
basis on its actual positive-gradient space. Source reflection gives the
paired negative-gradient basis. Each angle is the actual sine angle of
both vectors, and each sign is `+1` or `-1`. -/
theorem positive_gradient_optimal_phase_basis_of_isLocalMinOn_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) (U : unitary (E →L[ℂ] E))
    (hmap : K.map (Unitary.linearIsometryEquiv U).toLinearMap = L)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = L.starProjection}
      (U : E →L[ℂ] E)) :
    let H := Module.End.pointSpectralSubspace
      (schattenUnitaryGradient p.toReal (U : E →L[ℂ] E)).toLinearMap (Ioi 0)
    ∃ n : ℕ, ∃ (e : OrthonormalBasis (Fin n) ℂ H) (theta eps : Fin n → ℝ),
      (∀ i, theta i ∈ Ioo 0 (Real.pi / 2)) ∧
      (∀ i, eps i = 1 ∨ eps i = -1) ∧
      (∀ i, (U : E →L[ℂ] E) (e i : E) =
        Complex.exp (((theta i + eps i * optimalPhase p.toReal (theta i) : ℝ) : ℂ) *
          Complex.I) • (e i : E)) ∧
      (∀ i, (U : E →L[ℂ] E) (K.reflection (e i)) =
        Complex.exp (((-theta i + eps i * optimalPhase p.toReal (theta i) : ℝ) : ℂ) *
          Complex.I) • K.reflection (e i)) ∧
      (∀ i, K.sinAngleOperator L (e i : E) = (Real.sin (theta i) : ℂ) • (e i : E)) ∧
      (∀ i, K.sinAngleOperator L (K.reflection (e i)) =
        (Real.sin (theta i) : ℂ) • K.reflection (e i)) := by
  classical
  have ht := (map_eq_iff_conjugate_starProjection_complex K L U).mp hmap
  obtain ⟨n, e, _, alpha, beta, _, _, hu, hw, hmean, hcost, hbounds⟩ :=
    positive_gradient_phase_basis_of_isLocalMinOn_transports_complex
      p hp hp1 hp2 K L.starProjection U ht hmin
  let theta (i : Fin n) := (alpha i + beta i) / 2
  have hpair (i) :
      (alpha i = theta i + optimalPhase p.toReal (theta i) ∧
        beta i = theta i - optimalPhase p.toReal (theta i)) ∨
      (alpha i = theta i - optimalPhase p.toReal (theta i) ∧
        beta i = theta i + optimalPhase p.toReal (theta i)) := by
    have hc := hcost i
    rw [norm_one_sub_exp_eq_phaseChord (alpha i)
      ⟨(hbounds i).1.1.le, (hbounds i).1.2.le⟩,
      norm_one_sub_exp_neg_eq_phaseChord (beta i)
        ⟨(hbounds i).2.1.le, (hbounds i).2.2.le⟩] at hc
    exact (chord_pair_eq_minimum_iff_optimalPhase_signs p.toReal (theta i) (alpha i) (beta i)
      hp1 hp2 (hmean i).1 (hmean i).2 (hbounds i).1.1.le (hbounds i).2.1.le
      (by dsimp [theta]; ring)).mp hc
  let eps (i : Fin n) := if alpha i = theta i + optimalPhase p.toReal (theta i) then (1 : ℝ) else -1
  have hα (i) : alpha i = theta i + eps i * optimalPhase p.toReal (theta i) := by
    by_cases h : alpha i = theta i + optimalPhase p.toReal (theta i)
    · simpa only [eps, ite_eq_left h, one_mul] using h
    · rcases hpair i with hpair | hpair
      · exact (h hpair.1).elim
      · simpa only [eps, ite_eq_right h, neg_one_mul, sub_eq_add_neg] using hpair.1
  have hβ (i) : beta i = theta i - eps i * optimalPhase p.toReal (theta i) := by
    have hsum : alpha i + beta i = 2 * theta i := by dsimp [theta]; ring
    linarith [hα i]
  refine ⟨n, e, theta, eps, hmean, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    dsimp only [eps]
    split_ifs <;> simp
  · intro i
    rw [hu, hα]
  · intro i
    have hminus : -beta i = -theta i + eps i * optimalPhase p.toReal (theta i) := by
      rw [hβ]
      ring
    rw [hw, hminus]
  · intro i
    exact (Submodule.sinAngleOperator_apply_of_paired_phase_eigenvectors_complex
      K L (Unitary.linearIsometryEquiv U) hmap (e i) (alpha i) (beta i) (hu i) (hw i)
      ⟨(hmean i).1.le, (hmean i).2.le⟩).1
  · intro i
    exact (Submodule.sinAngleOperator_apply_of_paired_phase_eigenvectors_complex
      K L (Unitary.linearIsometryEquiv U) hmap (e i) (alpha i) (beta i) (hu i) (hw i)
      ⟨(hmean i).1.le, (hmean i).2.le⟩).2

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

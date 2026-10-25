/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.SchattenEqualAngleCompatibility
import DavisKahan.FiniteDimensional.DirectRotation.SchattenFixedDirections

/-!
# Weighted canonical commutation without acuteness

The cosine-weighted relative phase of every ambient local minimum commutes
with canonical rotation, even when right angles occur. Interior angle
spaces use the intrinsic commutation theorem. The cosine annihilates the
right-angle sector; both transporters fix zero-angle directions.
-/

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open Set
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- The cosine-weighted relative phase commutes with canonical rotation
on the whole space, with every angle and multiplicity allowed. -/
theorem cosine_mul_relative_phase_commutes_canonical_of_isLocalMinOn_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L)
    (U : unitary (E →L[ℂ] E))
    (hmap : K.map (Unitary.linearIsometryEquiv U).toLinearMap = L)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = L.starProjection}
      (U : E →L[ℂ] E)) :
    let R := nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL)
    let C := Proposition35.section3CosAngleOperator K L
    Commute (C * (star R * (U : E →L[ℂ] E))) R := by
  let D := finiteCrossedDefectEquiv K L hKL
  let R := nonacuteDirectRotation K L D
  let C := Proposition35.section3CosAngleOperator K L
  let Z := star R * (U : E →L[ℂ] E)
  have hRC : Commute R C := by
    change Commute R (Proposition35.section3CosAngleOperator K L)
    rw [Proposition35.section3CosAngleOperator_eq_canonicalAbsoluteValue]
    exact nonacuteDirectRotation_comm_absoluteValue K L D
  have hZC : Commute Z C :=
    Proposition35.commute_section3CosAngleOperator_of_commute_sinAngleOperator K L Z
      (relative_phase_commute_sinAngleOperator_of_isLocalMinOn_complex
        p hp hp1 hp2 K L U hmap hmin D)
  obtain ⟨n, m, e, theta, hθ, hC0, hC1, hCf, hR0, hR1, hRf, _⟩ :=
    SmoothedPhaseTransition.exists_subspace_paired_rotation_basis K L hKL
  change ∀ i, R (e (.inl (0, i))) =
    Complex.exp ((theta i : ℂ) * Complex.I) • e (.inl (0, i)) at hR0
  change ∀ i, R (e (.inl (1, i))) =
    Complex.exp (((-theta i : ℝ) : ℂ) * Complex.I) • e (.inl (1, i)) at hR1
  change ∀ j, R (e (.inr j)) = e (.inr j) at hRf
  have hpair (v : E) (angle : ℝ) (ha : angle ∈ Ioc 0 (Real.pi / 2))
      (a : ℂ) (hCv : C v = (Real.cos angle : ℂ) • v) (hRv : R v = a • v) :
      C (Z (R v)) = R (C (Z v)) := by
    by_cases hi : angle < Real.pi / 2
    · have hS := Proposition35.sine_apply_of_cosine_apply K L v angle ⟨ha.1.le, ha.2⟩ hCv
      have hcomm := relative_phase_commutes_canonical_on_angle_of_isLocalMinOn_complex
        p hp hp1 hp2 K L U hmap hmin D angle ⟨ha.1, hi⟩ v hS
      change Z (R v) = R (Z v) at hcomm
      calc
        _ = C (R (Z v)) := congrArg C hcomm
        _ = _ := (congrArg (fun A : E →L[ℂ] E => A (Z v)) hRC.eq).symm
    · have heq : angle = Real.pi / 2 := le_antisymm ha.2 (le_of_not_gt hi)
      have hCzero : C v = 0 := by simpa only [heq, Real.cos_pi_div_two,
        Complex.ofReal_zero, zero_smul] using hCv
      have hCZ : C (Z v) = 0 := by
        have h := congrArg (fun A : E →L[ℂ] E => A v) hZC.eq
        change Z (C v) = C (Z v) at h
        rw [hCzero, map_zero] at h
        exact h.symm
      rw [hRv, map_smul, map_smul, hCZ, smul_zero, map_zero]
  apply ContinuousLinearMap.coe_injective
  apply e.toBasis.ext
  intro j
  change C (Z (R (e j))) = R (C (Z (e j)))
  rcases j with ⟨r, i⟩ | j
  · fin_cases r
    · exact hpair _ _ (hθ i) _ (hC0 i) (hR0 i)
    · exact hpair _ _ (hθ i) _ (hC1 i) (hR1 i)
  · have hS : K.sinAngleOperator L (e (.inr j)) = 0 := by
      have h := Proposition35.sine_apply_of_cosine_apply K L (e (.inr j)) 0
        ⟨le_rfl, by linarith [Real.pi_pos]⟩ (by simpa only [Real.cos_zero,
          RCLike.ofReal_one, Complex.ofReal_one, one_smul] using hCf j)
      simpa only [Real.sin_zero, RCLike.ofReal_zero, Complex.ofReal_zero, zero_smul] using h
    have hPQ : K.starProjection (e (.inr j)) = L.starProjection (e (.inr j)) := by
      have h := K.norm_sinAngleOperator_apply L (e (.inr j))
      rw [hS, norm_zero] at h
      exact sub_eq_zero.mp (norm_eq_zero.mp h.symm)
    have hUfix := apply_eq_self_of_projections_eq_of_isLocalMinOn_transports_complex
      p hp hp1 hp2 K L U hmap hmin _ hPQ
    have hRstar := unitary_star_apply_of_apply_eq_smul
      (⟨R, nonacuteDirectRotation_mem_unitary K L D⟩ : unitary (E →L[ℂ] E))
      (1 : ℂ) (by simp) (e (.inr j)) (by simpa only [one_smul] using hRf j)
    have hZfix : Z (e (.inr j)) = e (.inr j) := by
      change star R ((U : E →L[ℂ] E) (e (.inr j))) = _
      rw [hUfix]
      simpa only [star_one, one_smul] using hRstar
    rw [hRf, hZfix, hCf, hRf]

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

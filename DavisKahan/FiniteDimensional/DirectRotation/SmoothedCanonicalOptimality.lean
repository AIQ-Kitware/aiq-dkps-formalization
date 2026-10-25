/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedQuarticStability

/-!
# Exact canonical optimality cutoff for complex smoothed transport

The canonical rotation is globally optimal exactly when every accepted
principal angle lies at or below the explicit smoothed cutoff. Uniqueness
through equality follows from the quartic certificate. Above the cutoff,
the explicitly defined spectral-phase optimizer strictly improves its cost.

Necessity compares the actual canonical nuclear trace with the attained
minimum. Every scalar gap is nonnegative, so equality forces each nonzero
angle into the canonical regime; the paired-angle trace bridge then gives
the statement for the accepted principal angles, including the extra zeros.
-/

public section

noncomputable section
namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition
open scoped InnerProductSpace

private theorem weightedPhaseCost_zero_eq_minimum_iff
    (a b theta : ℝ) (hb : 0 < b) (hab : b ≤ a)
    (hθ : theta ∈ Set.Icc 0 (Real.pi / 2)) :
    weightedPhaseCost a b theta 0 = weightedPhaseMinimum a b theta ↔
      b ≤ a * Real.cos theta := by
  rw [weightedPhaseCost_eq_minimum_iff a b theta 0 hb hab hθ ⟨le_rfl, hθ.1⟩]
  unfold optimalWeightedPhase
  split_ifs with hc
  · simp [hc]
  · have hpos : 0 < Real.arccos (a * Real.cos theta / b) :=
      Real.arccos_pos.mpr ((div_lt_one hb).mpr (lt_of_not_ge hc))
    simp [hc, (ne_of_gt hpos).symm]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

attribute [local instance 100] ContinuousLinearMap.realAlgebra
  ContinuousLinearMap.realIsScalarTower ContinuousLinearMap.continuousFunctionalCalculusReal
attribute [local instance] ContinuousLinearMap.instStarOrderedRingRCLike

omit [CompleteSpace E] in
private theorem nuclear_identity_phase_formula {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a b : ℝ) (hab : b ≤ a) (theta : ι → ℝ)
    (e : OrthonormalBasis ((Fin 2 × ι) ⊕ κ) ℂ E) (A : E →ₗ[ℂ] E)
    (hA0 : ∀ i, A (e (.inl (0, i))) =
      (((a * Real.cos (theta i) : ℝ) : ℂ) + (a * Real.sin (theta i)) * Complex.I) •
        e (.inl (0, i)))
    (hA1 : ∀ i, A (e (.inl (1, i))) =
      (((a * Real.cos (theta i) : ℝ) : ℂ) - (a * Real.sin (theta i)) * Complex.I) •
        e (.inl (1, i)))
    (hAf : ∀ j, A (e (.inr j)) = (a : ℂ) • e (.inr j)) :
    UnitarilyInvariantSeminorm.nuclear ℂ E E (A - (b : ℂ) • LinearMap.id) =
      (∑ i, weightedPhaseCost a b (theta i) 0) + Fintype.card κ * (a - b) := by
  exact nuclear_diagonalPhase_eq_sum_weightedPhaseCost a b hab theta (fun _ => 0) e A
    (LinearIsometryEquiv.refl ℂ E) hA0 hA1 hAf (by intro r i; simp [circlePhase])
    (by intro j; rfl)

set_option maxHeartbeats 600000 in
/-- Global optimality of the canonical rotation forces every accepted
principal angle into the exact canonical regime. -/
theorem principalAngles_le_cutoff_of_canonical_isMin
    (tau : ℝ) (hτ : 0 < tau) (U V : Submodule ℂ E)
    (hUV : Module.finrank ℂ U = Module.finrank ℂ V) :
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation U V (finiteCrossedDefectEquiv U V hUV),
        nonacuteDirectRotation_mem_unitary U V (finiteCrossedDefectEquiv U V hUV)⟩ :
          unitary (E →L[ℂ] E))
    (∀ T : E ≃ₗᵢ[ℂ] E, U.map T.toLinearMap = V →
      smoothedDisplacementCost tau R.toLinearMap ≤ smoothedDisplacementCost tau T.toLinearMap) →
      ∀ i : Fin (Module.finrank ℂ U), U.principalAngles V i ≤ smoothedCriticalAngle tau := by
  let a := smoothingRadius tau
  let b := a⁻¹
  have ha := one_lt_smoothingRadius tau hτ
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have hb : 0 < b := inv_pos.mpr ha0
  have hab : b < a := lt_trans ((inv_lt_one₀ ha0).mpr ha) ha
  let D := finiteCrossedDefectEquiv U V hUV
  let Rop := nonacuteDirectRotation U V D
  let R := Unitary.linearIsometryEquiv
    (⟨Rop, nonacuteDirectRotation_mem_unitary U V D⟩ : unitary (E →L[ℂ] E))
  obtain ⟨n, m, e, theta, hθ, hC0, hC1, hCf, hR0, hR1, hRf, hJ0⟩ :=
    exists_subspace_paired_rotation_basis U V hUV
  let A := (a : ℂ) • R.toLinearMap
  have hA0 (i) : A (e (.inl (0, i))) =
      (((a * Real.cos (theta i) : ℝ) : ℂ) + (a * Real.sin (theta i)) * Complex.I) •
        e (.inl (0, i)) := by
    change (a : ℂ) • R (e (.inl (0, i))) = _
    have hr : R (e (.inl (0, i))) =
        Complex.exp ((theta i : ℂ) * Complex.I) • e (.inl (0, i)) := hR0 i
    rw [hr, smul_smul, Complex.exp_ofReal_mul_I]
    congr 1
    push_cast
    ring
  have hA1 (i) : A (e (.inl (1, i))) =
      (((a * Real.cos (theta i) : ℝ) : ℂ) - (a * Real.sin (theta i)) * Complex.I) •
        e (.inl (1, i)) := by
    change (a : ℂ) • R (e (.inl (1, i))) = _
    have hr : R (e (.inl (1, i))) =
        Complex.exp ((-theta i : ℝ) * Complex.I) • e (.inl (1, i)) := hR1 i
    rw [hr, smul_smul, Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
    congr 1
    push_cast
    ring
  have hAf (j) : A (e (.inr j)) = (a : ℂ) • e (.inr j) := by
    change (a : ℂ) • R (e (.inr j)) = _
    rw [show R (e (.inr j)) = e (.inr j) from hRf j]
  dsimp only
  intro hmin
  have hRmap : U.map R.toLinearMap = V :=
    (U.map_eq_iff_intertwines_reflection V R).mpr
      (nonacuteDirectRotation_reflection_intertwines U V D)
  obtain ⟨W, hWmap, hWcost, hWmin⟩ :=
    exists_unitary_minimizing_smoothed_transport tau hτ U V hUV
  have hcosteq : smoothedDisplacementCost tau R.toLinearMap = smoothedTransportMinimum tau U V := by
    apply le_antisymm
    · exact (hmin W hWmap).trans hWcost.le
    · rw [← hWcost]
      exact hWmin R hRmap
  have hcostR : smoothedDisplacementCost tau R.toLinearMap =
      UnitarilyInvariantSeminorm.nuclear ℂ E E
        ((a : ℂ) • R.toLinearMap - (b : ℂ) • LinearMap.id) - Module.finrank ℂ E * tau :=
    smoothedDisplacementCost_eq_weightedNuclear tau hτ (Unitary.linearIsometryEquiv.symm R)
  let C := Proposition35.section3CosAngleOperator U V
  have hC : IsSelfAdjoint C :=
    ((ContinuousLinearMap.nonneg_iff_isPositive).mp
      (Proposition35.section3CosAngleOperator_nonneg U V)).isSelfAdjoint
  let : IsStarNormal C := hC.isStarNormal
  have hpaired := weightedRotationMinimum_eq_paired_sum a b hab.le C theta hθ e hC0 hC1 hCf
  have hcanonical := nuclear_identity_phase_formula a b hab.le theta e A hA0 hA1 hAf
  rw [hcostR] at hcosteq
  change UnitarilyInvariantSeminorm.nuclear ℂ E E (A - (b : ℂ) • LinearMap.id) - _ =
    weightedRotationMinimum a b C - _ at hcosteq
  rw [hcanonical, hpaired] at hcosteq
  simp only [Fintype.card_fin] at hcosteq
  have heq : (∑ i, weightedPhaseCost a b (theta i) 0) =
      ∑ i, weightedPhaseMinimum a b (theta i) := by linarith
  have hnonneg (i : Fin n) : 0 ≤ weightedPhaseCost a b (theta i) 0 - weightedPhaseMinimum a b (theta i) :=
    sub_nonneg.mpr (weightedPhaseMinimum_le_cost a b (theta i) ha0.le hb.le
      ⟨(hθ i).1.le, (hθ i).2⟩ 0)
  have hsum : (∑ i, (weightedPhaseCost a b (theta i) 0 - weightedPhaseMinimum a b (theta i))) = 0 := by
    rw [Finset.sum_sub_distrib, heq, sub_self]
  have hsub (i) : b ≤ a * Real.cos (theta i) := by
    have hle := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => hnonneg j) (Finset.mem_univ i)
    rw [hsum] at hle
    have hz := sub_eq_zero.mp (le_antisymm hle (hnonneg i))
    exact (weightedPhaseCost_zero_eq_minimum_iff a b (theta i) hb hab.le
      ⟨(hθ i).1.le, (hθ i).2⟩).mp hz
  apply principalAngles_le_of_paired_angles_le U V e theta hθ hC0 hC1 hCf hJ0
    (smoothedCriticalAngle tau) (smoothedCriticalAngle_mem_Icc tau).1
  intro i
  have hratio : b / a ≤ Real.cos (theta i) := (div_le_iff₀ ha0).mpr (by simpa only [mul_comm] using hsub i)
  have hratio' : (a⁻¹) ^ 2 ≤ Real.cos (theta i) := by
    dsimp only [b] at hratio
    convert hratio using 1
    field_simp
  have hangle := Real.arccos_le_arccos hratio'
  rw [Real.arccos_cos (hθ i).1.le (by linarith [(hθ i).2, Real.pi_pos])] at hangle
  exact hangle

/-- The canonical rotation is globally optimal exactly at the explicit
angle cutoff, with no supplied coordinates or no-mixing hypothesis. -/
theorem smoothed_canonical_isMin_iff
    (tau : ℝ) (hτ : 0 < tau) (U V : Submodule ℂ E)
    (hUV : Module.finrank ℂ U = Module.finrank ℂ V) :
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation U V (finiteCrossedDefectEquiv U V hUV),
        nonacuteDirectRotation_mem_unitary U V (finiteCrossedDefectEquiv U V hUV)⟩ :
          unitary (E →L[ℂ] E))
    (∀ T : E ≃ₗᵢ[ℂ] E, U.map T.toLinearMap = V →
      smoothedDisplacementCost tau R.toLinearMap ≤ smoothedDisplacementCost tau T.toLinearMap) ↔
      ∀ i : Fin (Module.finrank ℂ U), U.principalAngles V i ≤ smoothedCriticalAngle tau := by
  constructor
  · exact principalAngles_le_cutoff_of_canonical_isMin tau hτ U V hUV
  · intro hmax T hT
    exact ((smoothed_canonical_unique_minimizer tau hτ U V hUV hmax).2 T hT).1

/-- Whenever an accepted principal angle exceeds the cutoff, the named
spectral-phase optimizer strictly improves the canonical rotation. -/
theorem optimalSmoothedTransport_lt_canonical_of_supercritical
    (tau : ℝ) (hτ : 0 < tau) (U V : Submodule ℂ E)
    (hUV : Module.finrank ℂ U = Module.finrank ℂ V)
    (i : Fin (Module.finrank ℂ U))
    (hi : smoothedCriticalAngle tau < U.principalAngles V i) :
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation U V (finiteCrossedDefectEquiv U V hUV),
        nonacuteDirectRotation_mem_unitary U V (finiteCrossedDefectEquiv U V hUV)⟩ :
          unitary (E →L[ℂ] E))
    smoothedDisplacementCost tau (optimalSmoothedTransport tau U V hUV).toLinearMap <
      smoothedDisplacementCost tau R.toLinearMap := by
  dsimp only
  by_contra h
  have hcan : ∀ T : E ≃ₗᵢ[ℂ] E, U.map T.toLinearMap = V →
      smoothedDisplacementCost tau
          (Unitary.linearIsometryEquiv
            (⟨nonacuteDirectRotation U V (finiteCrossedDefectEquiv U V hUV),
              nonacuteDirectRotation_mem_unitary U V (finiteCrossedDefectEquiv U V hUV)⟩ :
                unitary (E →L[ℂ] E))).toLinearMap ≤
        smoothedDisplacementCost tau T.toLinearMap := fun T hT =>
    (le_of_not_gt h).trans (optimalSmoothedTransport_isMin tau hτ U V hUV T hT)
  have hmax := (smoothed_canonical_isMin_iff tau hτ U V hUV).mp hcan
  exact not_le_of_gt hi (hmax i)

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

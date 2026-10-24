/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.SmoothedOptimizerCertificate
import DavisKahan.FiniteDimensional.DirectRotation.SmoothedSubspaceOptimization
import DavisKahan.FiniteDimensional.DirectRotation.SmoothedQuarticStability

/-!
# An equality certificate for every weighted transport optimizer

The paired coordinates and dual unitary are derived from the original
subspaces. Every ambient unitary transporter attains the known exact minimum
if and only if its relative displacement satisfies the certificate equality
conditions. Every such optimizer agrees with direct rotation on the strict
subcritical and critical directions and fixes the canonical fixed directions.

The remaining positive-displacement equation is not yet a parametrization
of all supercritical solutions by spectral projections.
-/

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- Necessary and sufficient optimality conditions for every ambient
weighted nuclear transporter, with its certificate coordinates constructed
from the given pair. In particular every optimizer fixes the fixed directions
and agrees with the canonical rotation on every subcritical or critical plane. -/
theorem exists_paired_certificate_for_weighted_transport_complex
    (a b : ℝ) (hb : 0 < b) (hab : b < a)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L)
    (T : E ≃ₗᵢ[ℂ] E) (hT : K.map T.toLinearMap = L) :
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
        nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
          unitary (E →L[ℂ] E))
    let Z := R.trans T.symm
    ∃ n m : ℕ, ∃ (e : OrthonormalBasis ((Fin 2 × Fin n) ⊕ Fin m) ℂ E)
      (theta : Fin n → ℝ) (V : E ≃ₗᵢ[ℂ] E),
      (∀ i, theta i ∈ Set.Ioc 0 (Real.pi / 2)) ∧
      (∀ i, R (e (.inl (0, i))) =
        Complex.exp ((theta i : ℂ) * Complex.I) • e (.inl (0, i))) ∧
      (∀ i, R (e (.inl (1, i))) =
        Complex.exp ((-theta i : ℝ) * Complex.I) • e (.inl (1, i))) ∧
      (∀ j, R (e (.inr j)) = e (.inr j)) ∧
      (∀ i, K.reflection (e (.inl (0, i))) = e (.inl (1, i))) ∧
      (∀ j, V (e j) = pairedDualPhase a b theta j • e j) ∧
      (∀ i, Proposition35.section3CosAngleOperator K L (e (.inl (0, i))) =
        (Real.cos (theta i) : ℂ) • e (.inl (0, i))) ∧
      (∀ i, Proposition35.section3CosAngleOperator K L (e (.inl (1, i))) =
        (Real.cos (theta i) : ℂ) • e (.inl (1, i))) ∧
      (∀ j, Proposition35.section3CosAngleOperator K L (e (.inr j)) = e (.inr j)) ∧
      (UnitarilyInvariantSeminorm.nuclear ℂ E E
          ((a : ℂ) • T.toLinearMap - (b : ℂ) • LinearMap.id) =
            weightedRotationMinimum a b (Proposition35.section3CosAngleOperator K L) ↔
        weightedDiagonalDefect a b theta e Z.toLinearMap = 0 ∧
          (V.symm.toLinearMap ∘ₗ
            ((a : ℂ) • R.toLinearMap - (b : ℂ) • Z.toLinearMap)).IsPositive) ∧
      (UnitarilyInvariantSeminorm.nuclear ℂ E E
          ((a : ℂ) • T.toLinearMap - (b : ℂ) • LinearMap.id) =
            weightedRotationMinimum a b (Proposition35.section3CosAngleOperator K L) →
        (∀ i, b ≤ a * Real.cos (theta i) → ∀ r : Fin 2,
          T (e (.inl (r, i))) = R (e (.inl (r, i)))) ∧
          ∀ j, T (e (.inr j)) = e (.inr j)) := by
  classical
  let D := finiteCrossedDefectEquiv K L hKL
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L D, nonacuteDirectRotation_mem_unitary K L D⟩ :
      unitary (E →L[ℂ] E))
  let Z := R.trans T.symm
  let C := Proposition35.section3CosAngleOperator K L
  obtain ⟨n, m, e, theta, hθ, hC0, hC1, hCf, hR0, hR1, hRf, hJ0⟩ :=
    exists_subspace_paired_rotation_basis K L hKL
  have hC : IsSelfAdjoint C :=
    ((ContinuousLinearMap.nonneg_iff_isPositive).mp
      (Proposition35.section3CosAngleOperator_nonneg K L)).isSelfAdjoint
  let : IsStarNormal C := hC.isStarNormal
  have hvalue := weightedRotationMinimum_eq_paired_sum a b hab.le C theta hθ e hC0 hC1 hCf
  let A := (a : ℂ) • R.toLinearMap
  have hA0 (i) : A (e (.inl (0, i))) =
      (((a * Real.cos (theta i) : ℝ) : ℂ) + (a * Real.sin (theta i)) * Complex.I) •
        e (.inl (0, i)) := by
    change (a : ℂ) • R (e (.inl (0, i))) = _
    rw [show R (e (.inl (0, i))) = _ from hR0 i, smul_smul, Complex.exp_ofReal_mul_I]
    congr 1
    push_cast
    ring
  have hA1 (i) : A (e (.inl (1, i))) =
      (((a * Real.cos (theta i) : ℝ) : ℂ) - (a * Real.sin (theta i)) * Complex.I) •
        e (.inl (1, i)) := by
    change (a : ℂ) • R (e (.inl (1, i))) = _
    rw [show R (e (.inl (1, i))) = _ from hR1 i, smul_smul,
      Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
    congr 1
    push_cast
    ring
  have hAf (j) : A (e (.inr j)) = (a : ℂ) • e (.inr j) := by
    change (a : ℂ) • R (e (.inr j)) = _
    rw [show R (e (.inr j)) = _ from hRf j]
  have hRref (x : E) : R (K.reflection x) = L.reflection (R x) :=
    nonacuteDirectRotation_reflection_intertwines K L D x
  have hTref := (Submodule.map_eq_iff_intertwines_reflection K L T).mp hT
  have hcomm (x : E) : Z (K.reflection x) = K.reflection (Z x) := by
    apply T.injective
    change T (T.symm (R (K.reflection x))) = T (K.reflection (T.symm (R x)))
    rw [T.apply_symm_apply, hTref, T.apply_symm_apply, hRref]
  have hdiag (i) : (⟪e (.inl (0, i)), Z (e (.inl (0, i)))⟫_ℂ).im =
      (⟪e (.inl (1, i)), Z (e (.inl (1, i)))⟫_ℂ).im := by
    have h := inner_diagonal_eq_of_commute K.reflection Z.toLinearMap hcomm (e (.inl (0, i)))
    rw [hJ0] at h
    exact (congrArg Complex.im h).symm
  have hZ (j) : ‖Z.toLinearMap (e j)‖ ≤ 1 := by
    change ‖Z (e j)‖ ≤ 1
    rw [Z.norm_map, e.norm_eq_one]
  have hfactor : A - (b : ℂ) • Z.toLinearMap =
      ((a : ℂ) • T.toLinearMap - (b : ℂ) • LinearMap.id) ∘ₗ Z.toLinearMap := by
    ext x
    simp [A, Z]
  have hN : UnitarilyInvariantSeminorm.nuclear ℂ E E (A - (b : ℂ) • Z.toLinearMap) =
      UnitarilyInvariantSeminorm.nuclear ℂ E E
        ((a : ℂ) • T.toLinearMap - (b : ℂ) • LinearMap.id) := by
    rw [hfactor]
    exact (UnitarilyInvariantSeminorm.nuclear ℂ E E).map_comp_linearIsometryEquiv Z _
  obtain ⟨V, hV⟩ := e.exists_linearIsometryEquiv_apply_eq_smul
    (pairedDualPhase a b theta) (norm_pairedDualPhase a b hb.le hab theta)
  have hcert := weightedNuclear_eq_minimum_iff_certificate_complex a b hb hab theta e A Z.toLinearMap
    hA0 hA1 hAf hZ hdiag V hV
  rw [hN, Fintype.card_fin, ← hvalue] at hcert
  refine ⟨n, m, e, theta, V, hθ, hR0, hR1, hRf, hJ0, hV, hC0, hC1, hCf, hcert, ?_⟩
  intro hatt
  have hattcert := hcert.mp hatt
  have hfixed := (weightedDiagonalDefect_eq_zero_iff_fixed_complex a b theta e Z.toLinearMap hZ).mp
    hattcert.1
  have hfix (j) (hj : Z.toLinearMap (e j) = e j) : T (e j) = R (e j) := by
    have h := congrArg T hj
    change T (T.symm (R (e j))) = T (e j) at h
    rw [T.apply_symm_apply] at h
    exact h.symm
  refine ⟨?_, ?_⟩
  · intro i hi r
    apply hfix
    rcases lt_or_eq_of_le hi with hlt | heq
    · exact hfixed.1 i (dualReal_pos_of_lt a b (theta i) hb.le hab hlt) r
    · exact apply_eq_self_of_critical_certificate_complex a b hb hab theta hθ e A Z.toLinearMap
        hA0 hA1 hZ V hV hattcert.2 i heq r
  intro j
  exact (hfix _ (hfixed.2 j)).trans (hRf j)

/-- Every global minimizer of the literal Charbonnier cost attains the
known weighted nuclear value, with the ambient constant removed exactly. -/
theorem smoothed_minimizer_weighted_cost_eq_complex
    (tau : ℝ) (htau : 0 < tau)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L)
    (T : E ≃ₗᵢ[ℂ] E) (hT : K.map T.toLinearMap = L)
    (hmin : ∀ S : E ≃ₗᵢ[ℂ] E, K.map S.toLinearMap = L →
      smoothedDisplacementCost tau T.toLinearMap ≤ smoothedDisplacementCost tau S.toLinearMap) :
    UnitarilyInvariantSeminorm.nuclear ℂ E E
      ((smoothingRadius tau : ℂ) • T.toLinearMap -
        (((smoothingRadius tau)⁻¹ : ℝ) : ℂ) • LinearMap.id) =
      weightedRotationMinimum (smoothingRadius tau) (smoothingRadius tau)⁻¹
        (Proposition35.section3CosAngleOperator K L) := by
  obtain ⟨W, hWmap, hWcost, hWmin⟩ :=
    exists_unitary_minimizing_smoothed_transport tau htau K L hKL
  have hatt := (le_antisymm (hmin W hWmap) (hWmin T hT)).trans hWcost
  have hcost := smoothedDisplacementCost_eq_weightedNuclear tau htau
    (Unitary.linearIsometryEquiv.symm T)
  change smoothedDisplacementCost tau T.toLinearMap =
    UnitarilyInvariantSeminorm.nuclear ℂ E E
      ((smoothingRadius tau : ℂ) • T.toLinearMap -
        (((smoothingRadius tau)⁻¹ : ℝ) : ℂ) • LinearMap.id) -
      Module.finrank ℂ E * tau at hcost
  rw [hcost, smoothedTransportMinimum] at hatt
  linarith only [hatt]

/-- Every global minimizer of the literal Charbonnier displacement cost
agrees with direct rotation on all planes at or below the cutoff, even
when other angles are supercritical. It fixes every canonical fixed
direction. The original ambient transporter is unrestricted. -/
theorem smoothed_minimizer_agrees_with_canonical_on_subcritical_planes_complex
    (tau : ℝ) (htau : 0 < tau)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L)
    (T : E ≃ₗᵢ[ℂ] E) (hT : K.map T.toLinearMap = L)
    (hmin : ∀ S : E ≃ₗᵢ[ℂ] E, K.map S.toLinearMap = L →
      smoothedDisplacementCost tau T.toLinearMap ≤ smoothedDisplacementCost tau S.toLinearMap) :
    let R := nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL)
    ∃ n m : ℕ, ∃ (e : OrthonormalBasis ((Fin 2 × Fin n) ⊕ Fin m) ℂ E)
      (theta : Fin n → ℝ),
      (∀ i, theta i ∈ Set.Ioc 0 (Real.pi / 2)) ∧
      (∀ i, R (e (.inl (0, i))) =
        Complex.exp ((theta i : ℂ) * Complex.I) • e (.inl (0, i))) ∧
      (∀ i, R (e (.inl (1, i))) =
        Complex.exp ((-theta i : ℝ) * Complex.I) • e (.inl (1, i))) ∧
      (∀ j, R (e (.inr j)) = e (.inr j)) ∧
      (∀ i, theta i ≤ smoothedCriticalAngle tau → ∀ r : Fin 2,
        T (e (.inl (r, i))) = R (e (.inl (r, i)))) ∧
      ∀ j, T (e (.inr j)) = e (.inr j) := by
  let a := smoothingRadius tau
  have ha : 1 < a := one_lt_smoothingRadius tau htau
  have ha0 : 0 < a := zero_lt_one.trans ha
  have hab : a⁻¹ < a := ((inv_lt_one₀ ha0).mpr ha).trans ha
  obtain ⟨W, hWmap, hWcost, hWmin⟩ :=
    exists_unitary_minimizing_smoothed_transport tau htau K L hKL
  have hatt := (le_antisymm (hmin W hWmap) (hWmin T hT)).trans hWcost
  have hcost := smoothedDisplacementCost_eq_weightedNuclear tau htau
    (Unitary.linearIsometryEquiv.symm T)
  change smoothedDisplacementCost tau T.toLinearMap =
    UnitarilyInvariantSeminorm.nuclear ℂ E E
      ((a : ℂ) • T.toLinearMap - ((a⁻¹ : ℝ) : ℂ) • LinearMap.id) -
        Module.finrank ℂ E * tau at hcost
  rw [hcost, smoothedTransportMinimum] at hatt
  have hweighted : UnitarilyInvariantSeminorm.nuclear ℂ E E
      ((a : ℂ) • T.toLinearMap - ((a⁻¹ : ℝ) : ℂ) • LinearMap.id) =
      weightedRotationMinimum a a⁻¹ (Proposition35.section3CosAngleOperator K L) := by
    linarith only [hatt]
  obtain ⟨n, m, e, theta, V, hθ, hR0, hR1, hRf, _, _, _, _, _, _, hfixed⟩ :=
    exists_paired_certificate_for_weighted_transport_complex a a⁻¹
      (inv_pos.mpr ha0) hab K L hKL T hT
  have hfix := hfixed hweighted
  refine ⟨n, m, e, theta, hθ, hR0, hR1, hRf, ?_, hfix.2⟩
  intro i hi
  apply hfix.1 i
  have hc := smoothedCriticalAngle_mem_Icc tau
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi (hθ i).1.le
    (by linarith [hc.2, Real.pi_pos]) hi
  rw [cos_smoothedCriticalAngle tau htau] at hcos
  have hprod : a * (a⁻¹) ^ 2 = a⁻¹ := by
    rw [pow_two, ← mul_assoc, mul_inv_cancel₀ ha0.ne', one_mul]
  have h := mul_le_mul_of_nonneg_left hcos ha0.le
  change a * (a⁻¹) ^ 2 ≤ a * Real.cos (theta i) at h
  rwa [hprod] at h

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

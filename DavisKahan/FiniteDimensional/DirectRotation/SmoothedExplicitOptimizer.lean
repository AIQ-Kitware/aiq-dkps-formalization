/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.SmoothedFunctionalPhase
import DavisKahan.FiniteDimensional.DirectRotation.SmoothedPrincipalAngles

/-!
# An explicit optimal smoothed transport

The optimizer is the canonical rotation followed by the adjoint of a
spectral phase factor of the positive cosine operator. Its definition
uses neither a chosen principal basis nor an existential minimizer.
-/

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

attribute [local instance 100] ContinuousLinearMap.realAlgebra
  ContinuousLinearMap.realIsScalarTower ContinuousLinearMap.continuousFunctionalCalculusReal
attribute [local instance] ContinuousLinearMap.instStarOrderedRingRCLike

/-- The spectral optimal phase factor for a subspace pair, as an actual
ambient unitary. The definition is meaningful for arbitrary real weights. -/
def subspaceWeightedPhase (a b : ℝ) (U V : Submodule ℂ E) : unitary (E →L[ℂ] E) :=
  ⟨weightedPhaseFactor a b (Proposition35.section3CosAngleOperator U V),
    weightedPhaseFactor_mem_unitary a b _
      ((ContinuousLinearMap.nonneg_iff_isPositive).mp
        (Proposition35.section3CosAngleOperator_nonneg U V)).isSelfAdjoint.isStarNormal⟩

/-- The explicitly defined optimal transport: canonical rotation composed
with the adjoint of its spectral phase correction. -/
def optimalWeightedTransport (a b : ℝ) (U V : Submodule ℂ E)
    (hUV : Module.finrank ℂ U = Module.finrank ℂ V) : E ≃ₗᵢ[ℂ] E :=
  (Unitary.linearIsometryEquiv (subspaceWeightedPhase a b U V)).symm.trans
    (Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation U V (finiteCrossedDefectEquiv U V hUV),
        nonacuteDirectRotation_mem_unitary U V (finiteCrossedDefectEquiv U V hUV)⟩ :
          unitary (E →L[ℂ] E)))

/-- The named optimizer is exactly the displayed operator formula, with
the positive-cosine spectral phase and the completed canonical rotation. -/
theorem optimalWeightedTransport_toContinuousLinearMap (a b : ℝ)
    (U V : Submodule ℂ E) (hUV : Module.finrank ℂ U = Module.finrank ℂ V) :
    (optimalWeightedTransport a b U V hUV : E →L[ℂ] E) =
      nonacuteDirectRotation U V (finiteCrossedDefectEquiv U V hUV) *
        star (weightedPhaseFactor a b (Proposition35.section3CosAngleOperator U V)) := by
  rfl

/-- The phase correction preserves the source reflection and hence the
source subspace and its orthogonal complement. -/
theorem subspaceWeightedPhase_commutes_reflection (a b : ℝ) (U V : Submodule ℂ E)
    (x : E) :
    (subspaceWeightedPhase a b U V : E →L[ℂ] E) (U.reflection x) =
      U.reflection ((subspaceWeightedPhase a b U V : E →L[ℂ] E) x) := by
  let C := Proposition35.section3CosAngleOperator U V
  have hC : IsSelfAdjoint C :=
    ((ContinuousLinearMap.nonneg_iff_isPositive).mp
      (Proposition35.section3CosAngleOperator_nonneg U V)).isSelfAdjoint
  have hCP : Commute C U.starProjection :=
    Commute.cfc_real (Proposition35.section3AngleOperator_comm_projection U V) Real.cos
  have hZP := hC.commute_cfc hCP (weightedPhaseSymbol a b)
  have hP (y : E) :
      (subspaceWeightedPhase a b U V : E →L[ℂ] E) (U.starProjection y) =
        U.starProjection ((subspaceWeightedPhase a b U V : E →L[ℂ] E) y) :=
    DFunLike.congr_fun hZP.eq y
  rw [Submodule.reflection_apply, Submodule.reflection_apply, map_sub, map_nsmul, hP]

/-- The explicit spectral-phase formula is an admissible transport. -/
theorem optimalWeightedTransport_maps (a b : ℝ) (U V : Submodule ℂ E)
    (hUV : Module.finrank ℂ U = Module.finrank ℂ V) :
    U.map (optimalWeightedTransport a b U V hUV).toLinearMap = V := by
  let Z := Unitary.linearIsometryEquiv (subspaceWeightedPhase a b U V)
  have hZ (x : E) : Z.symm (U.reflection x) = U.reflection (Z.symm x) := by
    apply Z.injective
    rw [Z.apply_symm_apply]
    rw [show Z (U.reflection (Z.symm x)) = U.reflection (Z (Z.symm x)) from
      subspaceWeightedPhase_commutes_reflection a b U V _, Z.apply_symm_apply]
  apply (Submodule.map_eq_iff_intertwines_reflection U V _).mpr
  intro x
  change nonacuteDirectRotation U V (finiteCrossedDefectEquiv U V hUV)
      (Z.symm (U.reflection x)) = _
  rw [hZ, nonacuteDirectRotation_reflection_intertwines]
  rfl

/-- The explicit weighted transport attains the exact global spectral-trace
minimum, including repeated, zero, and right principal angles. -/
theorem nuclear_optimalWeightedTransport (a b : ℝ) (hb : 0 < b) (hab : b < a)
    (U V : Submodule ℂ E) (hUV : Module.finrank ℂ U = Module.finrank ℂ V) :
    UnitarilyInvariantSeminorm.nuclear ℂ E E
        ((a : ℂ) • (optimalWeightedTransport a b U V hUV).toLinearMap -
          (b : ℂ) • LinearMap.id) =
      weightedRotationMinimum a b (Proposition35.section3CosAngleOperator U V) := by
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation U V (finiteCrossedDefectEquiv U V hUV),
      nonacuteDirectRotation_mem_unitary U V (finiteCrossedDefectEquiv U V hUV)⟩ :
        unitary (E →L[ℂ] E))
  let C := Proposition35.section3CosAngleOperator U V
  let Z := Unitary.linearIsometryEquiv (subspaceWeightedPhase a b U V)
  have hC : IsSelfAdjoint C :=
    ((ContinuousLinearMap.nonneg_iff_isPositive).mp
      (Proposition35.section3CosAngleOperator_nonneg U V)).isSelfAdjoint
  let : IsStarNormal C := hC.isStarNormal
  obtain ⟨n, m, e, theta, hθ, hC0, hC1, hCf, hR0, hR1, hRf, _⟩ :=
    exists_subspace_paired_rotation_basis U V hUV
  have hCp (r : Fin 2) (i : Fin n) : C (e (.inl (r, i))) =
      (Real.cos (theta i) : ℂ) • e (.inl (r, i)) := by
    fin_cases r
    · exact hC0 i
    · exact hC1 i
  have hZp (r : Fin 2) (i : Fin n) : Z (e (.inl (r, i))) =
      circlePhase 1 (optimalWeightedPhase a b (theta i)) • e (.inl (r, i)) :=
    weightedPhaseFactor_apply_cos a b _ C _
      ⟨(hθ i).1.le, by linarith [(hθ i).2, Real.pi_pos]⟩ (hCp r i)
  have hZf (j : Fin m) : Z (e (.inr j)) = e (.inr j) :=
    weightedPhaseFactor_apply_one a b hab.le C _ (hCf j)
  have hc := nuclear_phaseTransport_eq_sum_weightedPhaseCost a b hab.le theta
    (fun i => optimalWeightedPhase a b (theta i)) e R Z hR0 hR1 hRf hZp hZf
  have hsum : (∑ i : Fin n, weightedPhaseCost a b (theta i) (optimalWeightedPhase a b (theta i))) =
      ∑ i : Fin n, weightedPhaseMinimum a b (theta i) := by
    apply Finset.sum_congr rfl
    intro i _
    exact weightedPhaseCost_optimal a b (theta i) hb hab.le ⟨(hθ i).1.le, (hθ i).2⟩
  rw [hsum] at hc
  simp only [Fintype.card_fin] at hc
  have hv := weightedRotationMinimum_eq_paired_sum a b hab.le C theta hθ e hC0 hC1 hCf
  exact hc.trans hv.symm

/-- The explicit optimal transport for the Charbonnier smoothing scale. -/
def optimalSmoothedTransport (tau : ℝ) (U V : Submodule ℂ E)
    (hUV : Module.finrank ℂ U = Module.finrank ℂ V) : E ≃ₗᵢ[ℂ] E :=
  optimalWeightedTransport (smoothingRadius tau) (smoothingRadius tau)⁻¹ U V hUV

/-- The explicitly defined smoothed optimizer carries the source onto the
target, including when right-angle defects are present. -/
theorem optimalSmoothedTransport_maps (tau : ℝ) (U V : Submodule ℂ E)
    (hUV : Module.finrank ℂ U = Module.finrank ℂ V) :
    U.map (optimalSmoothedTransport tau U V hUV).toLinearMap = V :=
  optimalWeightedTransport_maps _ _ U V hUV

/-- The explicitly defined spectral-phase transport attains the exact sum
over the accepted principal angles. -/
theorem smoothedDisplacementCost_optimalSmoothedTransport
    (tau : ℝ) (hτ : 0 < tau) (U V : Submodule ℂ E)
    (hUV : Module.finrank ℂ U = Module.finrank ℂ V) :
    smoothedDisplacementCost tau (optimalSmoothedTransport tau U V hUV).toLinearMap =
      ∑ i : Fin (Module.finrank ℂ U), smoothedPhaseMinimum tau (U.principalAngles V i) := by
  let a := smoothingRadius tau
  have ha : 1 < a := one_lt_smoothingRadius tau hτ
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have hab : a⁻¹ < a := lt_trans ((inv_lt_one₀ ha0).mpr ha) ha
  have hcost : smoothedDisplacementCost tau
      (optimalSmoothedTransport tau U V hUV).toLinearMap =
        UnitarilyInvariantSeminorm.nuclear ℂ E E
          ((a : ℂ) • (optimalSmoothedTransport tau U V hUV).toLinearMap -
            ((a⁻¹ : ℝ) : ℂ) • LinearMap.id) - Module.finrank ℂ E * tau :=
    smoothedDisplacementCost_eq_weightedNuclear tau hτ
      (Unitary.linearIsometryEquiv.symm (optimalSmoothedTransport tau U V hUV))
  rw [hcost]
  rw [show UnitarilyInvariantSeminorm.nuclear ℂ E E
      ((a : ℂ) • (optimalSmoothedTransport tau U V hUV).toLinearMap -
        ((a⁻¹ : ℝ) : ℂ) • LinearMap.id) =
      weightedRotationMinimum a a⁻¹ (Proposition35.section3CosAngleOperator U V) from
    nuclear_optimalWeightedTransport a a⁻¹ (inv_pos.mpr ha0) hab U V hUV]
  exact smoothedTransportMinimum_eq_sum_principalAngles tau hτ U V hUV

/-- The explicit formula is globally optimal among all admissible complex
unitaries; no eigenbasis or restriction on mixing is part of the API. -/
theorem optimalSmoothedTransport_isMin (tau : ℝ) (hτ : 0 < tau)
    (U V : Submodule ℂ E) (hUV : Module.finrank ℂ U = Module.finrank ℂ V)
    (T : E ≃ₗᵢ[ℂ] E) (hT : U.map T.toLinearMap = V) :
    smoothedDisplacementCost tau (optimalSmoothedTransport tau U V hUV).toLinearMap ≤
      smoothedDisplacementCost tau T.toLinearMap := by
  obtain ⟨_, _, _, hWmin⟩ :=
    exists_unitary_minimizing_smoothed_transport_principalAngles tau hτ U V hUV
  rw [smoothedDisplacementCost_optimalSmoothedTransport tau hτ U V hUV]
  exact hWmin T hT

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

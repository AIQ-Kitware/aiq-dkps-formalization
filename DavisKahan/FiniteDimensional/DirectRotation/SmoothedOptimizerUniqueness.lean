/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedCanonicalOptimality

/-!
# Opposite phase optimizers and the exact uniqueness criterion

Reversing the sign of every spectral phase gives a second explicit global
optimizer. The two are distinct as soon as one accepted principal angle
exceeds the cutoff. Combined with quartic stability, this classifies global
uniqueness for every finite-dimensional complex subspace pair.

The journal paper's canonical-cutoff corollary includes this uniqueness
classification. This does not classify every supercritical optimizer.
-/

public section

noncomputable section
open scoped InnerProductSpace ComplexConjugate
namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
private theorem circlePhase_neg_mul (t : ℝ) : circlePhase 1 (-t) * circlePhase 1 t = 1 := by
  simp only [circlePhase, Complex.ofReal_one, one_mul, ← Complex.exp_add]
  rw [show ((-t : ℝ) : ℂ) * Complex.I + (t : ℂ) * Complex.I = 0 by push_cast; ring]
  exact Complex.exp_zero

/-- The optimizer with the opposite sign of every nonnegative scalar phase. -/
def oppositeOptimalSmoothedTransport (tau : ℝ) (U V : Submodule ℂ E)
    (hUV : Module.finrank ℂ U = Module.finrank ℂ V) : E ≃ₗᵢ[ℂ] E :=
  (Unitary.linearIsometryEquiv (subspaceWeightedPhase (smoothingRadius tau) (smoothingRadius tau)⁻¹ U V)).trans
    (Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation U V (finiteCrossedDefectEquiv U V hUV),
        nonacuteDirectRotation_mem_unitary U V (finiteCrossedDefectEquiv U V hUV)⟩ :
          unitary (E →L[ℂ] E)))

theorem oppositeOptimalSmoothedTransport_maps (tau : ℝ) (U V : Submodule ℂ E)
    (hUV : Module.finrank ℂ U = Module.finrank ℂ V) :
    U.map (oppositeOptimalSmoothedTransport tau U V hUV).toLinearMap = V := by
  apply (U.map_eq_iff_intertwines_reflection V _).mpr
  intro x
  change nonacuteDirectRotation U V (finiteCrossedDefectEquiv U V hUV)
    ((subspaceWeightedPhase (smoothingRadius tau) (smoothingRadius tau)⁻¹ U V : E →L[ℂ] E)
      (U.reflection x)) = _
  rw [subspaceWeightedPhase_commutes_reflection, nonacuteDirectRotation_reflection_intertwines]
  rfl

theorem oppositeOptimalSmoothedTransport_cost (tau : ℝ) (htau : 0 < tau)
    (U V : Submodule ℂ E) (hUV : Module.finrank ℂ U = Module.finrank ℂ V) :
    smoothedDisplacementCost tau (oppositeOptimalSmoothedTransport tau U V hUV).toLinearMap =
      ∑ i : Fin (Module.finrank ℂ U), smoothedPhaseMinimum tau (U.principalAngles V i) := by
  let a := smoothingRadius tau
  let b := a⁻¹
  have ha : 1 < a := one_lt_smoothingRadius tau htau
  have ha0 : 0 < a := zero_lt_one.trans ha
  have hb : 0 < b := inv_pos.mpr ha0
  have hab : b < a := ((inv_lt_one₀ ha0).mpr ha).trans ha
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation U V (finiteCrossedDefectEquiv U V hUV),
      nonacuteDirectRotation_mem_unitary U V (finiteCrossedDefectEquiv U V hUV)⟩ : unitary (E →L[ℂ] E))
  let C := Proposition35.section3CosAngleOperator U V
  let Z := Unitary.linearIsometryEquiv (subspaceWeightedPhase a b U V)
  have hC : IsSelfAdjoint C :=
    ((ContinuousLinearMap.nonneg_iff_isPositive).mp (Proposition35.section3CosAngleOperator_nonneg U V)).isSelfAdjoint
  let : IsStarNormal C := hC.isStarNormal
  obtain ⟨n, m, e, theta, hθ, hC0, hC1, hCf, hR0, hR1, hRf, _⟩ :=
    exists_subspace_paired_rotation_basis U V hUV
  have hZp (r : Fin 2) (i : Fin n) : Z (e (.inl (r, i))) =
      circlePhase 1 (optimalWeightedPhase a b (theta i)) • e (.inl (r, i)) := by
    apply weightedPhaseFactor_apply_cos a b _ C _ ⟨(hθ i).1.le, by linarith [(hθ i).2, Real.pi_pos]⟩
    fin_cases r
    · exact hC0 i
    · exact hC1 i
  have hZf (j : Fin m) : Z (e (.inr j)) = e (.inr j) :=
    weightedPhaseFactor_apply_one a b hab.le C _ (hCf j)
  have hZsp (r : Fin 2) (i : Fin n) : Z.symm (e (.inl (r, i))) =
      circlePhase 1 (-optimalWeightedPhase a b (theta i)) • e (.inl (r, i)) := by
    apply Z.injective
    rw [Z.apply_symm_apply, Z.map_smul, hZp, smul_smul, circlePhase_neg_mul, one_smul]
  have hZsf (j : Fin m) : Z.symm (e (.inr j)) = e (.inr j) := by
    apply Z.injective
    rw [Z.apply_symm_apply, hZf]
  have hnc := nuclear_phaseTransport_eq_sum_weightedPhaseCost a b hab.le theta
    (fun i => -optimalWeightedPhase a b (theta i)) e R Z.symm hR0 hR1 hRf hZsp hZsf
  have hsum : (∑ i : Fin n, weightedPhaseCost a b (theta i) (-optimalWeightedPhase a b (theta i))) =
      ∑ i : Fin n, weightedPhaseMinimum a b (theta i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [weightedPhaseCost_neg]
    exact weightedPhaseCost_optimal a b (theta i) hb hab.le ⟨(hθ i).1.le, (hθ i).2⟩
  rw [hsum] at hnc
  have hmin := weightedRotationMinimum_eq_paired_sum a b hab.le C theta hθ e hC0 hC1 hCf
  have hcost := smoothedDisplacementCost_eq_weightedNuclear tau htau
    (Unitary.linearIsometryEquiv.symm (oppositeOptimalSmoothedTransport tau U V hUV))
  change smoothedDisplacementCost tau (oppositeOptimalSmoothedTransport tau U V hUV).toLinearMap =
    UnitarilyInvariantSeminorm.nuclear ℂ E E
      ((a : ℂ) • (Z.trans R).toLinearMap - (b : ℂ) • LinearMap.id) - Module.finrank ℂ E * tau at hcost
  simp only [LinearIsometryEquiv.symm_symm, Fintype.card_fin] at hnc
  rw [hcost, hnc, ← hmin]
  exact smoothedTransportMinimum_eq_sum_principalAngles tau htau U V hUV


private theorem phase_eq_zero_of_eq_negative (delta : ℝ)
    (hδ : delta ∈ Set.Icc 0 (Real.pi / 2))
    (heq : circlePhase 1 delta = circlePhase 1 (-delta)) : delta = 0 := by
  have hi := congrArg Complex.im heq
  simp only [circlePhase, Complex.ofReal_one, one_mul,
    Complex.exp_ofReal_mul_I_im, Real.sin_neg] at hi
  apply Real.strictMonoOn_sin.injOn
    (show delta ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) from
      ⟨by linarith [hδ.1, Real.pi_pos], hδ.2⟩)
    (show (0 : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) from
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
  rw [Real.sin_zero]
  linarith only [hi]

private theorem angles_le_cutoff_of_opposite_eq (tau : ℝ) (htau : 0 < tau)
    (U V : Submodule ℂ E) (hUV : Module.finrank ℂ U = Module.finrank ℂ V)
    (heq : oppositeOptimalSmoothedTransport tau U V hUV = optimalSmoothedTransport tau U V hUV) :
    ∀ i : Fin (Module.finrank ℂ U), U.principalAngles V i ≤ smoothedCriticalAngle tau := by
  let a := smoothingRadius tau
  let b := a⁻¹
  have ha : 1 < a := one_lt_smoothingRadius tau htau
  have ha0 : 0 < a := zero_lt_one.trans ha
  have hb : 0 < b := inv_pos.mpr ha0
  have hab : b < a := ((inv_lt_one₀ ha0).mpr ha).trans ha
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation U V (finiteCrossedDefectEquiv U V hUV),
      nonacuteDirectRotation_mem_unitary U V (finiteCrossedDefectEquiv U V hUV)⟩ : unitary (E →L[ℂ] E))
  let C := Proposition35.section3CosAngleOperator U V
  let Z := Unitary.linearIsometryEquiv (subspaceWeightedPhase a b U V)
  have hC : IsSelfAdjoint C :=
    ((ContinuousLinearMap.nonneg_iff_isPositive).mp (Proposition35.section3CosAngleOperator_nonneg U V)).isSelfAdjoint
  let : IsStarNormal C := hC.isStarNormal
  have hZZ (x : E) : Z x = Z.symm x := by
    apply R.injective
    exact congrArg (fun T : E ≃ₗᵢ[ℂ] E => T x) heq
  obtain ⟨n, m, e, theta, hθ, hC0, hC1, hCf, hR0, hR1, hRf, hJ0⟩ :=
    exists_subspace_paired_rotation_basis U V hUV
  apply principalAngles_le_of_paired_angles_le U V e theta hθ hC0 hC1 hCf hJ0
    (smoothedCriticalAngle tau) (smoothedCriticalAngle_mem_Icc tau).1
  intro i
  let delta := optimalWeightedPhase a b (theta i)
  have hZp : Z (e (.inl (0, i))) = circlePhase 1 delta • e (.inl (0, i)) :=
    weightedPhaseFactor_apply_cos a b _ C _ ⟨(hθ i).1.le, by linarith [(hθ i).2, Real.pi_pos]⟩ (hC0 i)
  have hZsp : Z.symm (e (.inl (0, i))) = circlePhase 1 (-delta) • e (.inl (0, i)) := by
    apply Z.injective
    rw [Z.apply_symm_apply, Z.map_smul, hZp, smul_smul, circlePhase_neg_mul, one_smul]
  have hcoef : circlePhase 1 delta = circlePhase 1 (-delta) := by
    apply smul_left_injective ℂ (e.toBasis.ne_zero (.inl (0, i)))
    change circlePhase 1 delta • e (.inl (0, i)) = circlePhase 1 (-delta) • e (.inl (0, i))
    rw [← hZp, ← hZsp, hZZ]
  have hδmem := optimalWeightedPhase_mem a b (theta i) hb hab.le ⟨(hθ i).1.le, (hθ i).2⟩
  have hδzero : delta = 0 := phase_eq_zero_of_eq_negative delta
    ⟨hδmem.1, hδmem.2.trans (hθ i).2⟩ hcoef
  have hsub : b ≤ a * Real.cos (theta i) := by
    by_contra h
    have hdpos : 0 < delta := by
      dsimp only [delta]
      rw [optimalWeightedPhase, ite_eq_right h]
      exact Real.arccos_pos.mpr ((div_lt_iff₀ hb).mpr (by simpa only [one_mul] using (lt_of_not_ge h)))
    linarith
  have hcos : b ^ 2 ≤ Real.cos (theta i) := by
    have hh := mul_le_mul_of_nonneg_left hsub hb.le
    have hp : b * a = 1 := inv_mul_cancel₀ ha0.ne'
    nlinarith only [hh, congrArg (fun x : ℝ => x * Real.cos (theta i)) hp]
  have hc := smoothedCriticalAngle_mem_Icc tau
  have hi := Real.strictAntiOn_cos.le_iff_ge
    (show smoothedCriticalAngle tau ∈ Set.Icc 0 Real.pi from
      ⟨hc.1, by linarith [hc.2, Real.pi_pos]⟩)
    (show theta i ∈ Set.Icc 0 Real.pi from
      ⟨(hθ i).1.le, by linarith [(hθ i).2, Real.pi_pos]⟩)
  rw [cos_smoothedCriticalAngle tau htau] at hi
  exact hi.mp hcos

/-- Above the cutoff, the two explicit opposite-phase global optimizers
are distinct ambient unitaries. -/
theorem oppositeOptimalSmoothedTransport_ne_of_supercritical
    (tau : ℝ) (htau : 0 < tau) (U V : Submodule ℂ E)
    (hUV : Module.finrank ℂ U = Module.finrank ℂ V)
    (i : Fin (Module.finrank ℂ U)) (hi : smoothedCriticalAngle tau < U.principalAngles V i) :
    oppositeOptimalSmoothedTransport tau U V hUV ≠ optimalSmoothedTransport tau U V hUV := by
  intro h
  exact (not_le_of_gt hi) (angles_le_cutoff_of_opposite_eq tau htau U V hUV h i)

/-- The opposite spectral-phase formula is globally optimal. -/
theorem oppositeOptimalSmoothedTransport_isMin
    (tau : ℝ) (htau : 0 < tau) (U V : Submodule ℂ E)
    (hUV : Module.finrank ℂ U = Module.finrank ℂ V)
    (T : E ≃ₗᵢ[ℂ] E) (hT : U.map T.toLinearMap = V) :
    smoothedDisplacementCost tau (oppositeOptimalSmoothedTransport tau U V hUV).toLinearMap ≤
      smoothedDisplacementCost tau T.toLinearMap := by
  rw [oppositeOptimalSmoothedTransport_cost tau htau U V hUV,
    ← smoothedDisplacementCost_optimalSmoothedTransport tau htau U V hUV]
  exact optimalSmoothedTransport_isMin tau htau U V hUV T hT


/-- The unrestricted smoothed transport minimum is unique exactly in the
closed canonical principal-angle regime. -/
theorem smoothed_transport_unique_minimizer_iff
    (tau : ℝ) (htau : 0 < tau) (U V : Submodule ℂ E)
    (hUV : Module.finrank ℂ U = Module.finrank ℂ V) :
    (∃! W : E ≃ₗᵢ[ℂ] E, U.map W.toLinearMap = V ∧
      ∀ T : E ≃ₗᵢ[ℂ] E, U.map T.toLinearMap = V →
        smoothedDisplacementCost tau W.toLinearMap ≤ smoothedDisplacementCost tau T.toLinearMap) ↔
      ∀ i : Fin (Module.finrank ℂ U), U.principalAngles V i ≤ smoothedCriticalAngle tau := by
  constructor
  · rintro ⟨W, hW, huniq⟩
    by_contra h
    obtain ⟨i, hi⟩ := not_forall.mp h
    have hp := huniq (optimalSmoothedTransport tau U V hUV)
      ⟨optimalSmoothedTransport_maps tau U V hUV, optimalSmoothedTransport_isMin tau htau U V hUV⟩
    have hm := huniq (oppositeOptimalSmoothedTransport tau U V hUV)
      ⟨oppositeOptimalSmoothedTransport_maps tau U V hUV, oppositeOptimalSmoothedTransport_isMin tau htau U V hUV⟩
    exact oppositeOptimalSmoothedTransport_ne_of_supercritical tau htau U V hUV i
      (lt_of_not_ge hi) (hm.trans hp.symm)
  · intro hmax
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation U V (finiteCrossedDefectEquiv U V hUV),
        nonacuteDirectRotation_mem_unitary U V (finiteCrossedDefectEquiv U V hUV)⟩ : unitary (E →L[ℂ] E))
    have hcan := smoothed_canonical_unique_minimizer tau htau U V hUV hmax
    dsimp only at hcan
    refine ⟨R, ⟨hcan.1, fun T hT => (hcan.2 T hT).1⟩, ?_⟩
    intro T hT
    exact (hcan.2 T hT.1).2 (hT.2 R hcan.1)

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

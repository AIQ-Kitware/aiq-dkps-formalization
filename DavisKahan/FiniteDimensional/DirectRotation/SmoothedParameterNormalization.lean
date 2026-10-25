/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.SmoothedPhaseWeight

/-!
# Unique effective phase and defect coordinates for Charbonnier optimizers

Normalize the phase projection to the orthogonal complement of the phase
weight's kernel. This removes the freedom on inactive, critical and right
directions while keeping every independent crossed-defect unitary.
-/

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- Compatible projections supported on the effective weighted phase space. -/
def weightedNormalizedPhaseProjections
    (a b : ℝ) (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L) :
    Set (E →L[ℂ] E) :=
  {P | IsStarProjection P ∧
    Commute P (nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL)) ∧
    (∀ x, P (K.reflection x) = K.reflection (P x)) ∧
    ∀ x, P x ∈ (weightedPhaseWeight a b (Proposition35.section3CosAngleOperator K L)).kerᗮ}

omit [FiniteDimensional ℂ E] in
private theorem weighted_phase_split_eq (C F P : E →L[ℂ] E) :
    C * (F * P + star F * (1 - P)) = C * star F + (C * (F - star F)) * P := by
  noncomm_ring

/-- Every compatible weighted phase projection has a normalized
representative with the same weighted phase formula. -/
theorem exists_normalized_weighted_phase_projection
    (a b : ℝ) (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L)
    (P : E →L[ℂ] E) (hP : IsStarProjection P)
    (hPR : Commute P (nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL)))
    (hPJ : ∀ x, P (K.reflection x) = K.reflection (P x)) :
    let C := Proposition35.section3CosAngleOperator K L
    let F := weightedPhaseFactor a b C
    ∃ Q ∈ weightedNormalizedPhaseProjections a b K L hKL,
      C * (F * Q + star F * (1 - Q)) = C * (F * P + star F * (1 - P)) := by
  let C := Proposition35.section3CosAngleOperator K L
  let F := weightedPhaseFactor a b C
  let W := weightedPhaseWeight a b C
  let A := W.kerᗮ.starProjection
  let Q := A * P
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
      nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
        unitary (E →L[ℂ] E))
  have hC : IsSelfAdjoint C :=
    (ContinuousLinearMap.nonneg_iff_isPositive.mp
      (Proposition35.section3CosAngleOperator_nonneg K L)).isSelfAdjoint
  have hPC : Commute P C := commute_cosine_of_commute_nonacuteDirectRotation
    K L _ P hP.isSelfAdjoint hPR
  have hnorm := ContinuousLinearMap.normalized_starProjection W P hP
    (weightedPhaseWeight_commute a b C P hC hPC.symm).symm
  have hRC : Commute (R : E →L[ℂ] E) C :=
    Proposition35.nonacuteDirectRotation_comm_cosine K L _
  have hAR : Commute A (R : E →L[ℂ] E) :=
    ContinuousLinearMap.commute_starProjection_orthogonal_ker_of_unitary W R
      (weightedPhaseWeight_commute a b C _ hC hRC.symm).symm
  have hCJ : Commute C (K.reflection : E →L[ℂ] E) :=
    (K.commute_reflection_iff.mpr
      (Proposition35.section3CosAngleOperator_comm_projection K L).symm).symm
  have hAJ : Commute A (K.reflection : E →L[ℂ] E) :=
    ContinuousLinearMap.commute_starProjection_orthogonal_ker_of_unitary W K.reflection
      (weightedPhaseWeight_commute a b C _ hC hCJ).symm
  have hPJ' : Commute P (K.reflection : E →L[ℂ] E) := by
    ext x
    exact hPJ x
  refine ⟨Q, ⟨hnorm.1, hAR.mul_left hPR, ?_, hnorm.2.1⟩, ?_⟩
  · intro x
    exact congrArg (fun B : E →L[ℂ] E => B x) (hAJ.mul_left hPJ').eq
  · change C * (F * Q + star F * (1 - Q)) = C * (F * P + star F * (1 - P))
    rw [weighted_phase_split_eq, weighted_phase_split_eq]
    exact congrArg (fun B => C * star F + B) hnorm.2.2

/-- All globally minimizing Charbonnier transports admit exactly one
normalized phase projection and crossed-defect unitary, including all
zero, critical, repeated and right angles. -/
theorem smoothed_transport_isMin_iff_unique_normalized_phase_and_defect_complex
    (tau : ℝ) (htau : 0 < tau)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L)
    (T : E ≃ₗᵢ[ℂ] E) (hT : K.map T.toLinearMap = L) :
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
        nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
          unitary (E →L[ℂ] E))
    let C := Proposition35.section3CosAngleOperator K L
    let a := smoothingRadius tau
    let F := weightedPhaseFactor a a⁻¹ C
    (∀ S : E ≃ₗᵢ[ℂ] E, K.map S.toLinearMap = L →
      smoothedDisplacementCost tau T.toLinearMap ≤ smoothedDisplacementCost tau S.toLinearMap) ↔
      ∃! data : (E →L[ℂ] E) ×
          (halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L),
        data.1 ∈ weightedNormalizedPhaseProjections a a⁻¹ K L hKL ∧
        (∀ x : halmosSourceDefect K L, T x = (data.2 x : E)) ∧
        (∀ y : halmosTargetDefect K L, T y = (data.2.symm y : E)) ∧
        C * (R.trans T.symm : E →L[ℂ] E) =
          C * (F * data.1 + star F * (1 - data.1)) := by
  let C := Proposition35.section3CosAngleOperator K L
  let a := smoothingRadius tau
  let F := weightedPhaseFactor a a⁻¹ C
  constructor
  · intro hmin
    obtain ⟨⟨D, ⟨hsrc, htgt⟩, _⟩, P, hP, hPR, hPJ, _, hphase⟩ :=
      (smoothed_transport_isMin_iff_phase_and_defect_equiv_complex tau htau
        K L hKL T hT).mp hmin
    obtain ⟨Q, hQ, hQphase⟩ := exists_normalized_weighted_phase_projection
      a a⁻¹ K L hKL P hP hPR hPJ
    refine ⟨(Q, D), ⟨hQ, hsrc, htgt, hphase.trans hQphase.symm⟩, ?_⟩
    rintro ⟨P', D'⟩ ⟨hP', hsrc', _, hphase'⟩
    have hD : D' = D := by
      ext x
      exact (hsrc' x).symm.trans (hsrc x)
    have hweight : weightedPhaseWeight a a⁻¹ C * P' = weightedPhaseWeight a a⁻¹ C * Q := by
      have h := hphase'.symm.trans (hphase.trans hQphase.symm)
      rw [weighted_phase_split_eq, weighted_phase_split_eq] at h
      exact add_left_cancel h
    exact Prod.ext
      (ContinuousLinearMap.eq_of_mul_eq_of_range_orthogonal_ker _ _ _ hweight
        hP'.2.2.2 hQ.2.2.2) hD
  · rintro ⟨⟨P, D⟩, ⟨hP, hsrc, htgt, hphase⟩, _⟩
    apply (smoothed_transport_isMin_iff_phase_and_kernel_complex tau htau K L hKL T hT).mpr
    have ha : 0 < a := zero_lt_one.trans (one_lt_smoothingRadius tau htau)
    have hC : IsSelfAdjoint C :=
      (ContinuousLinearMap.nonneg_iff_isPositive.mp
        (Proposition35.section3CosAngleOperator_nonneg K L)).isSelfAdjoint
    let : IsStarNormal C := hC.isStarNormal
    refine ⟨Proposition35.selfAdjoint_on_cosine_kernel_of_defect_equiv
      K L T D hsrc htgt, P, hP.1, hP.2.1, hP.2.2.1, ?_, hphase⟩
    intro x hx
    exact ContinuousLinearMap.apply_eq_zero_of_range_orthogonal_ker _ P hP.1.isSelfAdjoint
      hP.2.2.2 x (weightedPhaseWeight_apply_zero a a⁻¹ (inv_pos.mpr ha) ha.le C x hx)

/-- The complete set of global Charbonnier transport optimizers. -/
def smoothedTransportMinimizers (tau : ℝ) (K L : Submodule ℂ E) : Set (E ≃ₗᵢ[ℂ] E) :=
  {T | K.map T.toLinearMap = L ∧
    ∀ S : E ≃ₗᵢ[ℂ] E, K.map S.toLinearMap = L →
      smoothedDisplacementCost tau T.toLinearMap ≤ smoothedDisplacementCost tau S.toLinearMap}

/-- Normalized compatible projections and independent defect unitaries
parametrize every global optimizer bijectively, with the actual actions,
weighted phase formula and uniform Lipschitz recovery of the phase
projection from the optimizer. This is an algebraic equivalence; no manifold
or topological identification of the projection space is asserted. -/
theorem exists_smoothed_normalized_parameter_equiv
    (tau : ℝ) (htau : 0 < tau)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L) :
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
        nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
          unitary (E →L[ℂ] E))
    let C := Proposition35.section3CosAngleOperator K L
    let F := weightedPhaseFactor (smoothingRadius tau) (smoothingRadius tau)⁻¹ C
    ∃ e : (weightedNormalizedPhaseProjections
        (smoothingRadius tau) (smoothingRadius tau)⁻¹ K L hKL ×
        (halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)) ≃
          smoothedTransportMinimizers tau K L,
      (∀ data, (∀ x : halmosSourceDefect K L, (e data).val x = (data.2 x : E)) ∧
        (∀ y : halmosTargetDefect K L, (e data).val y = (data.2.symm y : E)) ∧
        C * (R.trans (e data).val.symm : E →L[ℂ] E) =
          C * (F * data.1.val + star F * (1 - data.1.val))) ∧
      ∃ k : ℝ, 0 ≤ k ∧ ∀ data data',
        ‖data.1.val - data'.1.val‖ ≤
          k * ‖((e data).val : E →L[ℂ] E) - ((e data').val : E →L[ℂ] E)‖ := by
  classical
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
      nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
        unitary (E →L[ℂ] E))
  let C := Proposition35.section3CosAngleOperator K L
  let F := weightedPhaseFactor (smoothingRadius tau) (smoothingRadius tau)⁻¹ C
  let Params := weightedNormalizedPhaseProjections
    (smoothingRadius tau) (smoothingRadius tau)⁻¹ K L hKL ×
    (halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
  let M := smoothedTransportMinimizers tau K L
  let rel (data : Params) (T : M) :=
    (∀ x : halmosSourceDefect K L, T.val x = (data.2 x : E)) ∧
      (∀ y : halmosTargetDefect K L, T.val y = (data.2.symm y : E)) ∧
      C * (R.trans T.val.symm : E →L[ℂ] E) =
        C * (F * data.1.val + star F * (1 - data.1.val))
  have hatt (data : Params) : ∃ T : M, rel data T := by
    obtain ⟨T, ⟨hT, hsrc, htgt, hphase, _, hmin⟩, _⟩ :=
      exists_unique_smoothed_transport_from_phase_and_defect_complex tau htau
        K L hKL data.1.val data.1.property.1 data.1.property.2.1
        data.1.property.2.2.1 data.2
    exact ⟨⟨T, hT, hmin⟩, hsrc, htgt, hphase⟩
  let f : Params → M := fun data => (hatt data).choose
  have hf (data) : rel data (f data) := (hatt data).choose_spec
  have hinj : Function.Injective f := by
    intro d e hde
    obtain ⟨data, _, huni⟩ :=
      (smoothed_transport_isMin_iff_unique_normalized_phase_and_defect_complex tau htau
        K L hKL (f d).val (f d).property.1).mp (f d).property.2
    have hd := huni (d.1.val, d.2) ⟨d.1.property, hf d⟩
    have he := huni (e.1.val, e.2) ⟨e.1.property, by rw [hde]; exact hf e⟩
    have heq := hd.trans he.symm
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst heq
    · exact congrArg (fun z : (E →L[ℂ] E) ×
        (halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L) => z.2) heq
  have hsurj : Function.Surjective f := by
    intro T
    obtain ⟨⟨P, D⟩, ⟨hP, hsrc, htgt, hphase⟩, _⟩ :=
      (smoothed_transport_isMin_iff_unique_normalized_phase_and_defect_complex tau htau
        K L hKL T.val T.property.1).mp T.property.2
    let data : Params := (⟨P, hP⟩, D)
    refine ⟨data, Subtype.ext ?_⟩
    exact transport_eq_of_phase_and_defect_actions_complex
      K L R (f data).val T.val D (hf data).1 (hf data).2.1 hsrc htgt
        ((hf data).2.2.trans hphase.symm)
  refine ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, hf, ?_⟩
  obtain ⟨k, hk, hbound⟩ :=
    LinearIsometryEquiv.exists_pos_normalized_left_split_parameter_recovery R C F (star F)
  refine ⟨k * ‖C‖, mul_nonneg hk.le (norm_nonneg _), fun d e => ?_⟩
  exact hbound (f d).val (f e).val d.1.val e.1.val
    d.1.property.2.2.2 e.1.property.2.2.2 (hf d).2.2 (hf e).2.2

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

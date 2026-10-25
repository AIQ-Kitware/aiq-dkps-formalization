/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedMultiplicityParameters
public import ForTauCeti.Analysis.InnerProductSpace.Projection.ParameterTopology
public import ForTauCeti.Analysis.InnerProductSpace.LinearIsometryEquivCompact

/-!
# Topology of the complete Charbonnier optimizer families

Actual multiplicity projections and independent right-defect unitaries
give all ambient optimizers, with their operator norm topology.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

open scoped TauCeti.LinearIsometryEquivOperatorNorm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- The normalized phase parameter space is compact in operator norm.
No exponent restriction is needed for this geometric fact. -/
theorem isCompact_weightedNormalizedPhaseProjections
    (a b : ℝ) (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L) :
    IsCompact (weightedNormalizedPhaseProjections a b K L hKL) := by
  let R := nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL)
  let N := (weightedPhaseWeight a b (Proposition35.section3CosAngleOperator K L)).kerᗮ
  have hcomm : IsClosed {P : E →L[ℂ] E | Commute P R} :=
    isClosed_eq (continuous_id.mul_const _) (continuous_id.const_mul _)
  have href : IsClosed {P : E →L[ℂ] E | ∀ x, P (K.reflection x) = K.reflection (P x)} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro x
    exact isClosed_eq (continuous_id.clm_apply continuous_const)
      (K.reflection.continuous.comp (continuous_id.clm_apply continuous_const))
  have hsupp : IsClosed {P : E →L[ℂ] E | ∀ x, P x ∈ N} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro x
    exact N.closed_of_finiteDimensional.preimage
      (continuous_id.clm_apply continuous_const)
  exact isCompact_setOf_isStarProjection.of_isClosed_subset
    (isClosed_setOf_isStarProjection.inter (hcomm.inter (href.inter hsupp)))
    (fun _ h => h.1)

/-- All global Charbonnier optimizers are homeomorphic, in operator norm,
to the normalized compatible phase projections and independent defect
unitaries. Both actual defect actions and the weighted phase identity
hold in these coordinates. -/
theorem exists_smoothed_normalized_parameter_homeomorph
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
        (halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)) ≃ₜ
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
  let : CompactSpace (weightedNormalizedPhaseProjections
      (smoothingRadius tau) (smoothingRadius tau)⁻¹ K L hKL) :=
    isCompact_iff_compactSpace.mp (isCompact_weightedNormalizedPhaseProjections
      (smoothingRadius tau) (smoothingRadius tau)⁻¹ K L hKL)
  obtain ⟨e, he, hk⟩ := exists_smoothed_normalized_parameter_equiv tau htau K L hKL
  let f : Params → E ≃ₗᵢ[ℂ] E := fun data => (e data).val
  have hrel (data : Params) (T : E ≃ₗᵢ[ℂ] E) : f data = T ↔
      (∀ x : halmosSourceDefect K L, T x = (data.2 x : E)) ∧
        (∀ y : halmosTargetDefect K L, T y = (data.2.symm y : E)) ∧
        C * (R.trans T.symm : E →L[ℂ] E) =
          C * (F * data.1.val + star F * (1 - data.1.val)) := by
    constructor
    · rintro rfl
      exact he data
    · rintro ⟨hsrc, htgt, hphase⟩
      exact transport_eq_of_phase_and_defect_actions_complex K L R (f data) T data.2
        (he data).1 (he data).2.1 hsrc htgt ((he data).2.2.trans hphase.symm)
  have hgraph : IsClosed (Function.graph f) := by
    let X := Params × (E ≃ₗᵢ[ℂ] E)
    have hD : Continuous (fun z : X => z.1.2) := continuous_snd.comp continuous_fst
    have hDs : Continuous (fun z : X => z.1.2.symm) :=
      LinearIsometryEquiv.continuous_symm_operatorNorm.comp hD
    have hP : Continuous (fun z : X => z.1.1.val) :=
      continuous_subtype_val.comp (continuous_fst.comp continuous_fst)
    have hTi : Continuous (fun z : X => (z.2.symm : E →L[ℂ] E)) :=
      LinearIsometryEquiv.isEmbedding_toContinuousLinearMap.continuous.comp
        (continuous_inv.comp continuous_snd)
    have hRT : Continuous (fun z : X => (R.trans z.2.symm : E →L[ℂ] E)) :=
      (hTi.mul (continuous_const : Continuous (fun _ : X => (R : E →L[ℂ] E)))).congr
        (fun _ => by ext x; rfl)
    have hsrc : IsClosed {z : X | ∀ x : halmosSourceDefect K L,
        z.2 x = (z.1.2 x : E)} := by
      simp only [Set.ofPred_forall]
      apply isClosed_iInter
      intro x
      exact isClosed_eq (continuous_snd.eval_const (x : E))
        (continuous_subtype_val.comp (hD.eval_const x))
    have htgt : IsClosed {z : X | ∀ y : halmosTargetDefect K L,
        z.2 y = (z.1.2.symm y : E)} := by
      simp only [Set.ofPred_forall]
      apply isClosed_iInter
      intro y
      exact isClosed_eq (continuous_snd.eval_const (y : E))
        (continuous_subtype_val.comp (hDs.eval_const y))
    have hphase : IsClosed {z : X | C * (R.trans z.2.symm : E →L[ℂ] E) =
        C * (F * z.1.1.val + star F * (1 - z.1.1.val))} :=
      isClosed_eq (continuous_const.mul hRT)
        (continuous_const.mul ((continuous_const.mul hP).add
          (continuous_const.mul (continuous_const.sub hP))))
    change IsClosed {z : X | f z.1 = z.2}
    simp only [hrel]
    exact hsrc.inter (htgt.inter hphase)
  have hf : Continuous f := continuous_of_isClosed_graph hgraph
  have hec : Continuous e := hf.subtype_mk _
  exact ⟨e.toHomeomorphOfContinuousClosed hec hec.isClosedMap, he, hk⟩

/-- Every complex Charbonnier optimizer is parametrized homeomorphically by one
arbitrary orthogonal projection on each actual active multiplicity space
and one independent defect unitary. The index set is finite and no frame
is prescribed to the competing ambient transporters. -/
theorem exists_smoothed_multiplicity_parameter_homeomorph
    (tau : ℝ) (htau : 0 < tau)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L) :
    let U : unitary (E →L[ℂ] E) :=
      ⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
        nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩
    let a := smoothingRadius tau
    let N := weightedRotationMultiplicitySpace a a⁻¹ U
    ∃ e : ((∀ theta : weightedActiveRotationAngles a a⁻¹ U,
        {Q : N theta →L[ℂ] N theta // IsStarProjection Q}) ×
          (halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)) ≃ₜ
            smoothedTransportMinimizers tau K L,
      (∀ data, (∀ x : halmosSourceDefect K L, (e data).val x = (data.2 x : E)) ∧
        (∀ y : halmosTargetDefect K L, (e data).val y = (data.2.symm y : E)) ∧
        ∃ P ∈ weightedNormalizedPhaseProjections a a⁻¹ K L hKL,
          (∀ theta (x : N theta), P x = ((data.1 theta).val x : E)) ∧
          Proposition35.section3CosAngleOperator K L *
              ((Unitary.linearIsometryEquiv U).trans (e data).val.symm : E →L[ℂ] E) =
            Proposition35.section3CosAngleOperator K L *
              (weightedPhaseFactor a a⁻¹ (Proposition35.section3CosAngleOperator K L) * P +
                star (weightedPhaseFactor a a⁻¹ (Proposition35.section3CosAngleOperator K L)) *
                  (1 - P))) ∧
      (∀ theta, IsLocallyConstant (fun T =>
        Module.finrank ℂ (((e.symm T).1 theta).val.range))) ∧
      ∃ k : ℝ, 0 < k ∧ ∀ data data' theta,
        Module.finrank ℂ ((data.1 theta).val.range) ≠
          Module.finrank ℂ ((data'.1 theta).val.range) →
        1 ≤ k * ‖((e data).val : E →L[ℂ] E) - ((e data').val : E →L[ℂ] E)‖ := by
  classical
  let a := smoothingRadius tau
  have ha : 1 < a := one_lt_smoothingRadius tau htau
  have ha0 : 0 < a := zero_lt_one.trans ha
  let U : unitary (E →L[ℂ] E) :=
    ⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
      nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩
  let mu := fun theta : weightedActiveRotationAngles a a⁻¹ U =>
    Complex.exp ((theta.val : ℂ) * Complex.I)
  have hmu (theta) : ‖mu theta‖ = 1 := Complex.norm_exp_ofReal_mul_I theta.val
  have hinj : Function.Injective mu := by
    intro theta eta heq
    have h := weightedSupercriticalAngles_exp_injective a a⁻¹
      (a₁ := ⟨theta.val, theta.property.1⟩) (a₂ := ⟨eta.val, eta.property.1⟩) heq
    exact Subtype.ext (congrArg (fun a : weightedSupercriticalAngles a a⁻¹ => a.val) h)
  have hconj (theta eta) : mu theta ≠ star (mu eta) := by
    intro heq
    have him := congrArg Complex.im heq
    have hpos (a : weightedActiveRotationAngles a a⁻¹ U) : 0 < Real.sin a.val :=
      Real.sin_pos_of_pos_of_lt_pi a.property.1.1.1
        (by linarith [a.property.1.1.2, Real.pi_pos])
    change (Complex.exp ((theta.val : ℂ) * Complex.I)).im =
      (star (Complex.exp ((eta.val : ℂ) * Complex.I))).im at him
    simp only [RCLike.star_def, Complex.conj_im, Complex.exp_ofReal_mul_I_im] at him
    linarith [hpos theta, hpos eta]
  obtain ⟨eP, heP⟩ := exists_unitary_paired_projection_homeomorph U K.reflection
    K.reflection_involutive
    (nonacuteDirectRotation_reflection_eq_reflection_star K L (finiteCrossedDefectEquiv K L hKL))
    mu hmu hinj hconj
  have hspaces := weightedNormalizedPhaseProjections_eq_paired_projection_space
    a a⁻¹ (inv_pos.mpr ha0) (((inv_lt_one₀ ha0).mpr ha).trans ha) K L hKL
  let eP' := eP.trans (Homeomorph.setCongr hspaces.symm)
  obtain ⟨eT, heT, k, hk, hrec⟩ := exists_smoothed_normalized_parameter_homeomorph tau htau K L hKL
  let e := (Homeomorph.prodCongr eP'
    (Homeomorph.refl (halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L))).trans eT
  refine ⟨e, ?_, ?_, k + 1, by linarith, ?_⟩
  · intro data
    have hdata := heT (eP' data.1, data.2)
    refine ⟨hdata.1, hdata.2.1, (eP' data.1).val, (eP' data.1).property, ?_, hdata.2.2⟩
    exact heP data.1
  · intro theta
    exact isLocallyConstant_starProjection_finrank.comp_continuous
      ((continuous_apply theta).comp (continuous_fst.comp e.symm.continuous))
  · intro data data' theta hrank
    have hnorm : 1 ≤ ‖(data.1 theta).val - (data'.1 theta).val‖ := by
      apply le_of_not_gt
      intro hclose
      exact hrank (finrank_range_eq_of_idempotent_of_norm_sub_lt_one _ _
        (data.1 theta).property.isIdempotentElem
        (data'.1 theta).property.isIdempotentElem hclose)
    have hrestr := ContinuousLinearMap.norm_sub_le_of_restrictions
      (eP' data.1).val (eP' data'.1).val _ (data.1 theta).val (data'.1 theta).val
      (heP data.1 theta) (heP data'.1 theta)
    calc
      1 ≤ ‖(eP' data.1).val - (eP' data'.1).val‖ := hnorm.trans hrestr
      _ ≤ k * ‖((e data).val : E →L[ℂ] E) - ((e data').val : E →L[ℂ] E)‖ :=
        hrec (eP' data.1, data.2) (eP' data'.1, data'.2)
      _ ≤ (k + 1) * ‖((e data).val : E →L[ℂ] E) - ((e data').val : E →L[ℂ] E)‖ :=
        mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)

/-- The complete optimizer set is compact in operator norm. -/
theorem isCompact_smoothedTransportMinimizers
    (tau : ℝ) (htau : 0 < tau)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L) :
    IsCompact (smoothedTransportMinimizers tau K L) := by
  let : CompactSpace (weightedNormalizedPhaseProjections
      (smoothingRadius tau) (smoothingRadius tau)⁻¹ K L hKL) :=
    isCompact_iff_compactSpace.mp (isCompact_weightedNormalizedPhaseProjections
      (smoothingRadius tau) (smoothingRadius tau)⁻¹ K L hKL)
  obtain ⟨e, _, _⟩ := exists_smoothed_normalized_parameter_homeomorph tau htau K L hKL
  exact isCompact_iff_compactSpace.mpr e.compactSpace

/-- With simple active angles and no right defect, every optimizer is
isolated within the full ambient optimizer set. Inactive multiplicities
remain unrestricted. -/
theorem discreteTopology_smoothedTransportMinimizers_of_simple_active_angles
    (tau : ℝ) (htau : 0 < tau)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L)
    (hdefect : Module.finrank ℂ (halmosSourceDefect K L) = 0) :
    let a := smoothingRadius tau
    let U : unitary (E →L[ℂ] E) :=
      ⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
        nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩
    (∀ theta : weightedActiveRotationAngles a a⁻¹ U,
      Module.finrank ℂ (weightedRotationMultiplicitySpace a a⁻¹ U theta) = 1) →
    DiscreteTopology (smoothedTransportMinimizers tau K L) := by
  dsimp only
  intro hdim
  have hcard := natCard_smoothedTransportMinimizers_of_simple_active_angles
    tau htau K L hKL hdefect hdim
  let : Finite (smoothedTransportMinimizers tau K L) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (by norm_num))
  infer_instance

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

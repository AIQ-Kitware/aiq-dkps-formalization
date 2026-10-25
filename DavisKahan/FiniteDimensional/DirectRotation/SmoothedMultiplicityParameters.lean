/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.SmoothedParameterNormalization
import ForTauCeti.Analysis.InnerProductSpace.PairedProjectionFamily
import ForTauCeti.Analysis.InnerProductSpace.Projection.FiniteParameters

/-!
# Independent effective multiplicity parameters for Charbonnier transport

The weighted phase support is the sum of actual canonical eigenspace pairs
with positive cosine below `b/a`. The normalized parameters are independent
orthogonal projections on one whole multiplicity space from each pair.
-/

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- Physical supercritical interior angles. Only finitely many have
nonzero eigenspace for a fixed finite-dimensional canonical rotation. -/
def weightedSupercriticalAngles (a b : ℝ) : Set ℝ :=
  {theta | theta ∈ Ioo 0 (Real.pi / 2) ∧ a * Real.cos theta < b}

/-- The positive canonical eigenphase distinguishes physical interior
angles, independently of the cutoff. -/
theorem weightedSupercriticalAngles_exp_injective (a b : ℝ) :
    Function.Injective (fun theta : weightedSupercriticalAngles a b =>
      Complex.exp ((theta.val : ℂ) * Complex.I)) := by
  intro theta eta heq
  apply Subtype.ext
  apply Real.injOn_cos
    ⟨theta.property.1.1.le, by linarith [theta.property.1.2, Real.pi_pos]⟩
    ⟨eta.property.1.1.le, by linarith [eta.property.1.2, Real.pi_pos]⟩
  simpa only [Complex.exp_ofReal_mul_I_re] using congrArg Complex.re heq

/-- The actual supercritical interior eigenangles of a unitary. Empty
eigenspaces are excluded, so these indices retain multiplicities as spaces. -/
def weightedActiveRotationAngles (a b : ℝ) (U : unitary (E →L[ℂ] E)) : Set ℝ :=
  {theta | theta ∈ weightedSupercriticalAngles a b ∧
    Module.End.HasEigenvalue (U : E →L[ℂ] E).toLinearMap
      (Complex.exp ((theta : ℂ) * Complex.I))}

/-- The actual positive canonical rotation eigenspace at an active angle. -/
def weightedRotationMultiplicitySpace
    (a b : ℝ) (U : unitary (E →L[ℂ] E)) (theta : weightedActiveRotationAngles a b U) :
    Submodule ℂ E :=
  Module.End.eigenspace (U : E →L[ℂ] E).toLinearMap
    (Complex.exp ((theta.val : ℂ) * Complex.I))

/-- A finite-dimensional unitary has only finitely many active
multiplicity-space factors. -/
theorem finite_weightedActiveRotationAngles (a b : ℝ) (U : unitary (E →L[ℂ] E)) :
    (weightedActiveRotationAngles a b U).Finite := by
  let f : weightedActiveRotationAngles a b U → Module.End.Eigenvalues
      (U : E →L[ℂ] E).toLinearMap := fun theta => ⟨_, theta.property.2⟩
  have hinj : Function.Injective f := by
    intro theta eta heq
    have h := weightedSupercriticalAngles_exp_injective a b
      (a₁ := ⟨theta.val, theta.property.1⟩) (a₂ := ⟨eta.val, eta.property.1⟩)
      (congrArg Subtype.val heq)
    exact Subtype.ext (congrArg (fun a : weightedSupercriticalAngles a b => a.val) h)
  let : Finite (weightedActiveRotationAngles a b U) := Finite.of_injective f hinj
  exact Set.toFinite _

/-- The phase-weight support is exactly the sum of the actual
supercritical interior canonical eigenspace pairs. No chosen optimizer or
simple principal-angle spectrum is assumed. -/
theorem weightedPhaseWeight_orthogonal_ker_eq_paired_eigenspace_sum
    (a b : ℝ) (hb : 0 < b) (hab : b < a)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L) :
    let U : unitary (E →L[ℂ] E) :=
      ⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
        nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩
    let C := Proposition35.section3CosAngleOperator K L
    let N := fun theta : weightedSupercriticalAngles a b =>
      Module.End.eigenspace (U : E →L[ℂ] E).toLinearMap
        (Complex.exp ((theta.val : ℂ) * Complex.I))
    (weightedPhaseWeight a b C).kerᗮ =
      ⨆ theta, N theta ⊔ (N theta).map K.reflection.toLinearMap := by
  classical
  have ha : 0 ≤ a := hb.le.trans hab.le
  let D := finiteCrossedDefectEquiv K L hKL
  let U : unitary (E →L[ℂ] E) :=
    ⟨nonacuteDirectRotation K L D, nonacuteDirectRotation_mem_unitary K L D⟩
  let C := Proposition35.section3CosAngleOperator K L
  let W := weightedPhaseWeight a b C
  let N := fun theta : weightedSupercriticalAngles a b =>
    Module.End.eigenspace (U : E →L[ℂ] E).toLinearMap
      (Complex.exp ((theta.val : ℂ) * Complex.I))
  let S := ⨆ theta, N theta ⊔ (N theta).map K.reflection.toLinearMap
  have hC : IsSelfAdjoint C :=
    (ContinuousLinearMap.nonneg_iff_isPositive.mp
      (Proposition35.section3CosAngleOperator_nonneg K L)).isSelfAdjoint
  let : IsStarNormal C := hC.isStarNormal
  have hW : IsStarNormal W := by
    rw [isStarNormal_iff, star_weightedPhaseWeight a b C hC]
    exact (Commute.refl W).neg_left
  have hrange : W.range = W.kerᗮ := by
    rw [← ContinuousLinearMap.IsStarNormal.orthogonal_range hW,
      Submodule.orthogonal_orthogonal]
  have hcos (theta : weightedSupercriticalAngles a b) (x : N theta) :
      C x = (Real.cos theta.val : ℂ) • (x : E) := by
    have h := unitary_real_part_apply_of_apply_eq_smul U C
      (nonacuteDirectRotation_add_star_eq_two_cosine K L D)
      (Complex.exp ((theta.val : ℂ) * Complex.I))
      (Complex.norm_exp_ofReal_mul_I theta.val) x (Module.End.mem_eigenspace_iff.mp x.property)
    change C x = ((Complex.exp ((theta.val : ℂ) * Complex.I)).re : ℂ) • (x : E) at h
    rwa [Complex.exp_ofReal_mul_I_re] at h
  have hmem (theta : weightedSupercriticalAngles a b) (x : E)
      (hx : C x = (Real.cos theta.val : ℂ) • x) : x ∈ W.kerᗮ := by
    rw [← hrange]
    by_cases hzero : x = 0
    · subst x
      exact Submodule.zero_mem _
    have hne : W x ≠ 0 := by
      intro hz
      exact (not_le_of_gt theta.property.2)
        ((weightedPhaseWeight_apply_eq_zero_iff a b (Real.cos theta.val) hb ha
          ⟨Real.cos_pos_of_mem_Ioo ⟨by linarith [theta.property.1.1, Real.pi_pos],
            theta.property.1.2⟩, Real.cos_le_one _⟩ C x hzero hx).mp hz)
    have he := weightedPhaseWeight_apply_smul a b (Real.cos theta.val) hb ha
      ⟨(Real.cos_pos_of_mem_Ioo ⟨by linarith [theta.property.1.1, Real.pi_pos],
        theta.property.1.2⟩).le, Real.cos_le_one _⟩ C x hx
    let lam := (((2 * Real.cos theta.val *
      Real.sqrt (1 - (min 1 (a * Real.cos theta.val / b)) ^ 2) : ℝ) : ℂ) * Complex.I)
    have hlam : lam ≠ 0 := by
      intro hz
      exact hne (he.trans (by change lam • x = 0; rw [hz, zero_smul]))
    refine ⟨lam⁻¹ • x, ?_⟩
    change W (lam⁻¹ • x) = x
    rw [map_smul, show W x = lam • x from he, smul_smul, inv_mul_cancel₀ hlam, one_smul]
  have hCJ : Commute C (K.reflection : E →L[ℂ] E) :=
    (K.commute_reflection_iff.mpr
      (Proposition35.section3CosAngleOperator_comm_projection K L).symm).symm
  have hSle : S ≤ W.kerᗮ := by
    refine iSup_le fun theta => sup_le (fun x hx => hmem theta x (hcos theta ⟨x, hx⟩)) ?_
    rintro x ⟨y, hy, rfl⟩
    apply hmem theta (K.reflection y)
    calc
      C (K.reflection y) = K.reflection (C y) :=
        congrArg (fun A : E →L[ℂ] E => A y) hCJ.eq
      _ = _ := by rw [hcos theta ⟨y, hy⟩, map_smul]
  apply le_antisymm ?_ hSle
  rw [← hrange]
  rintro x ⟨y, rfl⟩
  obtain ⟨n, m, e, angle, eps, hθ, hC0, hC1, hCf, hR0, _, _, hJ0, _⟩ :=
    SmoothedPhaseTransition.exists_subspace_paired_rotation_reflection_basis_complex K L hKL
  have hCp (r : Fin 2) (i : Fin n) : C (e (.inl (r, i))) =
      (Real.cos (angle i) : ℂ) • e (.inl (r, i)) := by
    fin_cases r
    · exact hC0 i
    · exact hC1 i
  have hWe (j) : W (e j) ∈ S := by
    rcases j with ⟨r, i⟩ | j
    · by_cases hright : angle i = Real.pi / 2
      · have hz : C (e (.inl (r, i))) = 0 := by
          rw [hCp, hright, Real.cos_pi_div_two, Complex.ofReal_zero, zero_smul]
        rw [show W (e (.inl (r, i))) = 0 from weightedPhaseWeight_apply_zero a b hb ha C _ hz]
        exact Submodule.zero_mem _
      have hθi : angle i ∈ Ioo 0 (Real.pi / 2) :=
        ⟨(hθ i).1, lt_of_le_of_ne (hθ i).2 hright⟩
      by_cases hinactive : b ≤ a * Real.cos (angle i)
      · rw [show W (e (.inl (r, i))) = 0 from
          (weightedPhaseWeight_apply_eq_zero_iff a b (Real.cos (angle i)) hb ha
            ⟨Real.cos_pos_of_mem_Ioo ⟨by linarith [hθi.1, Real.pi_pos], hθi.2⟩,
              Real.cos_le_one _⟩ C _ (e.orthonormal.ne_zero _) (hCp r i)).mpr hinactive]
        exact Submodule.zero_mem _
      let theta : weightedSupercriticalAngles a b := ⟨angle i, hθi, lt_of_not_ge hinactive⟩
      have heplus : e (.inl (0, i)) ∈ N theta :=
        Module.End.mem_eigenspace_iff.mpr (hR0 i)
      have heS : e (.inl (r, i)) ∈ S := by
        apply (le_iSup (fun theta => N theta ⊔ (N theta).map K.reflection.toLinearMap) theta)
        fin_cases r
        · exact Submodule.mem_sup_left heplus
        · apply Submodule.mem_sup_right
          exact ⟨e (.inl (0, i)), heplus, hJ0 i⟩
      rw [show W (e (.inl (r, i))) = _ from
        weightedPhaseWeight_apply_smul a b (Real.cos (angle i)) hb ha
          ⟨(Real.cos_pos_of_mem_Ioo ⟨by linarith [hθi.1, Real.pi_pos], hθi.2⟩).le,
            Real.cos_le_one _⟩ C _ (hCp r i)]
      exact S.smul_mem _ heS
    · rw [show W (e (.inr j)) = 0 from
        (weightedPhaseWeight_apply_eq_zero_iff a b 1 hb ha ⟨zero_lt_one, le_rfl⟩ C _
          (e.orthonormal.ne_zero _) (by simpa only [Complex.ofReal_one, one_smul] using hCf j)).mpr
            (by simpa only [mul_one] using hab.le)]
      exact Submodule.zero_mem _
  rw [← e.sum_repr' y, map_sum]
  apply S.sum_mem
  intro i _
  rw [map_smul]
  exact S.smul_mem _ (hWe i)

/-- The normalized compatible phase projections are exactly the
commuting projections supported on the finitely many actual active
canonical eigenspace pairs. -/
theorem weightedNormalizedPhaseProjections_eq_paired_projection_space
    (a b : ℝ) (hb : 0 < b) (hab : b < a)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L) :
    let U : unitary (E →L[ℂ] E) :=
      ⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
        nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩
    weightedNormalizedPhaseProjections a b K L hKL =
      unitaryPairedProjectionSpace U K.reflection
        (fun theta : weightedActiveRotationAngles a b U =>
          Complex.exp ((theta.val : ℂ) * Complex.I)) := by
  let U : unitary (E →L[ℂ] E) :=
    ⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
      nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩
  let N := fun theta : weightedSupercriticalAngles a b =>
    Module.End.eigenspace (U : E →L[ℂ] E).toLinearMap
      (Complex.exp ((theta.val : ℂ) * Complex.I))
  let S := ⨆ theta, N theta ⊔ (N theta).map K.reflection.toLinearMap
  let S' := ⨆ theta : weightedActiveRotationAngles a b U,
    weightedRotationMultiplicitySpace a b U theta ⊔
      (weightedRotationMultiplicitySpace a b U theta).map K.reflection.toLinearMap
  have hS : S = S' := by
    apply le_antisymm
    · refine iSup_le fun theta => ?_
      by_cases hbot : N theta = ⊥
      · simp only [hbot, Submodule.map_bot, sup_idem]
        exact bot_le
      · let eta : weightedActiveRotationAngles a b U := ⟨theta.val, theta.property, hbot⟩
        exact le_iSup (fun eta => weightedRotationMultiplicitySpace a b U eta ⊔
          (weightedRotationMultiplicitySpace a b U eta).map K.reflection.toLinearMap) eta
    · refine iSup_le fun eta => ?_
      let theta : weightedSupercriticalAngles a b := ⟨eta.val, eta.property.1⟩
      exact le_iSup (fun theta => N theta ⊔ (N theta).map K.reflection.toLinearMap) theta
  have hsupport := weightedPhaseWeight_orthogonal_ker_eq_paired_eigenspace_sum a b hb hab K L hKL
  change (weightedPhaseWeight a b (Proposition35.section3CosAngleOperator K L)).kerᗮ = S at hsupport
  ext P
  change (IsStarProjection P ∧ Commute P (U : E →L[ℂ] E) ∧
    (∀ x, P (K.reflection x) = K.reflection (P x)) ∧
    ∀ x, P x ∈ (weightedPhaseWeight a b (Proposition35.section3CosAngleOperator K L)).kerᗮ) ↔
    (IsStarProjection P ∧ Commute P (U : E →L[ℂ] E) ∧
      (∀ x, P (K.reflection x) = K.reflection (P x)) ∧ ∀ x, P x ∈ S')
  rw [hsupport, hS]

/-- Every complex Charbonnier optimizer is parametrized bijectively by one
arbitrary orthogonal projection on each actual active multiplicity space
and one independent defect unitary. The index set is finite and no frame
is prescribed to the competing ambient transporters. -/
theorem exists_smoothed_multiplicity_parameter_equiv
    (tau : ℝ) (htau : 0 < tau)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L) :
    let U : unitary (E →L[ℂ] E) :=
      ⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
        nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩
    let a := smoothingRadius tau
    let N := weightedRotationMultiplicitySpace a a⁻¹ U
    ∃ e : ((∀ theta : weightedActiveRotationAngles a a⁻¹ U,
        {Q : N theta →L[ℂ] N theta // IsStarProjection Q}) ×
          (halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)) ≃
            smoothedTransportMinimizers tau K L,
      ∀ data, (∀ x : halmosSourceDefect K L, (e data).val x = (data.2 x : E)) ∧
        (∀ y : halmosTargetDefect K L, (e data).val y = (data.2.symm y : E)) ∧
        ∃ P ∈ weightedNormalizedPhaseProjections a a⁻¹ K L hKL,
          (∀ theta (x : N theta), P x = ((data.1 theta).val x : E)) ∧
          Proposition35.section3CosAngleOperator K L *
              ((Unitary.linearIsometryEquiv U).trans (e data).val.symm : E →L[ℂ] E) =
            Proposition35.section3CosAngleOperator K L *
              (weightedPhaseFactor a a⁻¹ (Proposition35.section3CosAngleOperator K L) * P +
                star (weightedPhaseFactor a a⁻¹ (Proposition35.section3CosAngleOperator K L)) *
                  (1 - P)) := by
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
  obtain ⟨eP, heP⟩ := exists_unitary_paired_projection_equiv U K.reflection
    K.reflection_involutive
    (nonacuteDirectRotation_reflection_eq_reflection_star K L (finiteCrossedDefectEquiv K L hKL))
    mu hmu hinj hconj
  have hspaces := weightedNormalizedPhaseProjections_eq_paired_projection_space
    a a⁻¹ (inv_pos.mpr ha0) (((inv_lt_one₀ ha0).mpr ha).trans ha) K L hKL
  let eP' := eP.trans (Set.equivOfEq hspaces.symm)
  obtain ⟨eT, heT, _⟩ := exists_smoothed_normalized_parameter_equiv tau htau K L hKL
  let e := (Equiv.prodCongr eP'
    (Equiv.refl (halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L))).trans eT
  refine ⟨e, fun data => ?_⟩
  have hdata := heT (eP' data.1, data.2)
  refine ⟨hdata.1, hdata.2.1, (eP' data.1).val, (eP' data.1).property, ?_, hdata.2.2⟩
  exact heP data.1

/-- All optimizers are in algebraic bijection with a finite product of
rank-stratified subspace choices and the independent defect unitary space.
The strata are ordinary subspaces of fixed dimension; no manifold topology
or dimension theorem is asserted by this equivalence. -/
theorem nonempty_smoothed_rank_stratified_parameter_equiv
    (tau : ℝ) (htau : 0 < tau)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L) :
    let a := smoothingRadius tau
    let U : unitary (E →L[ℂ] E) :=
      ⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
        nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩
    let N := weightedRotationMultiplicitySpace a a⁻¹ U
    Nonempty (((∀ theta : weightedActiveRotationAngles a a⁻¹ U,
      Σ r : Fin (Module.finrank ℂ (N theta) + 1),
        {M : Submodule ℂ (N theta) // Module.finrank ℂ M = r.val}) ×
      (halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)) ≃
        smoothedTransportMinimizers tau K L) := by
  obtain ⟨e, _⟩ := exists_smoothed_multiplicity_parameter_equiv tau htau K L hKL
  exact ⟨(Equiv.prodCongr (Equiv.piCongrRight fun _ => starProjectionRankEquiv.symm)
    (Equiv.refl _)).trans e⟩

/-- When each active multiplicity is one, the complete phase family is
one independent Boolean per distinct active angle. Right-defect freedom
remains an independent unitary parameter. -/
theorem nonempty_smoothed_boolean_parameter_equiv
    (tau : ℝ) (htau : 0 < tau)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L) :
    let a := smoothingRadius tau
    let U : unitary (E →L[ℂ] E) :=
      ⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
        nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩
    (∀ theta : weightedActiveRotationAngles a a⁻¹ U,
      Module.finrank ℂ (weightedRotationMultiplicitySpace a a⁻¹ U theta) = 1) →
    Nonempty (((weightedActiveRotationAngles a a⁻¹ U → Bool) ×
      (halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)) ≃
        smoothedTransportMinimizers tau K L) := by
  classical
  let a := smoothingRadius tau
  dsimp only
  intro hdim
  obtain ⟨e, _⟩ := exists_smoothed_multiplicity_parameter_equiv tau htau K L hKL
  exact ⟨(Equiv.prodCongr (Equiv.piCongrRight fun theta =>
    (exists_bool_equiv_starProjections_of_finrank_eq_one (hdim theta)).choose)
      (Equiv.refl _)).trans e⟩

/-- With no right-angle defects and simple active multiplicities, the
exact number of all ambient global optimizers is two to the number of
distinct active angles. Inactive multiplicities are unrestricted. -/
theorem natCard_smoothedTransportMinimizers_of_simple_active_angles
    (tau : ℝ) (htau : 0 < tau)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L)
    (hdefect : Module.finrank ℂ (halmosSourceDefect K L) = 0) :
    let a := smoothingRadius tau
    let U : unitary (E →L[ℂ] E) :=
      ⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
        nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩
    (∀ theta : weightedActiveRotationAngles a a⁻¹ U,
      Module.finrank ℂ (weightedRotationMultiplicitySpace a a⁻¹ U theta) = 1) →
    Nat.card (smoothedTransportMinimizers tau K L) =
      2 ^ Nat.card (weightedActiveRotationAngles a a⁻¹ U) := by
  classical
  let a := smoothingRadius tau
  dsimp only
  let U : unitary (E →L[ℂ] E) :=
    ⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
      nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩
  intro hdim
  obtain ⟨e⟩ := nonempty_smoothed_boolean_parameter_equiv tau htau K L hKL hdim
  let D := halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L
  let d := finiteCrossedDefectEquiv K L hKL
  have htgt : Module.finrank ℂ (halmosTargetDefect K L) = 0 :=
    d.toLinearEquiv.finrank_eq.symm.trans hdefect
  let : Subsingleton (halmosTargetDefect K L) := Module.finrank_zero_iff.mp htgt
  let : Subsingleton D := ⟨fun d e => by
    apply LinearIsometryEquiv.ext
    intro x
    exact Subsingleton.elim _ _⟩
  let : Nonempty D := ⟨d⟩
  let : Fintype (weightedActiveRotationAngles a a⁻¹ U) :=
    (finite_weightedActiveRotationAngles a a⁻¹ U).fintype
  calc
    Nat.card (smoothedTransportMinimizers tau K L) =
        Nat.card ((weightedActiveRotationAngles a a⁻¹ U → Bool) × D) := Nat.card_congr e.symm
    _ = 2 ^ Nat.card (weightedActiveRotationAngles a a⁻¹ U) := by
      rw [Nat.card_prod, Nat.card_fun, Nat.card_unique (α := D), mul_one]
      simp [Nat.card_eq_fintype_card]

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

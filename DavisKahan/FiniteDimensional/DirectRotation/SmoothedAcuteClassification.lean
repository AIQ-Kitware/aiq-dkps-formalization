/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedProjectionOptimizers
public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedOptimizerNoMixing
public import ForTauCeti.Analysis.InnerProductSpace.JointEigenbasis
public import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Projection
public import TauCeti.Analysis.InnerProductSpace.FunctionalCalculusComparison
public import Mathlib.LinearAlgebra.Complex.Module
public import DavisKahan.Geometry.Angle.AcuteCosine

/-!
# Complete projection classification of acute smoothed optimizers

The positive spectral projection of the imaginary part of the relative
unitary supplies an intrinsic phase selection. Together with arbitrary
compatible projection attainment, this classifies every optimizer when
the principal cosine is injective. Zero and critical angles are included;
right-angle defect spaces are excluded by the injectivity hypothesis.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

open scoped ComplexStarModule InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

attribute [local instance 100] ContinuousLinearMap.realAlgebra
  ContinuousLinearMap.realIsScalarTower ContinuousLinearMap.continuousFunctionalCalculusReal
attribute [local instance] ContinuousLinearMap.instStarOrderedRingRCLike

omit [FiniteDimensional ℂ E] in
private theorem unitary_star_commute (Z : E ≃ₗᵢ[ℂ] E) (A : E →L[ℂ] E)
    (h : Commute (Z : E →L[ℂ] E) A) : Commute (star (Z : E →L[ℂ] E)) A := by
  rw [show star (Z : E →L[ℂ] E) = (Z.symm : E →L[ℂ] E) from Z.adjoint_eq_symm]
  ext x
  change Z.symm (A x) = A (Z.symm x)
  apply Z.injective
  rw [Z.apply_symm_apply]
  have hx := DFunLike.congr_fun h.eq (Z.symm x)
  change Z (A (Z.symm x)) = A (Z (Z.symm x)) at hx
  rw [Z.apply_symm_apply] at hx
  exact hx.symm

/-- Every attaining ambient weighted transporter for an injective principal
cosine has the compatible projection form. The witness is the positive
spectral projection of the imaginary part of its relative unitary, so it
vanishes on inactive directions where the two phase choices coincide. -/
theorem minimizing_weighted_transport_positive_phase_projection_complex
    (a b : ℝ) (hb : 0 < b) (hab : b < a)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L)
    (T : E ≃ₗᵢ[ℂ] E) (hT : K.map T.toLinearMap = L)
    (hatt : UnitarilyInvariantSeminorm.nuclear ℂ E E
      ((a : ℂ) • T.toLinearMap - (b : ℂ) • LinearMap.id) =
        weightedRotationMinimum a b (Proposition35.section3CosAngleOperator K L))
    (hinj : Function.Injective (Proposition35.section3CosAngleOperator K L)) :
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
        nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
          unitary (E →L[ℂ] E))
    let Z := (R.trans T.symm : E →L[ℂ] E)
    let U := weightedPhaseFactor a b (Proposition35.section3CosAngleOperator K L)
    let P := cfc ((Set.Ioi 0).indicator (1 : ℝ → ℝ)) (ℑ Z : E →L[ℂ] E)
    IsStarProjection P ∧ Commute P (R : E →L[ℂ] E) ∧
      (∀ x, P (K.reflection x) = K.reflection (P x)) ∧
      Z = U * P + star U * (1 - P) := by
  classical
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
      nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
        unitary (E →L[ℂ] E))
  let Z' := R.trans T.symm
  let Z : E →L[ℂ] E := Z'
  let C := Proposition35.section3CosAngleOperator K L
  let G : E →L[ℂ] E := ℑ Z
  let P := cfc ((Set.Ioi 0).indicator (1 : ℝ → ℝ)) G
  let U := weightedPhaseFactor a b C
  have hCpos := (ContinuousLinearMap.nonneg_iff_isPositive).mp
    (Proposition35.section3CosAngleOperator_nonneg K L)
  have hC : IsSelfAdjoint C := hCpos.isSelfAdjoint
  have hG : IsSelfAdjoint G := (ℑ Z).property
  let : IsStarNormal C := hC.isStarNormal
  have hZR : Commute Z (R : E →L[ℂ] E) :=
    minimizing_weighted_transport_relative_commutes_rotation_of_injective_cosine_complex
      a b hb hab K L hKL T hT hatt hinj
  have hZJ : Commute Z (K.reflection : E →L[ℂ] E) := by
    ext x
    exact K.relative_transport_commutes_reflection L R T
      ((K.map_eq_iff_intertwines_reflection L R).mpr
        (nonacuteDirectRotation_reflection_intertwines K L (finiteCrossedDefectEquiv K L hKL)))
      hT x
  obtain ⟨_, _, _, _, hZC, _⟩ :=
    minimizing_weighted_transport_twisted_average_complex a b hb hab K L hKL T hT hatt
  have hGC (A : E →L[ℂ] E) (hZA : Commute Z A) : Commute G A := by
    dsimp only [G]
    rw [imaginaryPart_apply_coe]
    exact ((hZA.sub_left (unitary_star_commute Z' A hZA)).smul_left
      ((2 : ℝ)⁻¹)).smul_left (-Complex.I)
  have hPR : Commute P (R : E →L[ℂ] E) := (hGC _ hZR).cfc_real _
  have hPJ : Commute P (K.reflection : E →L[ℂ] E) := (hGC _ hZJ).cfc_real _
  refine ⟨TauCeti.isStarProjection_cfc_indicator G (Set.Ioi 0), hPR,
    fun x => DFunLike.congr_fun hPJ.eq x, ?_⟩
  have hCG : Commute C.toLinearMap G.toLinearMap := by
    change C.toLinearMap * G.toLinearMap = G.toLinearMap * C.toLinearMap
    exact congrArg ContinuousLinearMap.toLinearMap (hGC C hZC).eq.symm
  obtain ⟨e, c, g, hCe, hGe⟩ := hC.isSymmetric.exists_joint_orthonormalBasis_real
    hG.isSymmetric hCG
  change ∀ i, C (e i) = (c i : ℂ) • e i at hCe
  change ∀ i, G (e i) = (g i : ℂ) • e i at hGe
  have hc (i) : 0 < c i := by
    have hnonneg : 0 ≤ c i := by
      have hn : 0 ≤ (inner ℂ (e i) (C (e i))).re := hCpos.re_inner_nonneg_right (e i)
      simpa only [hCe, inner_smul_right, e.inner_eq_one, mul_one, Complex.ofReal_re] using hn
    have hne : c i ≠ 0 := by
      intro hz
      have hx : e i = 0 := by
        apply hinj
        change C (e i) = C 0
        rw [show C (e i) = _ from hCe i, hz, Complex.ofReal_zero, zero_smul, map_zero]
      exact e.orthonormal.ne_zero i hx
    exact lt_of_le_of_ne hnonneg hne.symm
  have hc1 (i) : c i ≤ 1 := by
    have hsum := DFunLike.congr_fun
      (nonacuteDirectRotation_add_star_eq_two_cosine K L (finiteCrossedDefectEquiv K L hKL))
      (e i)
    change R (e i) + star (R : E →L[ℂ] E) (e i) = C (e i) + C (e i) at hsum
    rw [show C (e i) = _ from hCe i,
      show star (R : E →L[ℂ] E) = (R.symm : E →L[ℂ] E) from R.adjoint_eq_symm] at hsum
    change R (e i) + R.symm (e i) = (c i : ℂ) • e i + (c i : ℂ) • e i at hsum
    have hn := norm_add_le (R (e i)) (R.symm (e i))
    rw [hsum, ← add_smul] at hn
    have hn' : c i + c i ≤ 1 + 1 := by
      simpa [norm_smul, ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith [hc i] : 0 < c i + c i), e.norm_eq_one] using hn
    linarith
  apply ContinuousLinearMap.coe_injective
  apply e.toBasis.ext
  intro i
  let beta := min 1 (a * c i / b)
  let s := Real.sqrt (1 - beta ^ 2)
  have hreal := minimizing_weighted_transport_relative_real_part_complex
    a b hb hab K L hKL T hT hatt (c i) (hc i) (e i) (hCe i)
  have hre : (ℜ Z : E →L[ℂ] E) (e i) = (beta : ℂ) • e i := by
    rw [realPart_apply_coe]
    change (2 : ℝ)⁻¹ • (Z (e i) + star Z (e i)) = _
    rw [hreal]
    simp [beta, ← Complex.coe_smul, smul_smul]
  have hZe : Z (e i) = ((beta : ℂ) + (g i : ℂ) * Complex.I) • e i := by
    have h := DFunLike.congr_fun (realPart_add_I_smul_imaginaryPart Z) (e i)
    change (ℜ Z : E →L[ℂ] E) (e i) + Complex.I • G (e i) = Z (e i) at h
    rw [hre, show G (e i) = _ from hGe i] at h
    rw [← h]
    module
  have hnorm : ‖((beta : ℂ) + (g i : ℂ) * Complex.I)‖ = 1 := by
    have h := Z'.norm_map (e i)
    change ‖Z (e i)‖ = ‖e i‖ at h
    simpa only [hZe, norm_smul, e.norm_eq_one, mul_one] using h
  have hs : s = |g i| := by
    have hn := Complex.normSq_eq_norm_sq ((beta : ℂ) + (g i : ℂ) * Complex.I)
    simp only [Complex.normSq_apply, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_self,
      add_zero, Complex.add_im, Complex.mul_im, mul_one, zero_add, hnorm, one_pow] at hn
    have heq : 1 - beta ^ 2 = g i ^ 2 := by nlinarith
    rw [show s = Real.sqrt (1 - beta ^ 2) from rfl, heq, Real.sqrt_sq_eq_abs]
  have hUe : U (e i) = ((beta : ℂ) + (s : ℂ) * Complex.I) • e i := by
    rw [show U = cfc (weightedPhaseSymbol a b) C from rfl,
      ContinuousLinearMap.cfc_apply_of_apply_eq_smul_of_isStarNormal _ (hCe i)]
    rw [weightedPhaseSymbol_eq_clip a b (c i) hb (hb.le.trans hab.le) ⟨(hc i).le, hc1 i⟩]
  have hUs : star U (e i) = ((beta : ℂ) - (s : ℂ) * Complex.I) • e i := by
    have h := unitary_star_apply_of_apply_eq_smul
      (⟨U, weightedPhaseFactor_mem_unitary a b C inferInstance⟩ : unitary (E →L[ℂ] E))
      _ (by
        have hn := norm_circlePhase 1 (optimalWeightedPhase a b (Real.arccos (c i))) zero_le_one
        change ‖weightedPhaseSymbol a b (c i : ℂ)‖ = 1 at hn
        rwa [weightedPhaseSymbol_eq_clip a b (c i) hb (hb.le.trans hab.le) ⟨(hc i).le, hc1 i⟩] at hn)
      (e i) hUe
    simpa [RCLike.star_def, Complex.conj_ofReal, Complex.conj_I, sub_eq_add_neg] using h
  have hPe : P (e i) = (if 0 < g i then (1 : ℂ) else 0) • e i := by
    have h := ContinuousLinearMap.cfc_apply_of_apply_eq_smul
      ((Set.Ioi 0).indicator (1 : ℝ → ℝ)) (hGe i) hG
    simpa [P, Set.indicator_apply, Set.mem_Ioi] using h
  change Z (e i) = U (P (e i)) + star U (e i - P (e i))
  by_cases hg : 0 < g i
  · have hs' : s = g i := hs.trans (abs_of_pos hg)
    rw [hPe, ite_eq_left hg, one_smul, sub_self, map_zero, add_zero, hUe, hZe, hs']
  · have hs' : s = -g i := hs.trans (abs_of_nonpos (le_of_not_gt hg))
    rw [hPe, ite_eq_right hg, zero_smul, map_zero, sub_zero, zero_add, hUs, hZe, hs']
    simp only [Complex.ofReal_neg, neg_mul, sub_neg_eq_add]

/-- Complete ambient weighted optimizer classification when the principal
cosine is injective. The compatible projection may mix arbitrary vectors
within a repeated rotation phase, and the formula imposes no artificial
simplicity assumption. On inactive directions its parameter is redundant. -/
theorem minimizing_weighted_transport_iff_projection_of_injective_cosine_complex
    (a b : ℝ) (hb : 0 < b) (hab : b < a)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L)
    (T : E ≃ₗᵢ[ℂ] E) (hT : K.map T.toLinearMap = L)
    (hinj : Function.Injective (Proposition35.section3CosAngleOperator K L)) :
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
        nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
          unitary (E →L[ℂ] E))
    let U := weightedPhaseFactor a b (Proposition35.section3CosAngleOperator K L)
    UnitarilyInvariantSeminorm.nuclear ℂ E E
      ((a : ℂ) • T.toLinearMap - (b : ℂ) • LinearMap.id) =
        weightedRotationMinimum a b (Proposition35.section3CosAngleOperator K L) ↔
      ∃ P : E →L[ℂ] E, IsStarProjection P ∧ Commute P (R : E →L[ℂ] E) ∧
        (∀ x, P (K.reflection x) = K.reflection (P x)) ∧
        (R.trans T.symm : E →L[ℂ] E) = U * P + star U * (1 - P) := by
  constructor
  · intro hatt
    obtain ⟨hP, hPR, hPJ, hphase⟩ :=
      minimizing_weighted_transport_positive_phase_projection_complex
        a b hb hab K L hKL T hT hatt hinj
    exact ⟨_, hP, hPR, hPJ, hphase⟩
  · rintro ⟨P, hP, hPR, hPJ, hphase⟩
    obtain ⟨S, _, hSphase, hatt, _⟩ := exists_weighted_transport_from_projection_complex
      a b hb hab K L hKL P hP hPR hPJ
    have hTS := LinearIsometryEquiv.eq_of_relative_eq _ (hphase.trans hSphase.symm)
    simpa only [hTS] using hatt

/-- Every Charbonnier minimizer, and only a minimizer, has the compatible
projection form for an injective principal cosine. The comparison quantifier
ranges over all ambient complex unitary transporters. -/
theorem smoothed_transport_isMin_iff_projection_of_injective_cosine_complex
    (tau : ℝ) (htau : 0 < tau)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L)
    (T : E ≃ₗᵢ[ℂ] E) (hT : K.map T.toLinearMap = L)
    (hinj : Function.Injective (Proposition35.section3CosAngleOperator K L)) :
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
        nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
          unitary (E →L[ℂ] E))
    let U := weightedPhaseFactor (smoothingRadius tau) (smoothingRadius tau)⁻¹
      (Proposition35.section3CosAngleOperator K L)
    (∀ S : E ≃ₗᵢ[ℂ] E, K.map S.toLinearMap = L →
      smoothedDisplacementCost tau T.toLinearMap ≤ smoothedDisplacementCost tau S.toLinearMap) ↔
      ∃ P : E →L[ℂ] E, IsStarProjection P ∧ Commute P (R : E →L[ℂ] E) ∧
        (∀ x, P (K.reflection x) = K.reflection (P x)) ∧
        (R.trans T.symm : E →L[ℂ] E) = U * P + star U * (1 - P) := by
  let a := smoothingRadius tau
  have ha : 1 < a := one_lt_smoothingRadius tau htau
  have ha0 : 0 < a := zero_lt_one.trans ha
  constructor
  · intro hmin
    exact (minimizing_weighted_transport_iff_projection_of_injective_cosine_complex
      a a⁻¹ (inv_pos.mpr ha0) (((inv_lt_one₀ ha0).mpr ha).trans ha) K L hKL T hT hinj).mp
      (smoothed_minimizer_weighted_cost_eq_complex tau htau K L hKL T hT hmin)
  · rintro ⟨P, hP, hPR, hPJ, hphase⟩
    obtain ⟨S, _, hSphase, _, hmin⟩ := exists_smoothed_transport_from_projection_complex
      tau htau K L hKL P hP hPR hPJ
    have hTS := LinearIsometryEquiv.eq_of_relative_eq _ (hphase.trans hSphase.symm)
    simpa only [hTS] using hmin

/-- Complete Charbonnier optimizer classification for a pair with projection
gap strictly below one. This includes equal, zero, critical, and supercritical
acute principal angles and arbitrary fixed ambient directions. -/
theorem smoothed_transport_isMin_iff_projection_of_isUniformlyAcute_complex
    (tau : ℝ) (htau : 0 < tau)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L)
    (hacute : IsUniformlyAcute K L)
    (T : E ≃ₗᵢ[ℂ] E) (hT : K.map T.toLinearMap = L) :
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
        nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
          unitary (E →L[ℂ] E))
    let U := weightedPhaseFactor (smoothingRadius tau) (smoothingRadius tau)⁻¹
      (Proposition35.section3CosAngleOperator K L)
    (∀ S : E ≃ₗᵢ[ℂ] E, K.map S.toLinearMap = L →
      smoothedDisplacementCost tau T.toLinearMap ≤ smoothedDisplacementCost tau S.toLinearMap) ↔
      ∃ P : E →L[ℂ] E, IsStarProjection P ∧ Commute P (R : E →L[ℂ] E) ∧
        (∀ x, P (K.reflection x) = K.reflection (P x)) ∧
        (R.trans T.symm : E →L[ℂ] E) = U * P + star U * (1 - P) :=
  smoothed_transport_isMin_iff_projection_of_injective_cosine_complex tau htau K L hKL T hT
    (Proposition35.section3CosAngleOperator_injective_of_isUniformlyAcute K L hacute)

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

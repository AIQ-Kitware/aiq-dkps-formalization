/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.SmoothedNonacutePhases
import DavisKahan.FiniteDimensional.DirectRotation.SmoothedProjectionOptimizers
import DavisKahan.FiniteDimensional.DirectRotation.KernelCostSplitting
import ForTauCeti.Analysis.InnerProductSpace.JointEigenbasis
import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Projection
import TauCeti.Analysis.InnerProductSpace.FunctionalCalculusComparison
import Mathlib.LinearAlgebra.Complex.Module

/-!
# Intrinsic phase selection including right-angle defects

The positive spectral projection of `Im(C * (T*R))` selects every
optimizer's positive phase away from the cosine kernel, and vanishes on
that kernel. The kernel's reflecting action remains independent.
-/

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

open scoped ComplexStarModule InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

attribute [local instance 100] ContinuousLinearMap.realAlgebra
  ContinuousLinearMap.realIsScalarTower ContinuousLinearMap.continuousFunctionalCalculusReal
attribute [local instance] ContinuousLinearMap.instStarOrderedRingRCLike

omit [FiniteDimensional ℂ E] in
private theorem star_unitary_commute (V : unitary (E →L[ℂ] E)) (A : E →L[ℂ] E)
    (h : Commute (V : E →L[ℂ] E) A) : Commute (star (V : E →L[ℂ] E)) A := by
  have hu : Commute (↑(Unitary.toUnits V) : E →L[ℂ] E) A := h
  have hi := hu.units_inv_left
  change Commute (star (V : E →L[ℂ] E)) A at hi
  exact hi

omit [FiniteDimensional ℂ E] in
private theorem imaginaryPart_commute_unitary
    (A : E →L[ℂ] E) (V : unitary (E →L[ℂ] E))
    (h : Commute A (V : E →L[ℂ] E)) :
    Commute (ℑ A : E →L[ℂ] E) (V : E →L[ℂ] E) := by
  have hs : Commute (star A) (V : E →L[ℂ] E) :=
    (star_unitary_commute V A h.symm).symm.star_left
  rw [imaginaryPart_apply_coe]
  exact ((h.sub_left hs).smul_left ((2 : ℝ)⁻¹)).smul_left (-Complex.I)

omit [FiniteDimensional ℂ E] in
private theorem commute_of_relative_left_mul_eq
    (C : E →L[ℂ] E) (hC : IsSelfAdjoint C) (R T S : E ≃ₗᵢ[ℂ] E)
    (hSC : Commute (S : E →L[ℂ] E) C)
    (h : C * (R.trans T.symm : E →L[ℂ] E) =
      C * (R.trans S.symm : E →L[ℂ] E)) : Commute (T : E →L[ℂ] E) C := by
  have hTunit : (T : E →L[ℂ] E) ∈ unitary (E →L[ℂ] E) :=
    (Unitary.linearIsometryEquiv.symm T).property
  have hSunit : (S : E →L[ℂ] E) ∈ unitary (E →L[ℂ] E) :=
    (Unitary.linearIsometryEquiv.symm S).property
  have hRunit : (R : E →L[ℂ] E) ∈ unitary (E →L[ℂ] E) :=
    (Unitary.linearIsometryEquiv.symm R).property
  have hrel : C * star (T : E →L[ℂ] E) = C * star (S : E →L[ℂ] E) := by
    have heq := congrArg (fun B : E →L[ℂ] E => B * (R.symm : E →L[ℂ] E)) h
    change C * ((T.symm : E →L[ℂ] E) * (R : E →L[ℂ] E)) * (R.symm : E →L[ℂ] E) =
      C * ((S.symm : E →L[ℂ] E) * (R : E →L[ℂ] E)) * (R.symm : E →L[ℂ] E) at heq
    rw [← T.adjoint_eq_symm, ← S.adjoint_eq_symm, ← R.adjoint_eq_symm] at heq
    change C * (star (T : E →L[ℂ] E) * (R : E →L[ℂ] E)) * star (R : E →L[ℂ] E) =
      C * (star (S : E →L[ℂ] E) * (R : E →L[ℂ] E)) * star (R : E →L[ℂ] E) at heq
    simpa only [mul_assoc, Unitary.mul_star_self_of_mem hRunit, mul_one] using heq
  have hforward : (T : E →L[ℂ] E) * C = (S : E →L[ℂ] E) * C := by
    simpa only [star_mul, hC.star_eq, star_star] using congrArg star hrel
  have hSCstar : (S : E →L[ℂ] E) * (C * star (S : E →L[ℂ] E)) = C := by
    rw [← mul_assoc, hSC.eq, mul_assoc, Unitary.mul_star_self_of_mem hSunit, mul_one]
  change (T : E →L[ℂ] E) * C = C * (T : E →L[ℂ] E)
  calc
    (T : E →L[ℂ] E) * C = (S : E →L[ℂ] E) * C := hforward
    _ = (S : E →L[ℂ] E) * (C * star (T : E →L[ℂ] E)) * (T : E →L[ℂ] E) := by
      rw [mul_assoc, mul_assoc, Unitary.star_mul_self_of_mem hTunit, mul_one]
    _ = (S : E →L[ℂ] E) * (C * star (S : E →L[ℂ] E)) * (T : E →L[ℂ] E) := by
      rw [hrel]
    _ = C * (T : E →L[ℂ] E) := by
      rw [hSCstar]

/-- Every attaining ambient weighted transporter has a compatible phase
projection modulo the actual right-angle kernel. The projection is the
positive spectral selection of the cosine-weighted imaginary relative
unitary, and is zero on the kernel. No acuteness assumption is imposed. -/
theorem minimizing_weighted_transport_positive_phase_projection_mod_kernel_complex
    (a b : ℝ) (hb : 0 < b) (hab : b < a)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L)
    (T : E ≃ₗᵢ[ℂ] E) (hT : K.map T.toLinearMap = L)
    (hatt : UnitarilyInvariantSeminorm.nuclear ℂ E E
      ((a : ℂ) • T.toLinearMap - (b : ℂ) • LinearMap.id) =
        weightedRotationMinimum a b (Proposition35.section3CosAngleOperator K L)) :
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
        nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
          unitary (E →L[ℂ] E))
    let C := Proposition35.section3CosAngleOperator K L
    let Z := (R.trans T.symm : E →L[ℂ] E)
    let U := weightedPhaseFactor a b C
    let P := cfc ((Set.Ioi 0).indicator (1 : ℝ → ℝ)) (ℑ (C * Z) : E →L[ℂ] E)
    IsStarProjection P ∧ Commute P (R : E →L[ℂ] E) ∧
      (∀ x, P (K.reflection x) = K.reflection (P x)) ∧
      (∀ x, C x = 0 → P x = 0) ∧ C * Z = C * (U * P + star U * (1 - P)) := by
  classical
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
      nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
        unitary (E →L[ℂ] E))
  let Z' := R.trans T.symm
  let Z : E →L[ℂ] E := Z'
  let C := Proposition35.section3CosAngleOperator K L
  let A := C * Z
  let G : E →L[ℂ] E := ℑ Z
  let H : E →L[ℂ] E := ℑ A
  let P := cfc ((Set.Ioi 0).indicator (1 : ℝ → ℝ)) H
  let U := weightedPhaseFactor a b C
  have hCpos := (ContinuousLinearMap.nonneg_iff_isPositive).mp
    (Proposition35.section3CosAngleOperator_nonneg K L)
  have hC : IsSelfAdjoint C := hCpos.isSelfAdjoint
  have hG : IsSelfAdjoint G := (ℑ Z).property
  have hH : IsSelfAdjoint H := (ℑ A).property
  let : IsStarNormal C := hC.isStarNormal
  obtain ⟨_, _, _, _, hZC, _⟩ :=
    minimizing_weighted_transport_twisted_average_complex a b hb hab K L hKL T hT hatt
  change Commute Z C at hZC
  have hZJ : Commute Z (K.reflection : E →L[ℂ] E) := by
    ext x
    exact K.relative_transport_commutes_reflection L R T
      ((K.map_eq_iff_intertwines_reflection L R).mpr
        (nonacuteDirectRotation_reflection_intertwines K L (finiteCrossedDefectEquiv K L hKL)))
      hT x
  have hCJ : Commute C (K.reflection : E →L[ℂ] E) := by
    ext x
    change C (K.reflection x) = K.reflection (C x)
    have h := DFunLike.congr_fun (Proposition35.section3CosAngleOperator_comm_projection K L).eq x
    change C (K.starProjection x) = K.starProjection (C x) at h
    rw [Submodule.reflection_apply, Submodule.reflection_apply, map_sub, map_nsmul, h]
  have hGA (B : E →L[ℂ] E) (hZB : Commute Z B) : Commute G B := by
    dsimp only [G]
    rw [imaginaryPart_apply_coe]
    have hs := star_unitary_commute (Unitary.linearIsometryEquiv.symm Z') B hZB
    exact ((hZB.sub_left hs).smul_left ((2 : ℝ)⁻¹)).smul_left (-Complex.I)
  have hZstarC : Commute (star Z) C := by
    change star Z * C = C * star Z
    simpa only [star_mul, hC.star_eq] using (congrArg star hZC.eq).symm
  have hHG : H = C * G := by
    change (ℑ (C * Z) : E →L[ℂ] E) = C * (ℑ Z : E →L[ℂ] E)
    rw [imaginaryPart_apply_coe, imaginaryPart_apply_coe, star_mul, hC.star_eq, hZstarC.eq]
    simp only [mul_smul_comm, mul_sub]
  have hAR : Commute A (R : E →L[ℂ] E) :=
    minimizing_weighted_transport_cosine_mul_relative_commutes_rotation_complex
      a b hb hab K L hKL T hT hatt
  have hHR : Commute H (R : E →L[ℂ] E) :=
    imaginaryPart_commute_unitary A (Unitary.linearIsometryEquiv.symm R) hAR
  have hHJ : Commute H (K.reflection : E →L[ℂ] E) :=
    imaginaryPart_commute_unitary A (Unitary.linearIsometryEquiv.symm K.reflection)
      (hCJ.mul_left hZJ)
  have hPR : Commute P (R : E →L[ℂ] E) := hHR.cfc_real _
  have hPJ : Commute P (K.reflection : E →L[ℂ] E) := hHJ.cfc_real _
  have hHker (x : E) (hx : C x = 0) : H x = 0 := by
    rw [hHG]
    change C (G x) = 0
    have h := DFunLike.congr_fun (hGA C hZC).eq x
    change G (C x) = C (G x) at h
    rw [hx, map_zero] at h
    exact h.symm
  have hPker (x : E) (hx : C x = 0) : P x = 0 := by
    have h := ContinuousLinearMap.cfc_apply_of_apply_eq_smul
      ((Set.Ioi 0).indicator (1 : ℝ → ℝ))
      (show H x = (0 : ℂ) • x by rw [hHker x hx, zero_smul]) hH
    change P x = (((Set.Ioi 0).indicator (1 : ℝ → ℝ) 0 : ℝ) : ℂ) • x at h
    norm_num [Set.indicator_apply] at h
    exact h
  refine ⟨TauCeti.isStarProjection_cfc_indicator H (Set.Ioi 0), hPR,
    fun x => DFunLike.congr_fun hPJ.eq x, hPker, ?_⟩
  have hCG : Commute C.toLinearMap G.toLinearMap := by
    change C.toLinearMap * G.toLinearMap = G.toLinearMap * C.toLinearMap
    exact congrArg ContinuousLinearMap.toLinearMap (hGA C hZC).eq.symm
  obtain ⟨e, c, g, hCe, hGe⟩ := hC.isSymmetric.exists_joint_orthonormalBasis_real
    hG.isSymmetric hCG
  change ∀ i, C (e i) = (c i : ℂ) • e i at hCe
  change ∀ i, G (e i) = (g i : ℂ) • e i at hGe
  have hc (i) : 0 ≤ c i := by
    have hn : 0 ≤ (inner ℂ (e i) (C (e i))).re := hCpos.re_inner_nonneg_right (e i)
    simpa only [hCe, inner_smul_right, e.inner_eq_one, mul_one, Complex.ofReal_re] using hn
  have hc1 (i) : c i ≤ 1 := by
    have hsum := DFunLike.congr_fun
      (nonacuteDirectRotation_add_star_eq_two_cosine K L (finiteCrossedDefectEquiv K L hKL))
      (e i)
    change R (e i) + star (R : E →L[ℂ] E) (e i) = C (e i) + C (e i) at hsum
    rw [hCe, show star (R : E →L[ℂ] E) = (R.symm : E →L[ℂ] E) from R.adjoint_eq_symm]
      at hsum
    change R (e i) + R.symm (e i) = (c i : ℂ) • e i + (c i : ℂ) • e i at hsum
    have hn := norm_add_le (R (e i)) (R.symm (e i))
    rw [hsum, ← add_smul] at hn
    have hn' : c i + c i ≤ 1 + 1 := by
      simpa [norm_smul, ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (add_nonneg (hc i) (hc i)), e.norm_eq_one] using hn
    linarith
  have hHe (i) : H (e i) = ((c i * g i : ℝ) : ℂ) • e i := by
    rw [hHG]
    change C (G (e i)) = _
    rw [hGe, map_smul, hCe, smul_smul, Complex.ofReal_mul]
    congr 1
    ring
  apply ContinuousLinearMap.coe_injective
  apply e.toBasis.ext
  intro i
  let beta := min 1 (a * c i / b)
  let s := Real.sqrt (1 - beta ^ 2)
  have hUe : U (e i) = ((beta : ℂ) + (s : ℂ) * Complex.I) • e i := by
    rw [show U = cfc (weightedPhaseSymbol a b) C from rfl,
      ContinuousLinearMap.cfc_apply_of_apply_eq_smul_of_isStarNormal _ (hCe i),
      weightedPhaseSymbol_eq_clip a b (c i) hb (hb.le.trans hab.le) ⟨hc i, hc1 i⟩]
  have hUs : star U (e i) = ((beta : ℂ) - (s : ℂ) * Complex.I) • e i := by
    have h := unitary_star_apply_of_apply_eq_smul
      (⟨U, weightedPhaseFactor_mem_unitary a b C inferInstance⟩ : unitary (E →L[ℂ] E))
      _ (by
        have hn := norm_circlePhase 1 (optimalWeightedPhase a b (Real.arccos (c i))) zero_le_one
        change ‖weightedPhaseSymbol a b (c i : ℂ)‖ = 1 at hn
        rwa [weightedPhaseSymbol_eq_clip a b (c i) hb (hb.le.trans hab.le) ⟨hc i, hc1 i⟩] at hn)
      (e i) hUe
    simpa [RCLike.star_def, Complex.conj_ofReal, Complex.conj_I, sub_eq_add_neg] using h
  change C (Z (e i)) = C (U (P (e i)) + star U (e i - P (e i)))
  by_cases hz : c i = 0
  · have hzero : C (e i) = 0 := by rw [hCe, hz, Complex.ofReal_zero, zero_smul]
    have hPzero : P (e i) = 0 := hPker _ hzero
    have hCZ : C (Z (e i)) = Z (C (e i)) := (DFunLike.congr_fun hZC.eq (e i)).symm
    rw [hCZ, hzero, map_zero, hPzero, map_zero, sub_zero, zero_add, hUs, map_smul,
      hzero, smul_zero]
  · have hcpos : 0 < c i := lt_of_le_of_ne (hc i) (Ne.symm hz)
    have hreal := minimizing_weighted_transport_relative_real_part_complex
      a b hb hab K L hKL T hT hatt (c i) hcpos (e i) (hCe i)
    have hre : (ℜ Z : E →L[ℂ] E) (e i) = (beta : ℂ) • e i := by
      rw [realPart_apply_coe]
      change (2 : ℝ)⁻¹ • (Z (e i) + star Z (e i)) = _
      rw [hreal]
      simp [beta, ← Complex.coe_smul, smul_smul]
    have hZe : Z (e i) = ((beta : ℂ) + (g i : ℂ) * Complex.I) • e i := by
      have h := DFunLike.congr_fun (realPart_add_I_smul_imaginaryPart Z) (e i)
      change (ℜ Z : E →L[ℂ] E) (e i) + Complex.I • G (e i) = Z (e i) at h
      rw [hre, hGe] at h
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
    have hsign : 0 < c i * g i ↔ 0 < g i := mul_pos_iff_of_pos_left hcpos
    have hPe : P (e i) = (if 0 < g i then (1 : ℂ) else 0) • e i := by
      have h := ContinuousLinearMap.cfc_apply_of_apply_eq_smul
        ((Set.Ioi 0).indicator (1 : ℝ → ℝ)) (hHe i) hH
      change P (e i) = (((Set.Ioi 0).indicator (1 : ℝ → ℝ) (c i * g i) : ℝ) : ℂ) • e i
        at h
      by_cases hg : 0 < g i
      · simpa [Set.indicator_apply, hsign, hg] using h
      · simpa [Set.indicator_apply, hsign, hg] using h
    have hvec : Z (e i) = U (P (e i)) + star U (e i - P (e i)) := by
      by_cases hg : 0 < g i
      · have hs' : s = g i := hs.trans (abs_of_pos hg)
        rw [hPe, ite_eq_left hg, one_smul, sub_self, map_zero, add_zero, hUe, hZe, hs']
      · have hs' : s = -g i := hs.trans (abs_of_nonpos (le_of_not_gt hg))
        rw [hPe, ite_eq_right hg, zero_smul, map_zero, sub_zero, zero_add, hUs, hZe, hs']
        simp only [Complex.ofReal_neg, neg_mul, sub_neg_eq_add]
    exact congrArg C hvec

/-- Complete weighted optimizer criterion for every finite complex pair.
The phase projection is supported away from the right-angle kernel; the
transporter's self-adjoint kernel action is independent of that phase.
All conditions concern the actual ambient transporter. -/
theorem minimizing_weighted_transport_iff_phase_and_kernel_complex
    (a b : ℝ) (hb : 0 < b) (hab : b < a)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L)
    (T : E ≃ₗᵢ[ℂ] E) (hT : K.map T.toLinearMap = L) :
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
        nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
          unitary (E →L[ℂ] E))
    let C := Proposition35.section3CosAngleOperator K L
    let U := weightedPhaseFactor a b C
    UnitarilyInvariantSeminorm.nuclear ℂ E E
        ((a : ℂ) • T.toLinearMap - (b : ℂ) • LinearMap.id) =
          weightedRotationMinimum a b C ↔
      (∀ x, C x = 0 → T x = star (T : E →L[ℂ] E) x) ∧
      ∃ P : E →L[ℂ] E, IsStarProjection P ∧ Commute P (R : E →L[ℂ] E) ∧
        (∀ x, P (K.reflection x) = K.reflection (P x)) ∧
        (∀ x, C x = 0 → P x = 0) ∧
        C * (R.trans T.symm : E →L[ℂ] E) = C * (U * P + star U * (1 - P)) := by
  dsimp only
  constructor
  · intro hatt
    obtain ⟨hP, hPR, hPJ, hPker, hphase⟩ :=
      minimizing_weighted_transport_positive_phase_projection_mod_kernel_complex
        a b hb hab K L hKL T hT hatt
    exact ⟨minimizing_weighted_transport_selfAdjoint_on_right_defect_complex
        a b hb hab K L hKL T hT hatt, _, hP, hPR, hPJ, hPker, hphase⟩
  · rintro ⟨hselfT, P, hP, hPR, hPJ, _, hphase⟩
    obtain ⟨S, hS, hSphase, hSatt, _⟩ :=
      exists_weighted_transport_from_projection_complex a b hb hab K L hKL P hP hPR hPJ
    have hSC := minimizing_weighted_transport_commutes_cosine_complex
      a b hb hab K L hKL S hS hSatt
    have hselfS := minimizing_weighted_transport_selfAdjoint_on_right_defect_complex
      a b hb hab K L hKL S hS hSatt
    have hrel := hphase.trans
      (congrArg (fun B => Proposition35.section3CosAngleOperator K L * B) hSphase).symm
    have hC := ((ContinuousLinearMap.nonneg_iff_isPositive).mp
      (Proposition35.section3CosAngleOperator_nonneg K L)).isSelfAdjoint
    have hTC := commute_of_relative_left_mul_eq _ hC _ T S hSC hrel
    have hagree := LinearIsometryEquiv.eq_on_orthogonal_ker_of_relative_left_mul_eq
      _ _ T S hrel
    exact (weighted_transport_cost_eq_of_eq_on_cosine_kernel_orthogonal
      a b hb.le hab.le K L T S hT hS hTC hSC hselfT hselfS hagree).trans hSatt

/-- Every global Charbonnier optimizer, and only a global optimizer, has
the phase-plus-reflecting-kernel form. No angle, multiplicity, or
projection-gap restriction is imposed. -/
theorem smoothed_transport_isMin_iff_phase_and_kernel_complex
    (tau : ℝ) (htau : 0 < tau)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L)
    (T : E ≃ₗᵢ[ℂ] E) (hT : K.map T.toLinearMap = L) :
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
        nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
          unitary (E →L[ℂ] E))
    let C := Proposition35.section3CosAngleOperator K L
    let U := weightedPhaseFactor (smoothingRadius tau) (smoothingRadius tau)⁻¹ C
    (∀ S : E ≃ₗᵢ[ℂ] E, K.map S.toLinearMap = L →
      smoothedDisplacementCost tau T.toLinearMap ≤ smoothedDisplacementCost tau S.toLinearMap) ↔
      (∀ x, C x = 0 → T x = star (T : E →L[ℂ] E) x) ∧
      ∃ P : E →L[ℂ] E, IsStarProjection P ∧ Commute P (R : E →L[ℂ] E) ∧
        (∀ x, P (K.reflection x) = K.reflection (P x)) ∧
        (∀ x, C x = 0 → P x = 0) ∧
        C * (R.trans T.symm : E →L[ℂ] E) = C * (U * P + star U * (1 - P)) := by
  let a := smoothingRadius tau
  have ha : 1 < a := one_lt_smoothingRadius tau htau
  have ha0 : 0 < a := zero_lt_one.trans ha
  have hw := minimizing_weighted_transport_iff_phase_and_kernel_complex
    a a⁻¹ (inv_pos.mpr ha0) (((inv_lt_one₀ ha0).mpr ha).trans ha) K L hKL T hT
  constructor
  · intro hmin
    exact hw.mp (smoothed_minimizer_weighted_cost_eq_complex tau htau K L hKL T hT hmin)
  · intro hclass
    have hatt := hw.mpr hclass
    obtain ⟨W, hW, _, hWmin⟩ :=
      exists_unitary_minimizing_smoothed_transport tau htau K L hKL
    have hWatt := smoothed_minimizer_weighted_cost_eq_complex tau htau K L hKL W hW hWmin
    have hTc := smoothedDisplacementCost_eq_weightedNuclear tau htau
      (Unitary.linearIsometryEquiv.symm T)
    change smoothedDisplacementCost tau T.toLinearMap =
      UnitarilyInvariantSeminorm.nuclear ℂ E E
        ((a : ℂ) • T.toLinearMap - ((a⁻¹ : ℝ) : ℂ) • LinearMap.id) -
          Module.finrank ℂ E * tau at hTc
    have hWc := smoothedDisplacementCost_eq_weightedNuclear tau htau
      (Unitary.linearIsometryEquiv.symm W)
    change smoothedDisplacementCost tau W.toLinearMap =
      UnitarilyInvariantSeminorm.nuclear ℂ E E
        ((a : ℂ) • W.toLinearMap - ((a⁻¹ : ℝ) : ℂ) • LinearMap.id) -
          Module.finrank ℂ E * tau at hWc
    have heq : smoothedDisplacementCost tau T.toLinearMap =
        smoothedDisplacementCost tau W.toLinearMap := by
      rw [hTc, hWc, hatt, hWatt]
    intro S hS
    rw [heq]
    exact hWmin S hS

/-- Complete all-angle Charbonnier classification with actual typed
crossed-defect parameters. The defect isometry is uniquely determined
by the optimizer, while inactive phase projections may be redundant. -/
theorem smoothed_transport_isMin_iff_phase_and_defect_equiv_complex
    (tau : ℝ) (htau : 0 < tau)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L)
    (T : E ≃ₗᵢ[ℂ] E) (hT : K.map T.toLinearMap = L) :
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
        nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
          unitary (E →L[ℂ] E))
    let C := Proposition35.section3CosAngleOperator K L
    let U := weightedPhaseFactor (smoothingRadius tau) (smoothingRadius tau)⁻¹ C
    (∀ S : E ≃ₗᵢ[ℂ] E, K.map S.toLinearMap = L →
      smoothedDisplacementCost tau T.toLinearMap ≤ smoothedDisplacementCost tau S.toLinearMap) ↔
      (∃! D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L,
        (∀ x : halmosSourceDefect K L, T x = (D x : E)) ∧
        (∀ y : halmosTargetDefect K L, T y = (D.symm y : E))) ∧
      ∃ P : E →L[ℂ] E, IsStarProjection P ∧ Commute P (R : E →L[ℂ] E) ∧
        (∀ x, P (K.reflection x) = K.reflection (P x)) ∧
        (∀ x, C x = 0 → P x = 0) ∧
        C * (R.trans T.symm : E →L[ℂ] E) = C * (U * P + star U * (1 - P)) := by
  have hc := smoothed_transport_isMin_iff_phase_and_kernel_complex tau htau K L hKL T hT
  dsimp only at hc ⊢
  constructor
  · intro hmin
    obtain ⟨hself, hphase⟩ := hc.mp hmin
    exact ⟨Proposition35.exists_unique_defect_equiv_of_selfAdjoint_on_cosine_kernel
      K L T hT hself, hphase⟩
  · rintro ⟨⟨D, ⟨hsrc, htgt⟩, _⟩, hphase⟩
    exact hc.mpr ⟨
      Proposition35.selfAdjoint_on_cosine_kernel_of_defect_equiv K L T D hsrc htgt, hphase⟩

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

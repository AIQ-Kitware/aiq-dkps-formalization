/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SchattenNonacuteCommutation
public import DavisKahan.FiniteDimensional.DirectRotation.SchattenPhaseDefectAttainment
public import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Projection
public import ForTauCeti.Analysis.InnerProductSpace.JointEigenbasis
public import Mathlib.LinearAlgebra.Complex.Module

/-!
# Intrinsic phase projection of every nonacute Schatten optimizer

The positive spectral projection of the imaginary part of the
cosine-weighted relative unitary supplies a compatible phase parameter.
The cosine annihilates the right-angle sector. Fixed and critical
directions are retained, including at vanishing phase sine.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open Set
open scoped ENNReal ComplexStarModule InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

attribute [local instance 100] ContinuousLinearMap.realAlgebra
  ContinuousLinearMap.realIsScalarTower ContinuousLinearMap.continuousFunctionalCalculusReal
attribute [local instance] ContinuousLinearMap.instStarOrderedRingRCLike

omit [FiniteDimensional ℂ E] in
private theorem commute_star_of_commute_unitary_right
    (A : E →L[ℂ] E) (V : E ≃ₗᵢ[ℂ] E) (hAV : Commute A (V : E →L[ℂ] E)) :
    Commute (star A) (V : E →L[ℂ] E) := by
  have hinv : Commute (V.symm : E →L[ℂ] E) A := by
    ext x
    change V.symm (A x) = A (V.symm x)
    apply V.injective
    rw [V.apply_symm_apply]
    have h := congrArg (fun B : E →L[ℂ] E => B (V.symm x)) hAV.eq
    change A (V (V.symm x)) = V (A (V.symm x)) at h
    rwa [V.apply_symm_apply] at h
  rw [← V.adjoint_eq_symm] at hinv
  change Commute (star (V : E →L[ℂ] E)) A at hinv
  rw [commute_iff_eq]
  simpa only [star_mul, star_star] using congrArg star hinv.eq

set_option maxHeartbeats 1200000 in
/-- Every ambient local minimum has an intrinsic compatible phase
projection modulo the right-angle cosine kernel. The projection is the
positive spectral projection of the actual weighted relative imaginary
part; no angle or multiplicity hypothesis is supplied. -/
theorem schatten_minimizer_positive_phase_projection_mod_kernel_complex
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
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
        nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
          unitary (E →L[ℂ] E))
    let C := Proposition35.section3CosAngleOperator K L
    let Z := star (R : E →L[ℂ] E) * (U : E →L[ℂ] E)
    let F := schattenPhaseFactor p.toReal C
    let P := cfc ((Ioi 0).indicator (1 : ℝ → ℝ)) (ℑ (C * Z) : E →L[ℂ] E)
    IsStarProjection P ∧ Commute P (R : E →L[ℂ] E) ∧
      (∀ x, P (K.reflection x) = K.reflection (P x)) ∧
      C * Z = C * (F * P + star F * (1 - P)) := by
  classical
  let D := finiteCrossedDefectEquiv K L hKL
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L D, nonacuteDirectRotation_mem_unitary K L D⟩ :
      unitary (E →L[ℂ] E))
  let C := Proposition35.section3CosAngleOperator K L
  let Z' := (Unitary.linearIsometryEquiv U).trans R.symm
  let Z : E →L[ℂ] E := Z'
  let A := C * Z
  let G : E →L[ℂ] E := ℑ A
  let P := cfc ((Ioi 0).indicator (1 : ℝ → ℝ)) G
  let F := schattenPhaseFactor p.toReal C
  have hCpos := ContinuousLinearMap.nonneg_iff_isPositive.mp
    (Proposition35.section3CosAngleOperator_nonneg K L)
  have hC : IsSelfAdjoint C := hCpos.isSelfAdjoint
  have hG : IsSelfAdjoint G := (ℑ A).property
  let : IsStarNormal C := hC.isStarNormal
  have hZC : Commute Z C :=
    Proposition35.commute_section3CosAngleOperator_of_commute_sinAngleOperator K L Z
      (relative_phase_commute_sinAngleOperator_of_isLocalMinOn_complex
        p hp hp1 hp2 K L U hmap hmin D)
  have hRmap : K.map R.toLinearMap = L := by
    apply (Submodule.map_eq_iff_intertwines_reflection K L R).mpr
    exact nonacuteDirectRotation_reflection_intertwines K L D
  have hZJ : Commute Z (K.reflection : E →L[ℂ] E) := by
    ext x
    exact Submodule.relative_transport_commutes_reflection K L
      (Unitary.linearIsometryEquiv U) R hmap hRmap x
  have hCJ : Commute C (K.reflection : E →L[ℂ] E) :=
    (K.commute_reflection_iff.mpr
      (Proposition35.section3CosAngleOperator_comm_projection K L).symm).symm
  have hAR : Commute A (R : E →L[ℂ] E) :=
    cosine_mul_relative_phase_commutes_canonical_of_isLocalMinOn_complex
      p hp hp1 hp2 K L hKL U hmap hmin
  have hAJ : Commute A (K.reflection : E →L[ℂ] E) := hCJ.mul_left hZJ
  have hAC : Commute A C := (Commute.refl C).mul_left hZC
  have hAsC : Commute (star A) C := by
    rw [commute_iff_eq]
    simpa only [star_mul, hC.star_eq] using (congrArg star hAC.eq).symm
  have hGC (B : E →L[ℂ] E) (hAB : Commute A B) (hAsB : Commute (star A) B) :
      Commute G B := by
    dsimp only [G]
    rw [imaginaryPart_apply_coe]
    exact ((hAB.sub_left hAsB).smul_left ((2 : ℝ)⁻¹)).smul_left (-Complex.I)
  have hPR : Commute P (R : E →L[ℂ] E) :=
    (hGC _ hAR (commute_star_of_commute_unitary_right A R hAR)).cfc_real _
  have hPJ : Commute P (K.reflection : E →L[ℂ] E) :=
    (hGC _ hAJ (commute_star_of_commute_unitary_right A K.reflection hAJ)).cfc_real _
  refine ⟨TauCeti.isStarProjection_cfc_indicator G (Ioi 0), hPR,
    fun x => congrArg (fun B : E →L[ℂ] E => B x) hPJ.eq, ?_⟩
  have hCG : Commute C.toLinearMap G.toLinearMap :=
    congrArg ContinuousLinearMap.toLinearMap (hGC C hAC hAsC).eq.symm
  obtain ⟨e, c, g, hCe, hGe⟩ := hC.isSymmetric.exists_joint_orthonormalBasis_real
    hG.isSymmetric hCG
  change ∀ i, C (e i) = (c i : ℂ) • e i at hCe
  change ∀ i, G (e i) = (g i : ℂ) • e i at hGe
  have hc0 (i) : 0 ≤ c i := by
    have h : 0 ≤ (inner ℂ (e i) (C (e i))).re := hCpos.re_inner_nonneg_right (e i)
    simpa only [hCe, inner_smul_right, e.inner_eq_one, mul_one, Complex.ofReal_re] using h
  have hc1 (i) : c i ≤ 1 := by
    have hsum := congrArg (fun B : E →L[ℂ] E => B (e i))
      (nonacuteDirectRotation_add_star_eq_two_cosine K L D)
    change R (e i) + star (R : E →L[ℂ] E) (e i) = C (e i) + C (e i) at hsum
    rw [hCe, show star (R : E →L[ℂ] E) = (R.symm : E →L[ℂ] E)
      from R.adjoint_eq_symm] at hsum
    change R (e i) + R.symm (e i) = (c i : ℂ) • e i + (c i : ℂ) • e i at hsum
    have h := norm_add_le (R (e i)) (R.symm (e i))
    rw [hsum, ← add_smul] at h
    have h' : c i + c i ≤ 1 + 1 := by
      simpa only [norm_smul, ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (add_nonneg (hc0 i) (hc0 i)), e.norm_eq_one, mul_one,
        R.norm_map, R.symm.norm_map] using h
    linarith
  apply ContinuousLinearMap.coe_injective
  apply e.toBasis.ext
  intro i
  let theta := Real.arccos (c i)
  let delta := optimalPhase p.toReal theta
  let beta := Real.cos delta
  let s := Real.sin delta
  have hθ : theta ∈ Icc 0 (Real.pi / 2) :=
    ⟨Real.arccos_nonneg _, Real.arccos_le_pi_div_two.mpr (hc0 i)⟩
  have hcos : Real.cos theta = c i := Real.cos_arccos (by linarith [hc0 i]) (hc1 i)
  have hCc : C (e i) = (Real.cos theta : ℂ) • e i := by rw [hcos]; exact hCe i
  have hFe : F (e i) = ((beta : ℂ) + (s : ℂ) * Complex.I) • e i := by
    rw [show F = schattenPhaseFactor p.toReal C from rfl,
      schattenPhaseFactor_apply_cos p.toReal theta C _
        ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩ hCc, Complex.exp_ofReal_mul_I]
  have hFse : star F (e i) = ((beta : ℂ) - (s : ℂ) * Complex.I) • e i := by
    rw [show F = schattenPhaseFactor p.toReal C from rfl,
      schattenPhaseFactor_star_apply_cos p.toReal theta C _
        ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩ hCc, Complex.exp_ofReal_mul_I]
    simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg, neg_mul, sub_eq_add_neg,
      beta, s, delta]
  have hPe : P (e i) = (if 0 < g i then (1 : ℂ) else 0) • e i := by
    have h := ContinuousLinearMap.cfc_apply_of_apply_eq_smul
      ((Ioi 0).indicator (1 : ℝ → ℝ)) (hGe i) hG
    simpa [P, Set.indicator_apply, Set.mem_Ioi] using h
  have hAZ : A (e i) = (c i : ℂ) • Z (e i) := by
    change C (Z (e i)) = _
    rw [← show Z (C (e i)) = C (Z (e i)) from
      congrArg (fun B : E →L[ℂ] E => B (e i)) hZC.eq, hCe, map_smul]
  change C (Z (e i)) = C (F (P (e i)) + star F (e i - P (e i)))
  by_cases hz : c i = 0
  · have hCzero : C (e i) = 0 := by rw [hCe, hz, Complex.ofReal_zero, zero_smul]
    have hAzeros : C (Z (e i)) = 0 := by
      change A (e i) = 0
      rw [hAZ, hz, Complex.ofReal_zero, zero_smul]
    rw [hAzeros]
    by_cases hg : 0 < g i
    · rw [hPe, ite_eq_left hg, one_smul, sub_self, map_zero, add_zero, hFe,
        map_smul, hCzero, smul_zero]
    · rw [hPe, ite_eq_right hg, zero_smul, map_zero, sub_zero, zero_add, hFse,
        map_smul, hCzero, smul_zero]
  have hcpos : 0 < c i := lt_of_le_of_ne (hc0 i) (Ne.symm hz)
  have hreal : Z (e i) + star Z (e i) = (2 * (beta : ℂ)) • e i := by
    by_cases hθzero : theta = 0
    · have hS := Proposition35.sine_apply_of_cosine_apply K L (e i) theta hθ hCc
      have hSzero : K.sinAngleOperator L (e i) = 0 := by
        simpa only [hθzero, Real.sin_zero, RCLike.ofReal_zero, Complex.ofReal_zero, zero_smul] using hS
      have hPQ : K.starProjection (e i) = L.starProjection (e i) := by
        have h := K.norm_sinAngleOperator_apply L (e i)
        rw [hSzero, norm_zero] at h
        exact sub_eq_zero.mp (norm_eq_zero.mp h.symm)
      have hUfix := apply_eq_self_of_projections_eq_of_isLocalMinOn_transports_complex
        p hp hp1 hp2 K L U hmap hmin _ hPQ
      have hRfix : R (e i) = e i :=
        nonacuteDirectRotation_apply_eq_self_of_projections_eq K L D _ hPQ
      have hRcoe : (Unitary.linearIsometryEquiv.symm R : E →L[ℂ] E) =
          (R : E →L[ℂ] E) := Unitary.coe_symm_linearIsometryEquiv_apply R
      have hRstar := unitary_star_apply_of_apply_eq_smul
        (Unitary.linearIsometryEquiv.symm R) (1 : ℂ) (by simp) (e i)
        (by rw [hRcoe]; change R (e i) = (1 : ℂ) • e i; simpa only [one_smul] using hRfix)
      rw [hRcoe] at hRstar
      have hZfix : Z (e i) = e i := by
        change star (R : E →L[ℂ] E) ((U : E →L[ℂ] E) (e i)) = _
        rw [hUfix]
        simpa only [star_one, one_smul] using hRstar
      have hZcoe : (Unitary.linearIsometryEquiv.symm Z' : E →L[ℂ] E) = Z :=
        Unitary.coe_symm_linearIsometryEquiv_apply Z'
      have hZstar := unitary_star_apply_of_apply_eq_smul
        (Unitary.linearIsometryEquiv.symm Z') (1 : ℂ) (by simp) (e i)
        (by rw [hZcoe]; simpa only [one_smul] using hZfix)
      rw [hZcoe] at hZstar
      have hZstarfix : star Z (e i) = e i := by simpa only [star_one, one_smul] using hZstar
      rw [hZfix, hZstarfix]
      have hδzero : delta = 0 := by dsimp only [delta]; rw [hθzero, optimalPhase_zero _ hp1.le]
      simp only [beta, hδzero, Real.cos_zero, Complex.ofReal_one, mul_one, two_smul]
    · have hθpos : 0 < theta := lt_of_le_of_ne hθ.1 (Ne.symm hθzero)
      have hθlt : theta < Real.pi / 2 := Real.arccos_lt_pi_div_two.mpr hcpos
      exact relative_phase_add_star_on_angle_of_isLocalMinOn_complex
        p hp hp1 hp2 K L U hmap hmin D theta ⟨hθpos, hθlt⟩ (e i)
        (Proposition35.sine_apply_of_cosine_apply K L (e i) theta hθ hCc)
  have hAs : star A (e i) = (c i : ℂ) • star Z (e i) := by
    change (star (C * Z)) (e i) = _
    rw [star_mul, hC.star_eq]
    change star Z (C (e i)) = _
    rw [hCe, map_smul]
  have hrealA : A (e i) + star A (e i) = (2 * ((c i * beta : ℝ) : ℂ)) • e i := by
    rw [hAZ, hAs, ← smul_add, hreal, smul_smul]
    congr 1
    push_cast
    ring
  have hReA : (ℜ A : E →L[ℂ] E) (e i) = ((c i * beta : ℝ) : ℂ) • e i := by
    rw [realPart_apply_coe]
    change (2 : ℝ)⁻¹ • (A (e i) + star A (e i)) = _
    rw [hrealA]
    simp only [← Complex.coe_smul, smul_smul]
    congr 1
    push_cast
    ring
  have hAe : A (e i) = (((c i * beta : ℝ) : ℂ) + (g i : ℂ) * Complex.I) • e i := by
    have h := congrArg (fun B : E →L[ℂ] E => B (e i)) (realPart_add_I_smul_imaginaryPart A)
    change (ℜ A : E →L[ℂ] E) (e i) + Complex.I • G (e i) = A (e i) at h
    rw [hReA, hGe] at h
    rw [← h]
    module
  let gamma := g i / c i
  have hZe : Z (e i) = ((beta : ℂ) + (gamma : ℂ) * Complex.I) • e i := by
    apply smul_right_injective E (Complex.ofReal_ne_zero.mpr hcpos.ne')
    change (c i : ℂ) • Z (e i) = (c i : ℂ) •
      (((beta : ℂ) + (gamma : ℂ) * Complex.I) • e i)
    rw [← hAZ, hAe, smul_smul]
    congr 1
    dsimp only [gamma]
    push_cast
    have hcne : (c i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcpos.ne'
    field_simp [hcne]
  have hnorm : ‖(beta : ℂ) + (gamma : ℂ) * Complex.I‖ = 1 := by
    have h := Z'.norm_map (e i)
    change ‖Z (e i)‖ = ‖e i‖ at h
    simpa only [hZe, norm_smul, e.norm_eq_one, mul_one] using h
  have hsnon : 0 ≤ s := by
    have hm := (optimalPhase_spec p.toReal theta hp1.le hθ.1).1
    exact Real.sin_nonneg_of_nonneg_of_le_pi hm.1 (by linarith [hm.2, hθ.2, Real.pi_pos])
  have hs : s = |gamma| := by
    have h := Complex.normSq_eq_norm_sq ((beta : ℂ) + (gamma : ℂ) * Complex.I)
    simp only [Complex.normSq_apply, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_self,
      add_zero, Complex.add_im, Complex.mul_im, mul_one, zero_add, hnorm, one_pow] at h
    apply (sq_eq_sq₀ hsnon (abs_nonneg gamma)).mp
    rw [sq_abs]
    nlinarith [Real.sin_sq_add_cos_sq delta]
  congr 1
  by_cases hg : 0 < g i
  · have hgamma : 0 < gamma := div_pos hg hcpos
    have hs' : s = gamma := hs.trans (abs_of_pos hgamma)
    rw [hPe, ite_eq_left hg, one_smul, sub_self, map_zero, add_zero, hFe, hZe, hs']
  · have hgamma : gamma ≤ 0 := div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hg) hcpos.le
    have hs' : s = -gamma := hs.trans (abs_of_nonpos hgamma)
    rw [hPe, ite_eq_right hg, zero_smul, map_zero, sub_zero, zero_add, hFse, hZe, hs']
    simp only [Complex.ofReal_neg, neg_mul, sub_neg_eq_add]

/-- Complete unrestricted finite complex Schatten optimizer
classification: a feasible unitary is globally minimizing exactly when
it has compatible phase-projection and arbitrary reflecting defect data.
Every angle, multiplicity and ambient unitary competitor is included. -/
theorem schatten_transport_isMin_iff_phase_and_defect_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L)
    (T : E ≃ₗᵢ[ℂ] E) (hT : K.map T.toLinearMap = L) :
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
        nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
          unitary (E →L[ℂ] E))
    let C := Proposition35.section3CosAngleOperator K L
    let F := schattenPhaseFactor p.toReal C
    (∀ V : E ≃ₗᵢ[ℂ] E, K.map V.toLinearMap = L →
      UnitarilyInvariantSeminorm.schatten ℂ E E p
          (LinearMap.id - T.toLinearMap) ^ p.toReal ≤
        UnitarilyInvariantSeminorm.schatten ℂ E E p
          (LinearMap.id - V.toLinearMap) ^ p.toReal) ↔
      ∃ P : E →L[ℂ] E, IsStarProjection P ∧ Commute P (R : E →L[ℂ] E) ∧
        (∀ x, P (K.reflection x) = K.reflection (P x)) ∧
        ∃ D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L,
          (∀ x : halmosSourceDefect K L, T x = (D x : E)) ∧
          (∀ y : halmosTargetDefect K L, T y = (D.symm y : E)) ∧
          C * (T.trans R.symm : E →L[ℂ] E) = C * (F * P + star F * (1 - P)) := by
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
      nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
        unitary (E →L[ℂ] E))
  let C := Proposition35.section3CosAngleOperator K L
  let F := schattenPhaseFactor p.toReal C
  constructor
  · intro hmin
    let U := Unitary.linearIsometryEquiv.symm T
    have hUmap : K.map (Unitary.linearIsometryEquiv U).toLinearMap = L := by
      simpa only [U, MulEquiv.apply_symm_apply] using hT
    have hTmin : IsMinOn
        (fun V : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
          (LinearMap.id - V.toLinearMap) ^ p.toReal)
        {V | V ∈ unitary (E →L[ℂ] E) ∧ V * K.starProjection * star V = L.starProjection}
        (T : E →L[ℂ] E) := by
      intro V hV
      let V' : unitary (E →L[ℂ] E) := ⟨V, hV.1⟩
      have hh := hmin (Unitary.linearIsometryEquiv V')
        ((map_eq_iff_conjugate_starProjection_complex K L V').mpr hV.2)
      have hcoe : (Unitary.linearIsometryEquiv V').toLinearMap = V.toLinearMap := rfl
      rw [hcoe] at hh
      exact hh
    have hdata := schatten_minimizer_positive_phase_projection_mod_kernel_complex
      p hp hp1 hp2 K L hKL U hUmap hTmin.isLocalMinOn
    obtain ⟨D, ⟨hsrc, htgt⟩, _⟩ := exists_unique_defect_equiv_of_isLocalMinOn_transports_complex
      p hp hp1 hp2 K L U hUmap hTmin.isLocalMinOn
    refine ⟨_, hdata.1, hdata.2.1, hdata.2.2.1, D, ?_, ?_, ?_⟩
    · exact hsrc
    · exact htgt
    · exact hdata.2.2.2
  · rintro ⟨P, hP, hPR, hPJ, D, hsrc, htgt, hphase⟩
    obtain ⟨S, ⟨hS, hSsrc, hStgt, hSphase, _, hSmin⟩, _⟩ :=
      exists_unique_schatten_transport_from_phase_and_defect_complex
        p hp hp1 hp2 K L hKL P hP hPR hPJ D
    have hRC : Commute (R : E →L[ℂ] E) C := by
      change Commute (nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL))
        (Proposition35.section3CosAngleOperator K L)
      rw [Proposition35.section3CosAngleOperator_eq_canonicalAbsoluteValue]
      exact nonacuteDirectRotation_comm_absoluteValue K L _
    have heq : T = S := transport_eq_of_right_phase_and_defect_actions_complex
      K L R T S hRC D hsrc htgt hSsrc hStgt (hphase.trans hSphase.symm)
    subst T
    intro V hV
    let V' := Unitary.linearIsometryEquiv.symm V
    have hV'map : K.map (Unitary.linearIsometryEquiv V').toLinearMap = L := by
      simpa only [V', MulEquiv.apply_symm_apply] using hV
    have hh := hSmin ⟨V'.property, (map_eq_iff_conjugate_starProjection_complex K L V').mp hV'map⟩
    change UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - S.toLinearMap) ^ p.toReal ≤
      UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - (V' : E →L[ℂ] E).toLinearMap) ^ p.toReal at hh
    have hcoe : (V' : E →L[ℂ] E).toLinearMap = V.toLinearMap := rfl
    rwa [hcoe] at hh

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

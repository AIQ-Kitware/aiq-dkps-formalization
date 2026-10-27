/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SchattenNonacuteClassification
public import ForTauCeti.Analysis.InnerProductSpace.Projection.KernelSupport

/-!
# Nonredundant phase and defect parameters

The phase weight is `C * (F - F*)`. Its kernel consists of the directions
on which changing the phase projection cannot change the weighted formula.
Requiring the range of that projection to lie in the orthogonal complement
of this kernel removes precisely this redundancy. Every global optimizer
has exactly one resulting phase/defect pair.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- The coefficient that measures dependence on the phase projection. -/
def schattenPhaseWeight (p : ℝ) (C : E →L[ℂ] E) : E →L[ℂ] E :=
  C * (schattenPhaseFactor p C - star (schattenPhaseFactor p C))

omit [FiniteDimensional ℂ E] in
/-- Every operator commuting with the self-adjoint cosine commutes with
the phase weight. -/
theorem schattenPhaseWeight_commute
    (p : ℝ) (C B : E →L[ℂ] E) (hC : IsSelfAdjoint C) (hCB : Commute C B) :
    Commute (schattenPhaseWeight p C) B := by
  have hF := hC.commute_cfc hCB (schattenPhaseSymbol p)
  have hFs := hC.commute_cfc hCB (fun z => star (schattenPhaseSymbol p z))
  rw [cfc_star] at hFs
  exact hCB.mul_left (hF.sub_left hFs)

omit [FiniteDimensional ℂ E] in
/-- The effective phase weight of a self-adjoint cosine is skew-adjoint. -/
theorem star_schattenPhaseWeight (p : ℝ) (C : E →L[ℂ] E) (hC : IsSelfAdjoint C) :
    star (schattenPhaseWeight p C) = -schattenPhaseWeight p C := by
  have hF := hC.commute_cfc (Commute.refl C) (schattenPhaseSymbol p)
  have hFs := hC.commute_cfc (Commute.refl C) (fun z => star (schattenPhaseSymbol p z))
  rw [cfc_star] at hFs
  change Commute (schattenPhaseFactor p C) C at hF
  change Commute (star (schattenPhaseFactor p C)) C at hFs
  rw [schattenPhaseWeight, star_mul, star_sub, star_star, hC.star_eq]
  change (star (schattenPhaseFactor p C) - schattenPhaseFactor p C) * C = _
  rw [(hFs.sub_left hF).eq]
  noncomm_ring

/-- On a physical angle space the effective coefficient is
`2*i*cos(theta)*sin(optimalPhase(p,theta))`. -/
theorem schattenPhaseWeight_apply_cos
    (p theta : ℝ) (C : E →L[ℂ] E) [IsStarNormal C] (x : E)
    (hθ : theta ∈ Set.Icc 0 Real.pi)
    (hx : C x = (Real.cos theta : ℂ) • x) :
    schattenPhaseWeight p C x =
      (((2 * Real.cos theta * Real.sin (optimalPhase p theta) : ℝ) : ℂ) * Complex.I) • x := by
  change C (schattenPhaseFactor p C x - star (schattenPhaseFactor p C) x) = _
  rw [schattenPhaseFactor_apply_cos p theta C x hθ hx,
    schattenPhaseFactor_star_apply_cos p theta C x hθ hx,
    Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg, neg_mul,
    ← sub_smul, map_smul, hx, smul_smul]
  congr 1
  push_cast
  ring

/-- The phase weight vanishes on fixed directions. -/
theorem schattenPhaseWeight_apply_one
    (p : ℝ) (hp : 1 ≤ p) (C : E →L[ℂ] E) [IsStarNormal C]
    (x : E) (hx : C x = x) : schattenPhaseWeight p C x = 0 := by
  have h := schattenPhaseWeight_apply_cos p 0 C x
    ⟨le_rfl, Real.pi_pos.le⟩ (by simpa only [Real.cos_zero, Complex.ofReal_one, one_smul] using hx)
  simpa only [optimalPhase_zero p hp, Real.sin_zero, mul_zero, Complex.ofReal_zero,
    zero_mul, zero_smul]
    using h

/-- The phase weight vanishes on right-angle directions, regardless of
the scalar exponent. Their optimizer freedom is the independent defect map. -/
theorem schattenPhaseWeight_apply_zero
    (p : ℝ) (C : E →L[ℂ] E) [IsStarNormal C]
    (x : E) (hx : C x = 0) : schattenPhaseWeight p C x = 0 := by
  have h := schattenPhaseWeight_apply_cos p (Real.pi / 2) C x
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    (by simpa only [Real.cos_pi_div_two, Complex.ofReal_zero, zero_smul] using hx)
  simpa only [Real.cos_pi_div_two, mul_zero, zero_mul, Complex.ofReal_zero, zero_smul] using h

/-- An interior physical angle is ineffective exactly below and at the
canonical cutoff. Nonzero vectors are required to detect that coefficient. -/
theorem schattenPhaseWeight_apply_eq_zero_iff_le_critical
    (p theta : ℝ) (hp1 : 1 < p) (hp2 : p < 2)
    (C : E →L[ℂ] E) [IsStarNormal C] (x : E) (hne : x ≠ 0)
    (hθ : theta ∈ Set.Ioo 0 (Real.pi / 2))
    (hx : C x = (Real.cos theta : ℂ) • x) :
    schattenPhaseWeight p C x = 0 ↔ theta ≤ criticalAngle p := by
  have hcos : 0 < Real.cos theta :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hδ := (optimalPhase_spec p theta hp1.le hθ.1.le).1
  have hsin : Real.sin (optimalPhase p theta) = 0 ↔ optimalPhase p theta = 0 :=
    Real.sin_eq_zero_iff_of_lt_of_lt (by linarith [hδ.1, Real.pi_pos])
      (by linarith [hδ.2, hθ.2, Real.pi_pos])
  rw [schattenPhaseWeight_apply_cos p theta C x
    ⟨hθ.1.le, by linarith [hθ.2, Real.pi_pos]⟩ hx, smul_eq_zero_iff_left hne]
  have hcoeff :
      (((2 * Real.cos theta * Real.sin (optimalPhase p theta) : ℝ) : ℂ) * Complex.I) = 0 ↔
        Real.sin (optimalPhase p theta) = 0 := by
    rw [mul_eq_zero, or_iff_left Complex.I_ne_zero, Complex.ofReal_eq_zero,
      mul_eq_zero, or_iff_right (mul_ne_zero (by norm_num) hcos.ne')]
  rw [hcoeff, hsin, optimalPhase_eq_zero_iff_le_criticalAngle p theta hp1 hp2 hθ.1 hθ.2]

/-- Compatible phase projections with all ineffective directions removed.
The range condition is imposed on the actual phase-weight kernel. -/
@[expose]
def schattenNormalizedPhaseProjections
    (p : ℝ) (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L) :
    Set (E →L[ℂ] E) :=
  {P | IsStarProjection P ∧
    Commute P (nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL)) ∧
    (∀ x, P (K.reflection x) = K.reflection (P x)) ∧
    ∀ x, P x ∈ (schattenPhaseWeight p (Proposition35.section3CosAngleOperator K L)).kerᗮ}

omit [FiniteDimensional ℂ E] in
private theorem weighted_phase_split_eq (C F P : E →L[ℂ] E) :
    C * (F * P + star F * (1 - P)) = C * star F + (C * (F - star F)) * P := by
  noncomm_ring

/-- Every compatible phase projection has a normalized representative
with the same weighted phase formula and the same geometric compatibility. -/
theorem exists_normalized_schatten_phase_projection
    (p : ℝ) (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L)
    (P : E →L[ℂ] E) (hP : IsStarProjection P)
    (hPR : Commute P (nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL)))
    (hPJ : ∀ x, P (K.reflection x) = K.reflection (P x)) :
    let C := Proposition35.section3CosAngleOperator K L
    let F := schattenPhaseFactor p C
    ∃ Q ∈ schattenNormalizedPhaseProjections p K L hKL,
      C * (F * Q + star F * (1 - Q)) = C * (F * P + star F * (1 - P)) := by
  let C := Proposition35.section3CosAngleOperator K L
  let F := schattenPhaseFactor p C
  let W := schattenPhaseWeight p C
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
  have hAP : Commute A P :=
    ContinuousLinearMap.commute_starProjection_orthogonal_ker_of_isSelfAdjoint
      W P hP.isSelfAdjoint (schattenPhaseWeight_commute p C P hC hPC.symm).symm
  have hRC : Commute (R : E →L[ℂ] E) C :=
    Proposition35.nonacuteDirectRotation_comm_cosine K L _
  have hAR : Commute A (R : E →L[ℂ] E) :=
    ContinuousLinearMap.commute_starProjection_orthogonal_ker_of_unitary W R
      (schattenPhaseWeight_commute p C _ hC hRC.symm).symm
  have hCJ : Commute C (K.reflection : E →L[ℂ] E) :=
    (K.commute_reflection_iff.mpr
      (Proposition35.section3CosAngleOperator_comm_projection K L).symm).symm
  have hAJ : Commute A (K.reflection : E →L[ℂ] E) :=
    ContinuousLinearMap.commute_starProjection_orthogonal_ker_of_unitary W K.reflection
      (schattenPhaseWeight_commute p C _ hC hCJ).symm
  have hPJ' : Commute P (K.reflection : E →L[ℂ] E) := by
    ext x
    exact hPJ x
  refine ⟨Q, ⟨IsStarProjection.mul isStarProjection_starProjection hP hAP,
    hAR.mul_left hPR, ?_, ?_⟩, ?_⟩
  · intro x
    exact congrArg (fun B : E →L[ℂ] E => B x) (hAJ.mul_left hPJ').eq
  · intro x
    exact W.kerᗮ.starProjection_apply_mem (P x)
  · change C * (F * Q + star F * (1 - Q)) = C * (F * P + star F * (1 - P))
    rw [weighted_phase_split_eq, weighted_phase_split_eq]
    congr 1
    change W * (A * P) = W * P
    rw [← mul_assoc, ContinuousLinearMap.mul_starProjection_orthogonal_ker]

/-- Complete optimizer classification with a unique phase/defect pair.
The phase projection is normalized to the effective phase-weight space;
zero, critical and right angles need no exclusions. -/
theorem schatten_transport_isMin_iff_unique_normalized_phase_and_defect_complex
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
      ∃! data : (E →L[ℂ] E) ×
          (halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L),
        data.1 ∈ schattenNormalizedPhaseProjections p.toReal K L hKL ∧
        (∀ x : halmosSourceDefect K L, T x = (data.2 x : E)) ∧
        (∀ y : halmosTargetDefect K L, T y = (data.2.symm y : E)) ∧
        C * (T.trans R.symm : E →L[ℂ] E) =
          C * (F * data.1 + star F * (1 - data.1)) := by
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
      nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
        unitary (E →L[ℂ] E))
  let C := Proposition35.section3CosAngleOperator K L
  let F := schattenPhaseFactor p.toReal C
  constructor
  · intro hmin
    obtain ⟨P, hP, hPR, hPJ, D, hsrc, htgt, hphase⟩ :=
      (schatten_transport_isMin_iff_phase_and_defect_complex p hp hp1 hp2
        K L hKL T hT).mp hmin
    obtain ⟨Q, hQ, hQphase⟩ := exists_normalized_schatten_phase_projection
      p.toReal K L hKL P hP hPR hPJ
    refine ⟨(Q, D), ⟨hQ, hsrc, htgt, hphase.trans hQphase.symm⟩, ?_⟩
    rintro ⟨P', D'⟩ ⟨hP', hsrc', _, hphase'⟩
    have hD : D' = D := by
      ext x
      exact (hsrc' x).symm.trans (hsrc x)
    have hweight : schattenPhaseWeight p.toReal C * P' =
        schattenPhaseWeight p.toReal C * Q := by
      have h := hphase'.symm.trans (hphase.trans hQphase.symm)
      rw [weighted_phase_split_eq, weighted_phase_split_eq] at h
      exact add_left_cancel h
    have hprojection : P' = Q :=
      ContinuousLinearMap.eq_of_mul_eq_of_range_orthogonal_ker _ _ _ hweight hP'.2.2.2 hQ.2.2.2
    exact Prod.ext hprojection hD
  · rintro ⟨⟨P, D⟩, ⟨hP, hsrc, htgt, hphase⟩, _⟩
    apply (schatten_transport_isMin_iff_phase_and_defect_complex p hp hp1 hp2
      K L hKL T hT).mpr
    exact ⟨P, hP.1, hP.2.1, hP.2.2.1, D, hsrc, htgt, hphase⟩

/-- Feasible globally minimizing ambient transports for the Schatten
power. No prescribed frame or angle simplicity is part of this set. -/
def schattenTransportMinimizers
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (K L : Submodule ℂ E) : Set (E ≃ₗᵢ[ℂ] E) :=
  {T | K.map T.toLinearMap = L ∧
    ∀ V : E ≃ₗᵢ[ℂ] E, K.map V.toLinearMap = L →
      UnitarilyInvariantSeminorm.schatten ℂ E E p
          (LinearMap.id - T.toLinearMap) ^ p.toReal ≤
        UnitarilyInvariantSeminorm.schatten ℂ E E p
          (LinearMap.id - V.toLinearMap) ^ p.toReal}

omit [CompleteSpace E] in
/-- Membership in the finite optimizer set records feasibility and
comparison with every ambient unitary transporter. -/
@[simp]
theorem mem_schattenTransportMinimizers
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (K L : Submodule ℂ E) (T : E ≃ₗᵢ[ℂ] E) :
    T ∈ schattenTransportMinimizers p K L ↔
      K.map T.toLinearMap = L ∧
      ∀ V : E ≃ₗᵢ[ℂ] E, K.map V.toLinearMap = L →
        UnitarilyInvariantSeminorm.schatten ℂ E E p
            (LinearMap.id - T.toLinearMap) ^ p.toReal ≤
          UnitarilyInvariantSeminorm.schatten ℂ E E p
            (LinearMap.id - V.toLinearMap) ^ p.toReal := Iff.rfl

/-- Normalized compatible projections and independent defect unitaries
parametrize every global optimizer bijectively, with the actual actions,
weighted phase formula and uniform Lipschitz recovery of the phase
projection from the optimizer. This is an algebraic equivalence; no manifold
or topological identification of the projection space is asserted. -/
theorem exists_schatten_normalized_parameter_equiv
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L) :
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
        nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
          unitary (E →L[ℂ] E))
    let C := Proposition35.section3CosAngleOperator K L
    let F := schattenPhaseFactor p.toReal C
    ∃ e : (schattenNormalizedPhaseProjections p.toReal K L hKL ×
        (halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)) ≃
          schattenTransportMinimizers p K L,
      (∀ data, (∀ x : halmosSourceDefect K L, (e data).val x = (data.2 x : E)) ∧
        (∀ y : halmosTargetDefect K L, (e data).val y = (data.2.symm y : E)) ∧
        C * ((e data).val.trans R.symm : E →L[ℂ] E) =
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
  let F := schattenPhaseFactor p.toReal C
  let Params := schattenNormalizedPhaseProjections p.toReal K L hKL ×
    (halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
  let M := schattenTransportMinimizers p K L
  let rel (data : Params) (T : M) :=
    (∀ x : halmosSourceDefect K L, T.val x = (data.2 x : E)) ∧
      (∀ y : halmosTargetDefect K L, T.val y = (data.2.symm y : E)) ∧
      C * (T.val.trans R.symm : E →L[ℂ] E) =
        C * (F * data.1.val + star F * (1 - data.1.val))
  have hatt (data : Params) : ∃ T : M, rel data T := by
    obtain ⟨T, ⟨hT, hsrc, htgt, hphase, _, _⟩, _⟩ :=
      exists_unique_schatten_transport_from_phase_and_defect_complex p hp hp1 hp2
        K L hKL data.1.val data.1.property.1 data.1.property.2.1
        data.1.property.2.2.1 data.2
    have hmin := (schatten_transport_isMin_iff_phase_and_defect_complex p hp hp1 hp2
      K L hKL T hT).mpr
        ⟨data.1.val, data.1.property.1, data.1.property.2.1,
          data.1.property.2.2.1, data.2, hsrc, htgt, hphase⟩
    exact ⟨⟨T, hT, hmin⟩, hsrc, htgt, hphase⟩
  let f : Params → M := fun data => (hatt data).choose
  have hf (data) : rel data (f data) := (hatt data).choose_spec
  have hinj : Function.Injective f := by
    intro d e hde
    obtain ⟨data, _, huni⟩ :=
      (schatten_transport_isMin_iff_unique_normalized_phase_and_defect_complex p hp hp1 hp2
        K L hKL (f d).val (f d).property.1).mp (f d).property.2
    have hd := huni (d.1.val, d.2) ⟨d.1.property, hf d⟩
    have he := huni (e.1.val, e.2) ⟨e.1.property, by rw [hde]; exact hf e⟩
    have heq := hd.trans he.symm
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst heq
    · exact congrArg (fun z : (E →L[ℂ] E) ×
        (halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L) => z.2) heq
  have hRC : Commute (R : E →L[ℂ] E) C :=
    Proposition35.nonacuteDirectRotation_comm_cosine K L _
  have hsurj : Function.Surjective f := by
    intro T
    obtain ⟨⟨P, D⟩, ⟨hP, hsrc, htgt, hphase⟩, _⟩ :=
      (schatten_transport_isMin_iff_unique_normalized_phase_and_defect_complex p hp hp1 hp2
        K L hKL T.val T.property.1).mp T.property.2
    let data : Params := (⟨P, hP⟩, D)
    refine ⟨data, Subtype.ext ?_⟩
    exact transport_eq_of_right_phase_and_defect_actions_complex
      K L R (f data).val T.val hRC D (hf data).1 (hf data).2.1 hsrc htgt
        ((hf data).2.2.trans hphase.symm)
  refine ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, hf, ?_⟩
  obtain ⟨k, hk, hbound⟩ :=
    LinearIsometryEquiv.exists_pos_normalized_split_parameter_recovery R C F (star F)
  refine ⟨k * ‖C‖, mul_nonneg hk.le (norm_nonneg _), fun d e => ?_⟩
  exact hbound (f d).val (f e).val d.1.val e.1.val
    d.1.property.2.2.2 e.1.property.2.2.2 (hf d).2.2 (hf e).2.2

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

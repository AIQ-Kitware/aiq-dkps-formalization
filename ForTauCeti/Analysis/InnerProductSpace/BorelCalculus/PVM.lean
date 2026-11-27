/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.BorelCalculus.Multiplicative
public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Map
public import ForTauCeti.Analysis.InnerProductSpace.OperatorExt
import TauCeti.Analysis.InnerProductSpace.LinearPMap.ProjValMeasure.Basic

/-!
# Real-coordinate spectral projections

Push Tau Ceti's spectral measure of a bounded normal operator forward along a
measurable real coordinate. For a self-adjoint operator this coordinate is the
real part on its spectrum. The formulas for indicators and diagonal measures
connect the pushforward to the spectral-subspace consumers.
-/

public section

open scoped InnerProductSpace ENNReal CompactlySupported
open MeasureTheory

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace TauCeti
namespace BorelCalculus

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {a : H →L[ℂ] H}

omit [CompleteSpace H] in
/-- The indicator of a measurable set is an admissible symbol. -/
theorem isBddMeasurable_indicator {S : Set (spectrum ℂ a)} (hS : MeasurableSet S) :
    IsBddMeasurable (S.indicator (fun _ => (1 : ℂ))) := by
  refine ⟨measurable_const.indicator hS, 1, zero_le_one, fun x => ?_⟩
  by_cases hx : x ∈ S <;> simp [hx]

/-- The calculus of a measurable-set indicator is its native spectral projection. -/
theorem borelCalculus_indicator_eq_proj (ha : IsStarNormal a)
    {S : Set (spectrum ℂ a)} (hS : MeasurableSet S) :
    haveI := ha
    borelCalculus ha (isBddMeasurable_indicator hS) = a.spectralPVM.proj S hS := by
  have := ha
  rw [borelCalculus_eq_native, show (isBddMeasurable_indicator (a := a) hS).toBoundedBorelFunction =
      BoundedBorelFunction.indicator S hS 1 from
      BoundedBorelFunction.ext fun x => by
        simp only [IsBddMeasurable.toBoundedBorelFunction_apply,
          BoundedBorelFunction.indicator_apply]
        rfl]
  exact a.borelCalculus_indicator hS

section Coordinate

variable (ha : IsStarNormal a)

/-- The coordinate symbol -- the inclusion of the spectrum into `ℂ` -- is an
admissible symbol. -/
theorem isBddMeasurable_coord :
    IsBddMeasurable (fun w : spectrum ℂ a => (w : ℂ)) :=
  IsBddMeasurable.of_continuous ((ContinuousMap.id ℂ).restrict (spectrum ℂ a))

/-- **The Borel calculus of the coordinate symbol is the operator itself.**  It
extends the continuous functional calculus, where this is `cfcHom_id`. -/
theorem borelCalculus_coord :
    borelCalculus ha (isBddMeasurable_coord (a := a)) = a :=
  (borelCalculus_of_continuous ha ((ContinuousMap.id ℂ).restrict (spectrum ℂ a))
    (isBddMeasurable_coord (a := a))).trans (cfcHom_id ha)

end Coordinate

section BoundedSelfAdjoint

variable {T : H →L[ℂ] H} (hT : IsSelfAdjoint T)

/-- The real part, as a measurable relabelling of the spectrum of a bounded
self-adjoint operator.  Its spectrum is real, so this is a bijection onto the
spectrum and no Cayley detour is needed. -/
noncomputable def reCoord (w : spectrum ℂ T) : ℝ := (w : ℂ).re

omit [CompleteSpace H] in
/-- The real-part relabelling of the spectrum is measurable, which is what lets a PVM on `ℝ` be
pushed forward from one on the spectrum. -/
theorem measurable_reCoord : Measurable (reCoord (T := T)) :=
  Complex.measurable_re.comp measurable_subtypeVal

/-- **The spectral measure of a bounded self-adjoint operator**, indexed along
the real part of its spectrum. -/
noncomputable def boundedPVM : TauCeti.ProjValMeasure ℝ H :=
  letI := hT.isStarNormal
  T.spectralPVM.map reCoord measurable_reCoord

omit [CompleteSpace H] in
/-- The real-part relabelling, unfolded.  Consumers outside this module cannot reduce
`reCoord` by definition, so this is the rewrite form.  Deliberately not `@[simp]`:
several existing proofs match on `reCoord` syntactically. -/
theorem reCoord_apply (w : spectrum ℂ T) : reCoord w = (w : ℂ).re := (rfl)

omit [CompleteSpace H] in
/-- Relabelling the spectrum by real part is continuous. -/
theorem continuous_reCoord : Continuous (reCoord (T := T)) := by
  have hcoord : reCoord (T := T) = fun w : spectrum ℂ T => (w : ℂ).re :=
    funext reCoord_apply
  rw [hcoord]
  exact Complex.continuous_re.comp continuous_subtypeVal

/-- The projections of `boundedPVM` are the Borel calculus of band indicators.  Rewrite
form for consumers outside this module, where the definition bodies are not exposed. -/
theorem boundedPVM_proj (B : Set ℝ) (hB : MeasurableSet B) :
    (boundedPVM hT).proj B hB =
      borelCalculus hT.isStarNormal
        (isBddMeasurable_indicator (a := T) (measurable_reCoord hB)) := by
  have := hT.isStarNormal
  rw [boundedPVM, ProjValMeasure.map_proj, borelCalculus_indicator_eq_proj]

/-- The diagonal measures of `boundedPVM` are the pushforwards of the diagonal measures
along the real-part relabelling.  Rewrite form for consumers outside this module. -/
theorem boundedPVM_diag (ξ : H) :
    (boundedPVM hT).diag ξ = Measure.map reCoord ((cfcHom
      hT.isStarNormal).representationDiagMeasure ξ) := by
  have := hT.isStarNormal
  rw [boundedPVM, ProjValMeasure.map_diag, spectralPVM_diag_eq_representation]

/-- **The bridge to the continuous functional calculus.**  A spectral projection
of a bounded self-adjoint operator is the continuous functional calculus of any
continuous symbol agreeing with the indicator on the spectrum — which is all the
bounded-operator lane ever needs from a Borel calculus. -/
theorem boundedPVM_proj_eq_cfcHom (s : Set ℝ) (hs : MeasurableSet s)
    (g : C(spectrum ℂ T, ℂ))
    (hg : ∀ w, g w = (reCoord ⁻¹' s).indicator (fun _ => (1 : ℂ)) w) :
    (boundedPVM hT).proj s hs = cfcHom hT.isStarNormal g := by
  rw [boundedPVM_proj,
    ← borelCalculus_of_continuous hT.isStarNormal g (IsBddMeasurable.of_continuous g)]
  exact borelCalculus_congr_ae _ _ _ fun η =>
    Filter.Eventually.of_forall fun w => (hg w).symm

/-- **A spectral projection of a bounded self-adjoint operator commutes with
it** -- so its range and the orthogonal complement of its range are both
invariant, i.e. every spectral subspace reduces the operator. -/
theorem boundedPVM_proj_comm (s : Set ℝ) (hs : MeasurableSet s) :
    T * (boundedPVM hT).proj s hs = (boundedPVM hT).proj s hs * T := by
  have := hT.isStarNormal
  rw [boundedPVM, ProjValMeasure.map_proj]
  exact ((T.forall_commute_spectralPVM_proj_iff T).2 (Commute.refl T) _ _).eq

private theorem boundedPVM_eq_toPMap_top :
    boundedPVM hT = ((T : H →ₗ[ℂ] H).toPMap ⊤).spectralPVM
      (LinearPMap.isSelfAdjoint_toPMap_top hT) := by
  have := hT.isStarNormal
  rw [hT.spectralPVM_toPMap_top]
  rfl

/-- If the spectral projection on `[c, ∞)` kills a vector, its quadratic form is at most
`c` times its squared norm. -/
theorem re_inner_le_of_boundedPVM_proj_Ici_eq_zero (c : ℝ) {ξ : H}
    (hξ : (boundedPVM hT).proj (Set.Ici c) measurableSet_Ici ξ = 0) :
    (⟪T ξ, ξ⟫_ℂ).re ≤ c * ‖ξ‖ ^ 2 := by
  let x : ((T : H →ₗ[ℂ] H).toPMap ⊤).domain := ⟨ξ, by simp⟩
  have hx : (x : H) ∈ ((boundedPVM hT).proj (Set.Ici c)ᶜ
      measurableSet_Ici.compl).range := by
    refine ⟨ξ, ?_⟩
    rw [ProjValMeasure.proj_compl _ _ measurableSet_Ici]
    change (ContinuousLinearMap.id ℂ H - (boundedPVM hT).proj
      (Set.Ici c) measurableSet_Ici) ξ = ξ
    rw [_root_.sub_apply, ContinuousLinearMap.id_apply, hξ, sub_zero]
  rw [boundedPVM_eq_toPMap_top hT] at hx
  have hTop := LinearPMap.isSelfAdjoint_toPMap_top hT
  have h := hTop.re_inner_le_mul_norm_sq_of_mem_range_spectralPVM_proj
    measurableSet_Ici.compl (fun _ hs => le_of_lt (lt_of_not_ge hs)) hx
  change (⟪T ξ, ξ⟫_ℂ).re ≤ c * ‖ξ‖ ^ 2 at h
  exact h

/-- If the spectral projection on `(-∞, c]` kills a vector, its quadratic form is at least
`c` times its squared norm. -/
theorem le_re_inner_of_boundedPVM_proj_Iic_eq_zero (c : ℝ) {ξ : H}
    (hξ : (boundedPVM hT).proj (Set.Iic c) measurableSet_Iic ξ = 0) :
    c * ‖ξ‖ ^ 2 ≤ (⟪T ξ, ξ⟫_ℂ).re := by
  let x : ((T : H →ₗ[ℂ] H).toPMap ⊤).domain := ⟨ξ, by simp⟩
  have hx : (x : H) ∈ ((boundedPVM hT).proj (Set.Iic c)ᶜ
      measurableSet_Iic.compl).range := by
    refine ⟨ξ, ?_⟩
    rw [ProjValMeasure.proj_compl _ _ measurableSet_Iic]
    change (ContinuousLinearMap.id ℂ H - (boundedPVM hT).proj
      (Set.Iic c) measurableSet_Iic) ξ = ξ
    rw [_root_.sub_apply, ContinuousLinearMap.id_apply, hξ, sub_zero]
  rw [boundedPVM_eq_toPMap_top hT] at hx
  have hTop := LinearPMap.isSelfAdjoint_toPMap_top hT
  have h := hTop.mul_norm_sq_le_re_inner_of_mem_range_spectralPVM_proj
    measurableSet_Iic.compl (fun _ hs => le_of_lt (lt_of_not_ge hs)) hx
  change c * ‖ξ‖ ^ 2 ≤ (⟪T ξ, ξ⟫_ℂ).re at h
  exact h

end BoundedSelfAdjoint

end BorelCalculus
end TauCeti

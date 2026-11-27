/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import TauCeti.Analysis.InnerProductSpace.BorelCalculus.Basic
public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Map
public import ForTauCeti.Analysis.InnerProductSpace.OperatorExt
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.ProjValMeasure.Basic

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

/-- A projection of the real-line spectral measure is the Borel calculus of the
indicator of the corresponding band. -/
theorem boundedPVM_proj (B : Set ℝ) (hB : MeasurableSet B) :
    haveI := hT.isStarNormal
    ((T.toLinearMap.toPMap ⊤).spectralPVM (LinearPMap.isSelfAdjoint_toPMap_top hT)).proj B hB =
      T.borelCalculus
        (BoundedBorelFunction.indicator (reCoord ⁻¹' B) (measurable_reCoord hB) 1) := by
  have := hT.isStarNormal
  rw [hT.spectralPVM_toPMap_top, ProjValMeasure.map_proj, T.borelCalculus_indicator]
  rfl

/-- The diagonal measures of the real-line spectral measure are the pushforwards
of the diagonal measures along the real-part relabelling. -/
theorem boundedPVM_diag (ξ : H) :
    ((T.toLinearMap.toPMap ⊤).spectralPVM (LinearPMap.isSelfAdjoint_toPMap_top hT)).diag ξ =
      Measure.map reCoord ((cfcHom hT.isStarNormal).representationDiagMeasure ξ) := by
  have := hT.isStarNormal
  rw [hT.spectralPVM_toPMap_top, ProjValMeasure.map_diag, T.spectralPVM_eq_ofRepresentation,
    ProjValMeasure.ofRepresentation_diag]
  rfl

/-- **The bridge to the continuous functional calculus.**  A spectral projection
of a bounded self-adjoint operator is the continuous functional calculus of any
continuous symbol agreeing with the indicator on the spectrum — which is all the
bounded-operator lane ever needs from a Borel calculus. -/
theorem boundedPVM_proj_eq_cfcHom (s : Set ℝ) (hs : MeasurableSet s)
    (g : C(spectrum ℂ T, ℂ))
    (hg : ∀ w, g w = (reCoord ⁻¹' s).indicator (fun _ => (1 : ℂ)) w) :
    ((T.toLinearMap.toPMap ⊤).spectralPVM (LinearPMap.isSelfAdjoint_toPMap_top hT)).proj s hs =
      cfcHom hT.isStarNormal g := by
  have := hT.isStarNormal
  rw [boundedPVM_proj hT s hs, ← T.borelCalculus_ofContinuousMap g]
  congr 1
  ext w
  by_cases hw : w ∈ reCoord ⁻¹' s <;> simp [hw, hg w]

/-- **A spectral projection of a bounded self-adjoint operator commutes with
it** -- so its range and the orthogonal complement of its range are both
invariant, i.e. every spectral subspace reduces the operator. -/
theorem boundedPVM_proj_comm (s : Set ℝ) (hs : MeasurableSet s) :
    T * ((T.toLinearMap.toPMap ⊤).spectralPVM (LinearPMap.isSelfAdjoint_toPMap_top hT)).proj s hs =
      ((T.toLinearMap.toPMap ⊤).spectralPVM
        (LinearPMap.isSelfAdjoint_toPMap_top hT)).proj s hs * T := by
  have := hT.isStarNormal
  rw [hT.spectralPVM_toPMap_top, ProjValMeasure.map_proj]
  exact ((T.forall_commute_spectralPVM_proj_iff T).2 (Commute.refl T) _ _).eq

/-- If the spectral projection on `[c, ∞)` kills a vector, its quadratic form is at most
`c` times its squared norm. -/
theorem re_inner_le_of_boundedPVM_proj_Ici_eq_zero (c : ℝ) {ξ : H}
    (hξ : ((T.toLinearMap.toPMap ⊤).spectralPVM (LinearPMap.isSelfAdjoint_toPMap_top hT)).proj
      (Set.Ici c) measurableSet_Ici ξ = 0) :
    (⟪T ξ, ξ⟫_ℂ).re ≤ c * ‖ξ‖ ^ 2 := by
  have hTop := LinearPMap.isSelfAdjoint_toPMap_top hT
  let P := (T.toLinearMap.toPMap ⊤).spectralPVM hTop
  let x : ((T : H →ₗ[ℂ] H).toPMap ⊤).domain := ⟨ξ, by simp⟩
  have hx : (x : H) ∈ (P.proj (Set.Ici c)ᶜ
      measurableSet_Ici.compl).range := by
    refine ⟨ξ, ?_⟩
    rw [ProjValMeasure.proj_compl _ _ measurableSet_Ici]
    change (ContinuousLinearMap.id ℂ H - P.proj
      (Set.Ici c) measurableSet_Ici) ξ = ξ
    change P.proj (Set.Ici c) measurableSet_Ici ξ = 0 at hξ
    rw [_root_.sub_apply, ContinuousLinearMap.id_apply, hξ, sub_zero]
  have h := hTop.re_inner_le_mul_norm_sq_of_mem_range_spectralPVM_proj
    measurableSet_Ici.compl (fun _ hs => le_of_lt (lt_of_not_ge hs)) hx
  change (⟪T ξ, ξ⟫_ℂ).re ≤ c * ‖ξ‖ ^ 2 at h
  exact h

/-- If the spectral projection on `(-∞, c]` kills a vector, its quadratic form is at least
`c` times its squared norm. -/
theorem le_re_inner_of_boundedPVM_proj_Iic_eq_zero (c : ℝ) {ξ : H}
    (hξ : ((T.toLinearMap.toPMap ⊤).spectralPVM (LinearPMap.isSelfAdjoint_toPMap_top hT)).proj
      (Set.Iic c) measurableSet_Iic ξ = 0) :
    c * ‖ξ‖ ^ 2 ≤ (⟪T ξ, ξ⟫_ℂ).re := by
  have hTop := LinearPMap.isSelfAdjoint_toPMap_top hT
  let P := (T.toLinearMap.toPMap ⊤).spectralPVM hTop
  let x : ((T : H →ₗ[ℂ] H).toPMap ⊤).domain := ⟨ξ, by simp⟩
  have hx : (x : H) ∈ (P.proj (Set.Iic c)ᶜ
      measurableSet_Iic.compl).range := by
    refine ⟨ξ, ?_⟩
    rw [ProjValMeasure.proj_compl _ _ measurableSet_Iic]
    change (ContinuousLinearMap.id ℂ H - P.proj
      (Set.Iic c) measurableSet_Iic) ξ = ξ
    change P.proj (Set.Iic c) measurableSet_Iic ξ = 0 at hξ
    rw [_root_.sub_apply, ContinuousLinearMap.id_apply, hξ, sub_zero]
  have h := hTop.mul_norm_sq_le_re_inner_of_mem_range_spectralPVM_proj
    measurableSet_Iic.compl (fun _ hs => le_of_lt (lt_of_not_ge hs)) hx
  change c * ‖ξ‖ ^ 2 ≤ (⟪T ξ, ξ⟫_ℂ).re at h
  exact h

end BoundedSelfAdjoint

end BorelCalculus
end TauCeti

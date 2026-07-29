/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.BorelCalculus.Multiplicative
public import ForTauCeti.Analysis.InnerProductSpace.ProjValMeasure.Basic

/-!
# Projection-valued measures from the Borel calculus

Applying the bounded Borel functional calculus to indicator functions turns a
normal operator into a projection-valued measure.  The sets are indexed along an
arbitrary measurable *relabelling* `κ : spectrum ℂ a → ℝ`, because
`TauCeti.ProjValMeasure` is a measure on the Borel sets of `ℝ` while the
spectrum of a normal operator lives in `ℂ`; for a self-adjoint operator `κ` will
be the real part, and for the Cayley transform of an unbounded self-adjoint
operator it will be the inverse Cayley map.

## Provenance

*New*; see `ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/DiagonalMeasure.lean`.
The target structure `TauCeti.ProjValMeasure` is Spectra's, ported in
`ForTauCeti/Analysis/InnerProductSpace/ProjValMeasure/Basic.lean`; the
construction filling it here is not.
-/

@[expose] public section

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

section Projections

variable (ha : IsStarNormal a) {κ : spectrum ℂ a → ℝ} (hκ : Measurable κ)

/-- The spectral projection attached to a Borel subset of `ℝ`, pulled back along
the relabelling `κ`. -/
noncomputable def specProj (B : Set ℝ) (hB : MeasurableSet B) : H →L[ℂ] H :=
  borelCalculus ha (isBddMeasurable_indicator (a := a) (hκ hB))

/-- The relabelled diagonal measure. -/
noncomputable def specDiag (κ' : spectrum ℂ a → ℝ) (ξ : H) : Measure ℝ :=
  Measure.map κ' (diagMeasure ha ξ)

include hκ in
theorem isFiniteMeasure_specDiag (ξ : H) : IsFiniteMeasure (specDiag ha κ ξ) := by
  refine ⟨?_⟩
  rw [specDiag, Measure.map_apply hκ MeasurableSet.univ]
  exact measure_lt_top _ _

/-- The weld: the diagonal matrix element of a spectral projection is the mass
the relabelled diagonal measure gives to the set. -/
theorem inner_specProj_self (B : Set ℝ) (hB : MeasurableSet B) (ξ : H) :
    ⟪ξ, specProj ha hκ B hB ξ⟫_ℂ = (((specDiag ha κ ξ) B).toReal : ℂ) := by
  rw [specProj, inner_borelCalculus_self, integral_indicator_const _ (hκ hB),
    specDiag, Measure.map_apply hκ hB, Complex.real_smul, mul_one,
    MeasureTheory.measureReal_def]

/-- The whole line carries the identity. -/
theorem specProj_univ :
    specProj (H := H) ha hκ Set.univ MeasurableSet.univ = ContinuousLinearMap.id ℂ H := by
  refine op_ext_of_inner_self fun ξ => ?_
  rw [inner_specProj_self]
  have hm : ((specDiag ha κ ξ) Set.univ).toReal = ‖ξ‖ ^ 2 := by
    rw [specDiag, Measure.map_apply hκ MeasurableSet.univ, Set.preimage_univ,
      diagMeasure_univ_toReal]
  rw [hm]
  change (((‖ξ‖ ^ 2 : ℝ)) : ℂ) = ⟪ξ, ξ⟫_ℂ
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast

/-- Multiplicativity: intersection of sets is composition of projections. -/
theorem specProj_inter (B₁ B₂ : Set ℝ) (hB₁ : MeasurableSet B₁) (hB₂ : MeasurableSet B₂) :
    specProj (H := H) ha hκ B₁ hB₁ * specProj ha hκ B₂ hB₂
      = specProj ha hκ (B₁ ∩ B₂) (hB₁.inter hB₂) := by
  refine ContinuousLinearMap.ext fun ξ => ext_inner_left ℂ fun ψ => ?_
  have hprod : (fun x => (κ ⁻¹' B₁).indicator (fun _ => (1 : ℂ)) x *
        (κ ⁻¹' B₂).indicator (fun _ => (1 : ℂ)) x)
      = (κ ⁻¹' (B₁ ∩ B₂)).indicator (fun _ => (1 : ℂ)) := by
    ext x
    by_cases hx1 : x ∈ κ ⁻¹' B₁ <;> by_cases hx2 : x ∈ κ ⁻¹' B₂ <;>
      simp only [Set.mem_preimage] at hx1 hx2 <;>
      simp [Set.mem_preimage, Set.mem_inter_iff, hx1, hx2]
  have hL : ⟪ψ, (specProj (H := H) ha hκ B₁ hB₁ * specProj ha hκ B₂ hB₂) ξ⟫_ℂ
      = pair ha (fun x => (κ ⁻¹' B₁).indicator (fun _ => (1 : ℂ)) x *
          (κ ⁻¹' B₂).indicator (fun _ => (1 : ℂ)) x) ψ ξ :=
    (pair_mul_eq_inner_comp ha (isBddMeasurable_indicator (a := a) (hκ hB₁))
      (isBddMeasurable_indicator (a := a) (hκ hB₂)) ψ ξ).symm
  rw [hL, hprod, specProj, inner_borelCalculus]

/-- **The projection-valued measure of a normal operator**, indexed along a
measurable relabelling `κ` of its spectrum. -/
noncomputable def toProjValMeasure : TauCeti.ProjValMeasure H where
  proj := specProj ha hκ
  diag := specDiag ha κ
  diag_finite := isFiniteMeasure_specDiag ha hκ
  inner_proj := inner_specProj_self ha hκ
  proj_univ := specProj_univ ha hκ
  proj_inter := specProj_inter ha hκ

@[simp] theorem toProjValMeasure_proj (B : Set ℝ) (hB : MeasurableSet B) :
    (toProjValMeasure (H := H) ha hκ).proj B hB = specProj ha hκ B hB := rfl

@[simp] theorem toProjValMeasure_diag (ξ : H) :
    (toProjValMeasure (H := H) ha hκ).diag ξ = specDiag ha κ ξ := rfl

end Projections

section BoundedSelfAdjoint

variable {T : H →L[ℂ] H} (hT : IsSelfAdjoint T)

/-- The real part, as a measurable relabelling of the spectrum of a bounded
self-adjoint operator.  Its spectrum is real, so this is a bijection onto the
spectrum and no Cayley detour is needed. -/
noncomputable def reCoord (w : spectrum ℂ T) : ℝ := (w : ℂ).re

omit [CompleteSpace H] in
theorem measurable_reCoord : Measurable (reCoord (T := T)) :=
  Complex.measurable_re.comp measurable_subtype_coe

/-- **The spectral measure of a bounded self-adjoint operator**, indexed along
the real part of its spectrum. -/
noncomputable def boundedPVM : TauCeti.ProjValMeasure H :=
  toProjValMeasure hT.isStarNormal measurable_reCoord

/-- **The bridge to the continuous functional calculus.**  A spectral projection
of a bounded self-adjoint operator is the continuous functional calculus of any
continuous symbol agreeing with the indicator on the spectrum — which is all the
bounded-operator lane ever needs from a Borel calculus. -/
theorem boundedPVM_proj_eq_cfcHom (s : Set ℝ) (hs : MeasurableSet s)
    (g : C(spectrum ℂ T, ℂ))
    (hg : ∀ w, g w = (reCoord ⁻¹' s).indicator (fun _ => (1 : ℂ)) w) :
    (boundedPVM hT).proj s hs = cfcHom hT.isStarNormal g := by
  rw [boundedPVM, toProjValMeasure_proj, specProj,
    ← borelCalculus_of_continuous hT.isStarNormal g (IsBddMeasurable.of_continuous g)]
  exact borelCalculus_congr_ae _ _ _ fun η =>
    Filter.Eventually.of_forall fun w => (hg w).symm

end BoundedSelfAdjoint

end BorelCalculus
end TauCeti

/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.Ideals.Symmetric
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Bochner integration of compact-operator-valued functions

Compact continuous linear maps form a norm-closed linear subspace of the
bounded rectangular operator space.  Therefore the Bochner integral of an
integrable, almost-everywhere compact-valued function is compact.  This is the
closure fact needed by the Fourier Sylvester inverse.
-/

namespace ForMathlib
namespace DavisKahanExt

open MeasureTheory Filter

noncomputable section

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [CompleteSpace E]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [CompleteSpace F]

/-- Compact rectangular operators as a linear subspace. -/
def compactOperatorSubmodule : Submodule ℂ (E →L[ℂ] F) where
  carrier := {T | IsCompactOperator T}
  zero_mem' := isCompactOperator_zero
  add_mem' := fun hS hT => hS.add hT
  smul_mem' := fun c T hT => hT.smul c

/-- The compact-operator submodule is operator-norm closed. -/
theorem isClosed_compactOperatorSubmodule :
    IsClosed (compactOperatorSubmodule (E := E) (F := F) : Set (E →L[ℂ] F)) := by
  exact isClosed_setOf_isCompactOperator

/-- Bochner integration preserves compactness. -/
theorem isCompactOperator_integral
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → E →L[ℂ] F}
    (hf : Integrable f μ)
    (hcompact : ∀ᵐ a ∂μ, IsCompactOperator (f a)) :
    IsCompactOperator (∫ a, f a ∂μ) := by
  let K := compactOperatorSubmodule (E := E) (F := F)
  have hKclosed : IsClosed (K : Set (E →L[ℂ] F)) :=
    isClosed_compactOperatorSubmodule
  letI : CompleteSpace K := hKclosed.completeSpace_coe
  let g : α → K := fun a =>
    if ha : IsCompactOperator (f a) then ⟨f a, ha⟩ else 0
  have hgf : ∀ᵐ a ∂μ, ((g a : K) : E →L[ℂ] F) = f a := by
    filter_upwards [hcompact] with a ha
    simp [g, ha]
  have hg_meas : StronglyMeasurable g := by
    have hcoe : StronglyMeasurable fun a => ((g a : K) : E →L[ℂ] F) :=
      hf.stronglyMeasurable.congr hgf.symm
    exact stronglyMeasurable_subtype_mk hcoe
  have hg_norm : ∀ᵐ a ∂μ, ‖g a‖ = ‖f a‖ := by
    filter_upwards [hgf] with a ha
    exact congrArg norm ha
  have hg : Integrable g μ := by
    refine ⟨hg_meas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    exact hf.hasFiniteIntegral.congr' hg_norm
  let G : K := ∫ a, g a ∂μ
  have hcoeG : ((G : K) : E →L[ℂ] F) = ∫ a, f a ∂μ := by
    calc
      ((G : K) : E →L[ℂ] F)
          = ∫ a, ((g a : K) : E →L[ℂ] F) ∂μ := by
              exact (K.subtypeL.integral_comp_comm hg).symm
      _ = ∫ a, f a ∂μ := integral_congr_ae hgf
  rw [← hcoeG]
  exact G.property

end DavisKahanExt
end ForMathlib

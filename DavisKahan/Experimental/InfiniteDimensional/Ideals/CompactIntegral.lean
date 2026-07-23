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
    IsCompactOperator (∫ a, f a ∂μ : E →L[ℂ] F) := by
  -- Open obligation: lift the integrand into the closed compact-operator
  -- submodule `K` (complete via `IsClosed.completeSpace_coe`), transport
  -- integrability through `K.subtypeL`, and read off `(∫ g).property`.  The
  -- construction is sound; the remaining work is naming the subtype
  -- strong-measurability and `integral_comp_comm` lemmas in the pinned Mathlib.
  -- Handed to the mathematics agent.
  sorry

end

end DavisKahanExt
end ForMathlib

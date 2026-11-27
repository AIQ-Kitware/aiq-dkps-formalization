/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.BorelCalculus.Polarization
public import TauCeti.Analysis.InnerProductSpace.BorelCalculus.Basic

/-!
# Bounded Borel symbols and matrix elements

Existing consumers pass measurable bounded symbols as functions with a
predicate. Bundle the symbol for Tau Ceti's normal-operator calculus.
Polarization expresses its matrix elements in terms of the diagonal measures
used by the real and complex comparison proofs.
-/

public section

open scoped InnerProductSpace ENNReal CompactlySupported
open MeasureTheory

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace TauCeti
namespace BorelCalculus

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {a : H →L[ℂ] H}

/-- A symbol admissible for the bounded Borel calculus: measurable and bounded. -/
structure IsBddMeasurable (f : spectrum ℂ a → ℂ) : Prop where
  measurable : Measurable f
  exists_bound : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖f x‖ ≤ M

namespace IsBddMeasurable

/-- A nonnegative uniform chooseBound for an admissible symbol. -/
noncomputable def chooseBound {f : spectrum ℂ a → ℂ} (hf : IsBddMeasurable f) : ℝ :=
  hf.exists_bound.choose

omit [CompleteSpace H] in
/-- The chosen bound is nonnegative. -/
theorem chooseBound_nonneg {f : spectrum ℂ a → ℂ} (hf : IsBddMeasurable f) : 0 ≤ hf.chooseBound :=
  hf.exists_bound.choose_spec.1

omit [CompleteSpace H] in
/-- The chosen bound does bound the symbol.  It is *a* bound, not the supremum -- see
`chooseBound`. -/
theorem norm_le_chooseBound {f : spectrum ℂ a → ℂ} (hf : IsBddMeasurable f) (x : spectrum ℂ a) :
    ‖f x‖ ≤ hf.chooseBound :=
  hf.exists_bound.choose_spec.2 x

omit [CompleteSpace H] in
/-- Bundle a measurable bounded symbol for the native calculus. -/
noncomputable def toBoundedBorelFunction {f : spectrum ℂ a → ℂ}
    (hf : IsBddMeasurable f) : BoundedBorelFunction (spectrum ℂ a) :=
  BoundedBorelFunction.ofFunction f hf.measurable hf.exists_bound

omit [CompleteSpace H] in
@[simp] theorem toBoundedBorelFunction_apply {f : spectrum ℂ a → ℂ}
    (hf : IsBddMeasurable f) (x : spectrum ℂ a) : hf.toBoundedBorelFunction x = f x := by
  rw [toBoundedBorelFunction, BoundedBorelFunction.ofFunction_apply]

omit [CompleteSpace H] in
/-- The underlying function of a bounded Borel symbol is admissible. -/
theorem ofBoundedBorelFunction (f : BoundedBorelFunction (spectrum ℂ a)) :
    IsBddMeasurable (f : spectrum ℂ a → ℂ) :=
  ⟨f.measurable, f.exists_bound⟩

omit [CompleteSpace H] in
/-- Bundling the underlying function recovers the original symbol. -/
@[simp]
theorem toBoundedBorelFunction_ofBoundedBorelFunction (f : BoundedBorelFunction (spectrum ℂ a)) :
    (ofBoundedBorelFunction f).toBoundedBorelFunction = f :=
  BoundedBorelFunction.ext fun x => toBoundedBorelFunction_apply _ x

end IsBddMeasurable

variable (ha : IsStarNormal a) {f : spectrum ℂ a → ℂ}

/-- Apply the native Borel calculus to a symbol specified by admissibility. -/
noncomputable def borelCalculus (hf : IsBddMeasurable f) : H →L[ℂ] H :=
  letI := ha
  a.borelCalculus hf.toBoundedBorelFunction

/-- Rewrite a calculus application in terms of the bundled upstream symbol. -/
theorem borelCalculus_eq_native (hf : IsBddMeasurable f) :
    haveI := ha
    borelCalculus ha hf = a.borelCalculus hf.toBoundedBorelFunction := (rfl)

/-- The spectral diagonal measures agree with those of the continuous representation. -/
theorem spectralPVM_diag_eq_representation (ξ : H) :
    haveI := ha
    a.spectralPVM.diag ξ = (cfcHom ha).representationDiagMeasure ξ := by
  have := ha
  rw [a.spectralPVM_eq_ofRepresentation, ProjValMeasure.ofRepresentation_diag]

/-- Diagonal matrix elements are integrals against the continuous representation measure. -/
theorem inner_borelCalculus_self (hf : IsBddMeasurable f) (ξ : H) :
    ⟪ξ, borelCalculus ha hf ξ⟫_ℂ = ∫ x, f x ∂((cfcHom ha).representationDiagMeasure ξ) := by
  have := ha
  simp only [borelCalculus_eq_native, a.inner_borelCalculus_self, ← a.spectralPVM_diag,
    spectralPVM_diag_eq_representation ha, IsBddMeasurable.toBoundedBorelFunction_apply]

/-- The matrix elements of the native calculus are the polarized diagonal integrals. -/
@[simp] theorem inner_borelCalculus (hf : IsBddMeasurable f) (ψ ξ : H) :
    ⟪ψ, borelCalculus ha hf ξ⟫_ℂ = pair ha f ψ ξ := by
  rw [pair_def, ← inner_borelCalculus_self ha hf, ← inner_borelCalculus_self ha hf,
    ← inner_borelCalculus_self ha hf, ← inner_borelCalculus_self ha hf]
  exact ((borelCalculus ha hf).toLinearMap.inner_polarization ψ ξ).symm

end BorelCalculus
end TauCeti

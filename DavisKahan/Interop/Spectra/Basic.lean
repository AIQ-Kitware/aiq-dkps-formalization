/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.BoundedOperator.Basic
import Spectra.Operator.Bounded

/-!
# Basic bridge from bounded Davis--Kahan operators to Spectra

This bridge is additive. It does not replace the scalar-generic bounded theory
or the independent experimental spectral constructions. This first active
slice imports only Spectra's shallow bounded/unbounded operator bridge; the
canonical spectral-PVM route remains archived until Spectra's heavier
spectral-theorem import cone is ported to the root Lean/Mathlib revision.
-/

open scoped InnerProductSpace

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace SpectraBridge

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Regard a bounded symmetric operator as a Spectra self-adjoint operator with
full domain. -/
noncomputable def boundedSelfAdjointOperator (A : H →L[ℂ] H)
    (hA : IsSelfAdjointOperator A) :
    Spectra.Operator.SelfAdjointOperator H :=
  Spectra.Operator.SelfAdjointOperator.ofBounded A
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA)

@[simp]
theorem boundedSelfAdjointOperator_domain (A : H →L[ℂ] H)
    (hA : IsSelfAdjointOperator A) :
    (boundedSelfAdjointOperator A hA).domain = ⊤ :=
  Spectra.Operator.SelfAdjointOperator.domain_ofBounded A
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA)

/-- The bounded extension of the bridged operator is the original map. -/
theorem boundedExtension_boundedSelfAdjointOperator
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A) :
    (boundedSelfAdjointOperator A hA).boundedExtension
      ((boundedSelfAdjointOperator_domain A hA)) = A := by
  apply ContinuousLinearMap.ext
  intro x
  rw [Spectra.Operator.SelfAdjointOperator.boundedExtension_apply]
  rfl

end SpectraBridge
end Experimental
end DavisKahan
end ForMathlib

/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.Interop.Spectra.HalmosTwoProjections

/-!
# Unitary equivalence of subspace pairs and bounded operators

Grounded relational predicates promoted out of the experimental Davis--Kahan
frontier.  They express unitary equivalence of ordered pairs of subspaces and of
bounded operators acting on possibly different Hilbert spaces, stated as bare
existential propositions so they carry no computational datum.
-/

open scoped InnerProductSpace

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace Frontier

open SpectraBridge

universe u v

section CrossSpaceClassification

variable {H₁ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [CompleteSpace H₁]
variable {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
  [CompleteSpace H₂]

/-- Unitary equivalence of two ordered pairs of subspaces.

Stated as existential quantification over the unitary rather than as a
`Prop`-valued structure carrying it: the intended notion is a proposition, and
a `Prop` structure cannot hold the datum `H₁ ≃ₗᵢ[ℂ] H₂`. -/
def PairOfSubspacesUnitaryEquivalent
    (U₁ V₁ : Submodule ℂ H₁) (U₂ V₂ : Submodule ℂ H₂) : Prop :=
  ∃ e : H₁ ≃ₗᵢ[ℂ] H₂,
    U₁.map e.toLinearMap = U₂ ∧ V₁.map e.toLinearMap = V₂

/-- Unitary equivalence of bounded operators acting on possibly different
Hilbert spaces.

The intertwining is stated pointwise.  Writing it as a composition of
continuous linear maps forces `e` through `LinearMap.toContinuousLinearMap`,
which carries a `FiniteDimensional` hypothesis that the source statement does
not have. -/
def BoundedOperatorsUnitaryEquivalent
    (A : H₁ →L[ℂ] H₁) (B : H₂ →L[ℂ] H₂) : Prop :=
  ∃ e : H₁ ≃ₗᵢ[ℂ] H₂, ∀ x : H₁, e (A x) = B (e x)

end CrossSpaceClassification

end Frontier
end Experimental
end DavisKahan
end ForMathlib

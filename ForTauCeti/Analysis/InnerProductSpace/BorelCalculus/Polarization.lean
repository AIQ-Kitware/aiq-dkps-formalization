/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import TauCeti.Analysis.InnerProductSpace.BorelCalculus.DiagonalMeasure
public import TauCeti.MeasureTheory.Function.ContinuousApproximation
public import TauCeti.Analysis.InnerProductSpace.OperatorIdentities

/-!
# Polarized diagonal integrals

The four diagonal integrals in `pair` express matrix elements of the native
Borel calculus. The explicit formula is used to transport those matrix
elements under changes of representation and real conjugation.
-/

public section

open scoped InnerProductSpace ENNReal CompactlySupported
open MeasureTheory

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace TauCeti
namespace BorelCalculus

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {a : H →L[ℂ] H}

section Pair

variable (ha : IsStarNormal a)

/-- The **polarised diagonal integral** of a symbol at a pair of vectors.  For
continuous symbols this is `⟪ψ, cfcHom f ξ⟫`; it is the blueprint for the
matrix elements of the bounded Borel calculus. -/
noncomputable def pair (f : spectrum ℂ a → ℂ) (ψ ξ : H) : ℂ :=
  (1 / 4 : ℂ) *
    ((∫ x, f x ∂((cfcHom ha).representationDiagMeasure (ξ + ψ)))
      + Complex.I * (∫ x, f x ∂((cfcHom ha).representationDiagMeasure (ξ + Complex.I • ψ)))
      - (∫ x, f x ∂((cfcHom ha).representationDiagMeasure (ξ - ψ)))
      - Complex.I * (∫ x, f x ∂((cfcHom ha).representationDiagMeasure (ξ - Complex.I • ψ))))

/-- Rewrite form of `pair`, so call sites need not unfold the definition.

Added 2026-07-30: `BorelCalculus/Operator` was doing `rw [pair]`, which requires the
body to be exposed. Tau Ceti's `api-design` rubric asks for the lemma instead. -/
theorem pair_def (f : spectrum ℂ a → ℂ) (ψ ξ : H) :
    pair ha f ψ ξ = (1 / 4 : ℂ) *
      ((∫ x, f x ∂((cfcHom ha).representationDiagMeasure (ξ + ψ)))
        + Complex.I * (∫ x, f x ∂((cfcHom ha).representationDiagMeasure (ξ + Complex.I • ψ)))
        - (∫ x, f x ∂((cfcHom ha).representationDiagMeasure (ξ - ψ)))
        - Complex.I * (∫ x, f x ∂((cfcHom ha).representationDiagMeasure (ξ - Complex.I • ψ)))) :=
          (rfl)

end Pair

end BorelCalculus
end TauCeti

/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import ForTauCeti.Analysis.OperatorIdeal.Family.OperatorNorm
import DavisKahan.SpectralTheory.ClosedOperator.Basic
import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Sylvester
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-!
# Closed Sylvester equations and everywhere-bounded inverses

The proved front of the unbounded spectral development: the closed Sylvester
equation interface, closed resolvent data, and everywhere-defined bounded
inverses.  The spectral projection and truncation theory that is still open
stays in `DavisKahan.InfiniteDimensional.Core.UnboundedSpectral`.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace
open scoped Topology
open Filter

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Local shorthand for a closed operator on the left space. -/
abbrev ClosedOperatorE :=
  TauCeti.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := E)
/-- Local shorthand for a closed operator on the right space. -/
abbrev ClosedOperatorF :=
  TauCeti.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := F)

/-- Compatibility facade for a lower semibound of the canonical partial map. -/
abbrev SemiboundedBelow
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E)) (c : ℝ) : Prop :=
  TauCeti.LinearPMap.SemiboundedBelow A.toLinearPMap c

/-- Compatibility facade for an upper semibound of the canonical partial map. -/
abbrev SemiboundedAbove
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E)) (c : ℝ) : Prop :=
  TauCeti.LinearPMap.SemiboundedAbove A.toLinearPMap c

/-- Compatibility facade for the canonical `LinearPMap` Sylvester equation.

Closedness, dense domain, and self-adjointness are properties of `A.toLinearPMap`
and `B.toLinearPMap`; the algebraic equation itself is no longer tied to the
historical bundled representation. -/
abbrev ClosedSylvesterEquation
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (B : ClosedOperatorF (𝕜 := 𝕜) (F := F))
    (X C : F →L[𝕜] E) : Prop :=
  TauCeti.LinearPMap.SylvesterEquation A.toLinearPMap B.toLinearPMap X C

/-- Compatibility name retained for the existing experimental theorem graph.

The arguments are written explicitly rather than leaving Lean to synthesize the
ambient Hilbert spaces from the polymorphic structure constant.  This avoids a
stuck `CompleteSpace` metavariable at the alias declaration. -/
abbrev HasClosedSylvesterEquation
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (B : ClosedOperatorF (𝕜 := 𝕜) (F := F))
    (X C : F →L[𝕜] E) : Prop :=
  ClosedSylvesterEquation A B X C

namespace ClosedSylvesterEquation

omit [CompleteSpace E] [CompleteSpace F] in
/-- Rewrite the canonical partial-map equation through the historical
`toLinearMap` fields.  The explicit output-domain witness may be any proof of
the required membership; proof irrelevance identifies it with the witness
stored by the canonical equation. -/
theorem equation_toLinearMap
    {A : ClosedOperatorE (𝕜 := 𝕜) (E := E)}
    {B : ClosedOperatorF (𝕜 := 𝕜) (F := F)}
    {X C : F →L[𝕜] E}
    (h : HasClosedSylvesterEquation A B X C)
    (x : B.domain) (hx : X (x : F) ∈ A.domain) :
    A.toLinearMap ⟨X (x : F), hx⟩ - X (B.toLinearMap x) = C (x : F) := by
  have heq := h.equation x
  simp only [
    TauCeti.DavisKahanExt.ClosedOperator.toLinearPMap_apply] at heq
  have harg :
      (⟨X (x : F), hx⟩ : A.domain) =
        ⟨X (x : F), h.mapsTo_domain x⟩ := by
    apply Subtype.ext
    rfl
  rw [harg]
  exact heq

end ClosedSylvesterEquation

/-- Compatibility facade for a bounded everywhere inverse of the canonical
partial map. -/
abbrev HasBoundedEverywhereInverse
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E)) :=
  TauCeti.LinearPMap.HasBoundedEverywhereInverse A.toLinearPMap

end ExactSinTheta
end DavisKahan
end TauCeti
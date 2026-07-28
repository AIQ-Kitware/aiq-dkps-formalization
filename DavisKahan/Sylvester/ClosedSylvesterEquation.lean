/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.OperatorIdeal.UnitarilyInvariant.RectangularFamily
import DavisKahan.SpectralTheory.ClosedOperator.Basic
import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Sylvester
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-!
# Closed Sylvester equations and everywhere-bounded inverses

The proved front of the unbounded spectral development: the closed Sylvester
equation interface, closed resolvent data, and everywhere-defined bounded
inverses.  The spectral projection and truncation theory that is still open
stays in `DavisKahan.Experimental.InfiniteDimensional.Core.UnboundedSpectral`.
-/

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open scoped InnerProductSpace
open scoped Topology
open Filter

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

abbrev ClosedOperatorE :=
  TauCeti.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := E)
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

omit [CompleteSpace E] in
/-- Extract the operator-domain transport from a Sylvester equation. -/
theorem mapsTo
    {A : ClosedOperatorE (𝕜 := 𝕜) (E := E)}
    {B : ClosedOperatorF (𝕜 := 𝕜) (F := F)}
    {X C : F →L[𝕜] E}
    (h : HasClosedSylvesterEquation A B X C) :
    A.MapsDomainTo B X :=
  TauCeti.LinearPMap.SylvesterEquation.mapsTo h

omit [CompleteSpace E] [CompleteSpace F] in
/-- A bounded Sylvester equation is a full-domain closed Sylvester equation. -/
theorem ofBounded
    {A : E →L[𝕜] E} {B : F →L[𝕜] F} {X C : F →L[𝕜] E}
    (hEq : A ∘L X - X ∘L B = C) :
    HasClosedSylvesterEquation
      (TauCeti.DavisKahanExt.ClosedOperator.ofBounded A)
      (TauCeti.DavisKahanExt.ClosedOperator.ofBounded B) X C := by
  refine {
    mapsTo_domain := ?_
    equation := ?_
  }
  · intro x
    simp
  · intro x
    have hx := congrArg (fun T : F →L[𝕜] E => T (x : F)) hEq
    change A (X (x : F)) - X (B (x : F)) = C (x : F)
    simpa only [ContinuousLinearMap.comp_apply, sub_apply] using hx

omit [CompleteSpace E] [CompleteSpace F] in
/-- The zero map solves the homogeneous domain-aware equation. -/
theorem zero
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (B : ClosedOperatorF (𝕜 := 𝕜) (F := F)) :
    HasClosedSylvesterEquation A B 0 0 :=
  TauCeti.LinearPMap.SylvesterEquation.zero A.toLinearPMap B.toLinearPMap

omit [CompleteSpace E] [CompleteSpace F] in
/-- Domain-aware Sylvester equations add. -/
theorem add
    {A : ClosedOperatorE (𝕜 := 𝕜) (E := E)}
    {B : ClosedOperatorF (𝕜 := 𝕜) (F := F)}
    {X Y C D : F →L[𝕜] E}
    (hX : HasClosedSylvesterEquation A B X C)
    (hY : HasClosedSylvesterEquation A B Y D) :
    HasClosedSylvesterEquation A B (X + Y) (C + D) :=
  TauCeti.LinearPMap.SylvesterEquation.add hX hY

omit [CompleteSpace E] [CompleteSpace F] in
/-- Domain-aware Sylvester equations are preserved by negation. -/
theorem neg
    {A : ClosedOperatorE (𝕜 := 𝕜) (E := E)}
    {B : ClosedOperatorF (𝕜 := 𝕜) (F := F)}
    {X C : F →L[𝕜] E}
    (hX : HasClosedSylvesterEquation A B X C) :
    HasClosedSylvesterEquation A B (-X) (-C) :=
  TauCeti.LinearPMap.SylvesterEquation.neg hX

omit [CompleteSpace E] [CompleteSpace F] in
/-- Domain-aware Sylvester equations subtract. -/
theorem sub
    {A : ClosedOperatorE (𝕜 := 𝕜) (E := E)}
    {B : ClosedOperatorF (𝕜 := 𝕜) (F := F)}
    {X Y C D : F →L[𝕜] E}
    (hX : HasClosedSylvesterEquation A B X C)
    (hY : HasClosedSylvesterEquation A B Y D) :
    HasClosedSylvesterEquation A B (X - Y) (C - D) :=
  TauCeti.LinearPMap.SylvesterEquation.sub hX hY

omit [CompleteSpace E] [CompleteSpace F] in
/-- Domain-aware Sylvester equations commute with scalar multiplication. -/
theorem smul
    {A : ClosedOperatorE (𝕜 := 𝕜) (E := E)}
    {B : ClosedOperatorF (𝕜 := 𝕜) (F := F)}
    {X C : F →L[𝕜] E}
    (hX : HasClosedSylvesterEquation A B X C) (c : 𝕜) :
    HasClosedSylvesterEquation A B (c • X) (c • C) :=
  TauCeti.LinearPMap.SylvesterEquation.smul hX c

end ClosedSylvesterEquation

/-- Compatibility facade for a bounded everywhere inverse of the canonical
partial map. -/
abbrev HasBoundedEverywhereInverse
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E)) :=
  TauCeti.LinearPMap.HasBoundedEverywhereInverse A.toLinearPMap

namespace HasBoundedEverywhereInverse

omit [CompleteSpace E] in
/-- A closed operator with an everywhere-defined two-sided inverse is injective. -/
theorem injective
    {A : ClosedOperatorE (𝕜 := 𝕜) (E := E)}
    (hA : HasBoundedEverywhereInverse A) :
    Function.Injective A.toLinearMap :=
  TauCeti.LinearPMap.HasBoundedEverywhereInverse.injective hA

omit [CompleteSpace E] in
/-- The operator action is onto the ambient Hilbert space. -/
theorem surjective
    {A : ClosedOperatorE (𝕜 := 𝕜) (E := E)}
    (hA : HasBoundedEverywhereInverse A) :
    Function.Surjective A.toLinearMap :=
  TauCeti.LinearPMap.HasBoundedEverywhereInverse.surjective hA

end HasBoundedEverywhereInverse
end ExactSinTheta
end Experimental
end DavisKahan
end TauCeti
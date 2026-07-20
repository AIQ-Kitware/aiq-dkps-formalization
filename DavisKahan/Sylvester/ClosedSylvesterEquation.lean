/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.OperatorIdeal.UnitarilyInvariant.RectangularFamily
import DavisKahan.SpectralTheory.ClosedOperator.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-!
# Closed Sylvester equations and everywhere-bounded inverses

The proved front of the unbounded spectral development: the closed Sylvester
equation interface, closed resolvent data, and everywhere-defined bounded
inverses.  The spectral projection and truncation theory that is still open
stays in `DavisKahan.Experimental.InfiniteDimensional.Core.UnboundedSpectral`.
-/

namespace ForMathlib
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
  ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := E)
abbrev ClosedOperatorF :=
  ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := F)

/-- Lower semibound for a closed operator. -/
def SemiboundedBelow
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E)) (c : ℝ) : Prop :=
  ∀ x : A.domain,
    c * ‖(x : E)‖ ^ 2 ≤
      RCLike.re ⟪A.toLinearMap x, (x : E)⟫_𝕜

/-- Upper semibound for a closed operator. -/
def SemiboundedAbove
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E)) (c : ℝ) : Prop :=
  ∀ x : A.domain,
    RCLike.re ⟪A.toLinearMap x, (x : E)⟫_𝕜 ≤
      c * ‖(x : E)‖ ^ 2

omit [CompleteSpace E] in
/-- A lower semibound remains valid after decreasing the constant. -/
theorem SemiboundedBelow.mono
    {A : ClosedOperatorE (𝕜 := 𝕜) (E := E)} {c d : ℝ}
    (hA : SemiboundedBelow A c) (hdc : d ≤ c) :
    SemiboundedBelow A d := by
  intro x
  exact (mul_le_mul_of_nonneg_right hdc (sq_nonneg ‖(x : E)‖)).trans (hA x)

omit [CompleteSpace E] in
/-- An upper semibound remains valid after increasing the constant. -/
theorem SemiboundedAbove.mono
    {A : ClosedOperatorE (𝕜 := 𝕜) (E := E)} {c d : ℝ}
    (hA : SemiboundedAbove A c) (hcd : c ≤ d) :
    SemiboundedAbove A d := by
  intro x
  exact (hA x).trans
    (mul_le_mul_of_nonneg_right hcd (sq_nonneg ‖(x : E)‖))

/-- Domain-aware equation `A X - X B = C` for two closed blocks.

The domain transport is a named field rather than an existential nested inside
the equation.  This is essential for spectral-cutoff composition and for the
residual block identity in the unbounded sine theorem. -/
structure ClosedSylvesterEquation
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (B : ClosedOperatorF (𝕜 := 𝕜) (F := F))
    (X C : F →L[𝕜] E) : Prop where
  mapsTo_domain : A.MapsDomainTo B X
  equation : ∀ x : B.domain,
    A.toLinearMap ⟨X (x : F), mapsTo_domain x⟩ -
      X (B.toLinearMap x) = C (x : F)

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

omit [CompleteSpace E] in
/-- Extract the operator-domain transport from a Sylvester equation. -/
theorem mapsTo
    {A : ClosedOperatorE (𝕜 := 𝕜) (E := E)}
    {B : ClosedOperatorF (𝕜 := 𝕜) (F := F)}
    {X C : F →L[𝕜] E}
    (h : HasClosedSylvesterEquation A B X C) :
    A.MapsDomainTo B X :=
  h.mapsTo_domain

omit [CompleteSpace E] in
/-- A bounded Sylvester equation is a full-domain closed Sylvester equation. -/
theorem ofBounded
    {A : E →L[𝕜] E} {B : F →L[𝕜] F} {X C : F →L[𝕜] E}
    (hEq : A ∘L X - X ∘L B = C) :
    HasClosedSylvesterEquation
      (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded A)
      (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded B) X C := by
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

omit [CompleteSpace E] in
/-- The zero map solves the homogeneous domain-aware equation. -/
theorem zero
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (B : ClosedOperatorF (𝕜 := 𝕜) (F := F)) :
    HasClosedSylvesterEquation A B 0 0 := by
  refine ⟨?_, ?_⟩
  · intro x
    simp
  · intro x
    change A.toLinearMap (0 : A.domain) - 0 = (0 : E)
    simp

omit [CompleteSpace E] in
/-- Domain-aware Sylvester equations add. -/
theorem add
    {A : ClosedOperatorE (𝕜 := 𝕜) (E := E)}
    {B : ClosedOperatorF (𝕜 := 𝕜) (F := F)}
    {X Y C D : F →L[𝕜] E}
    (hX : HasClosedSylvesterEquation A B X C)
    (hY : HasClosedSylvesterEquation A B Y D) :
    HasClosedSylvesterEquation A B (X + Y) (C + D) := by
  refine ⟨?_, ?_⟩
  · intro x
    exact A.domain.add_mem (hX.mapsTo_domain x) (hY.mapsTo_domain x)
  · intro x
    change A.toLinearMap
        (⟨X (x : F), hX.mapsTo_domain x⟩ +
          ⟨Y (x : F), hY.mapsTo_domain x⟩) -
        (X (B.toLinearMap x) + Y (B.toLinearMap x)) =
      C (x : F) + D (x : F)
    rw [map_add, ← hX.equation x, ← hY.equation x]
    abel

omit [CompleteSpace E] in
/-- Domain-aware Sylvester equations are preserved by negation. -/
theorem neg
    {A : ClosedOperatorE (𝕜 := 𝕜) (E := E)}
    {B : ClosedOperatorF (𝕜 := 𝕜) (F := F)}
    {X C : F →L[𝕜] E}
    (hX : HasClosedSylvesterEquation A B X C) :
    HasClosedSylvesterEquation A B (-X) (-C) := by
  refine ⟨?_, ?_⟩
  · intro x
    exact A.domain.neg_mem (hX.mapsTo_domain x)
  · intro x
    change A.toLinearMap (-⟨X (x : F), hX.mapsTo_domain x⟩) -
        (-X (B.toLinearMap x)) = -C (x : F)
    rw [map_neg, ← hX.equation x]
    abel

omit [CompleteSpace E] in
/-- Domain-aware Sylvester equations subtract. -/
theorem sub
    {A : ClosedOperatorE (𝕜 := 𝕜) (E := E)}
    {B : ClosedOperatorF (𝕜 := 𝕜) (F := F)}
    {X Y C D : F →L[𝕜] E}
    (hX : HasClosedSylvesterEquation A B X C)
    (hY : HasClosedSylvesterEquation A B Y D) :
    HasClosedSylvesterEquation A B (X - Y) (C - D) := by
  simpa [sub_eq_add_neg] using hX.add hY.neg

omit [CompleteSpace E] in
/-- Domain-aware Sylvester equations commute with scalar multiplication. -/
theorem smul
    {A : ClosedOperatorE (𝕜 := 𝕜) (E := E)}
    {B : ClosedOperatorF (𝕜 := 𝕜) (F := F)}
    {X C : F →L[𝕜] E}
    (hX : HasClosedSylvesterEquation A B X C) (c : 𝕜) :
    HasClosedSylvesterEquation A B (c • X) (c • C) := by
  refine ⟨?_, ?_⟩
  · intro x
    exact A.domain.smul_mem c (hX.mapsTo_domain x)
  · intro x
    change A.toLinearMap (c • ⟨X (x : F), hX.mapsTo_domain x⟩) -
        c • X (B.toLinearMap x) = c • C (x : F)
    rw [map_smul, ← hX.equation x, smul_sub]

end ClosedSylvesterEquation

/-- A closed operator whose inverse is everywhere defined and bounded. -/
structure HasBoundedEverywhereInverse
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E)) where
  inv : E →L[𝕜] E
  inv_mapsTo_domain : ∀ y, inv y ∈ A.domain
  apply_inv : ∀ y,
    A.toLinearMap ⟨inv y, inv_mapsTo_domain y⟩ = y
  inv_apply : ∀ x : A.domain, inv (A.toLinearMap x) = (x : E)

namespace HasBoundedEverywhereInverse

omit [CompleteSpace E] in
/-- A closed operator with an everywhere-defined two-sided inverse is injective. -/
theorem injective
    {A : ClosedOperatorE (𝕜 := 𝕜) (E := E)}
    (hA : HasBoundedEverywhereInverse A) :
    Function.Injective A.toLinearMap := by
  intro x y hxy
  apply Subtype.ext
  calc
    (x : E) = hA.inv (A.toLinearMap x) := (hA.inv_apply x).symm
    _ = hA.inv (A.toLinearMap y) := congrArg hA.inv hxy
    _ = (y : E) := hA.inv_apply y

omit [CompleteSpace E] in
/-- The operator action is onto the ambient Hilbert space. -/
theorem surjective
    {A : ClosedOperatorE (𝕜 := 𝕜) (E := E)}
    (hA : HasBoundedEverywhereInverse A) :
    Function.Surjective A.toLinearMap := by
  intro y
  exact ⟨⟨hA.inv y, hA.inv_mapsTo_domain y⟩, hA.apply_inv y⟩

end HasBoundedEverywhereInverse
end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib

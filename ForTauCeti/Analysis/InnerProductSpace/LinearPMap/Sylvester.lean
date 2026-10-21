/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Sylvester

/-!
# Form bounds for partial linear maps

Lower and upper quadratic-form bounds for Mathlib `LinearPMap` operators.
The domain-aware Sylvester equation is provided by the accepted upstream
Tau Ceti API in `LinearPMap.Sylvester` and is used there directly.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `DavisKahan/SpectralTheory/ClosedOperator/Basic.lean`.
* Extraction class: reusable semibound predicates not yet provided upstream.
-/

public section

namespace TauCeti
namespace LinearPMap

open scoped InnerProductSpace

universe u v w

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Lower semibound for a partial linear map. -/
def SemiboundedBelow (A : E →ₗ.[𝕜] E) (c : ℝ) : Prop :=
  ∀ x : A.domain,
    c * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : E)⟫_𝕜

/-- Upper semibound for a partial linear map. -/
def SemiboundedAbove (A : E →ₗ.[𝕜] E) (c : ℝ) : Prop :=
  ∀ x : A.domain,
    RCLike.re ⟪A x, (x : E)⟫_𝕜 ≤ c * ‖(x : E)‖ ^ 2

/-- Unfolds the lower semibound through a stable public API. -/
theorem semiboundedBelow_iff (A : E →ₗ.[𝕜] E) (c : ℝ) :
    SemiboundedBelow A c ↔
      ∀ x : A.domain, c * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : E)⟫_𝕜 :=
  Iff.rfl

/-- Unfolds the upper semibound through a stable public API. -/
theorem semiboundedAbove_iff (A : E →ₗ.[𝕜] E) (c : ℝ) :
    SemiboundedAbove A c ↔
      ∀ x : A.domain, RCLike.re ⟪A x, (x : E)⟫_𝕜 ≤ c * ‖(x : E)‖ ^ 2 :=
  Iff.rfl

/-- A lower semibound remains valid after decreasing the constant. -/
theorem SemiboundedBelow.mono {A : E →ₗ.[𝕜] E} {c d : ℝ}
    (hA : SemiboundedBelow A c) (hdc : d ≤ c) :
    SemiboundedBelow A d := by
  intro x
  exact (mul_le_mul_of_nonneg_right hdc (sq_nonneg ‖(x : E)‖)).trans (hA x)

/-- An upper semibound remains valid after increasing the constant. -/
theorem SemiboundedAbove.mono {A : E →ₗ.[𝕜] E} {c d : ℝ}
    (hA : SemiboundedAbove A c) (hcd : c ≤ d) :
    SemiboundedAbove A d := by
  intro x
  exact (hA x).trans
    (mul_le_mul_of_nonneg_right hcd (sq_nonneg ‖(x : E)‖))

/-- A Sylvester equation with a partial left block and a bounded right block.
This is the upstream domain-aware equation with the right block embedded on its
full domain. -/
abbrev UnboundedBoundedSylvesterEquation
    {F : Type w} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    (A : E →ₗ.[𝕜] E) (B : F →L[𝕜] F) (X C : F →L[𝕜] E) : Prop :=
  _root_.LinearPMap.SylvesterEquation A (B.toLinearMap.toPMap ⊤) X C

/-- A partial linear map whose inverse is everywhere defined and bounded. -/
structure HasBoundedEverywhereInverse (A : E →ₗ.[𝕜] E) where
  inv : E →L[𝕜] E
  inv_mapsTo_domain : ∀ y, inv y ∈ A.domain
  apply_inv : ∀ y, A ⟨inv y, inv_mapsTo_domain y⟩ = y
  inv_apply : ∀ x : A.domain, inv (A x) = (x : E)

namespace HasBoundedEverywhereInverse

/-- A partial map with an everywhere-defined two-sided inverse is injective. -/
theorem injective {A : E →ₗ.[𝕜] E}
    (hA : HasBoundedEverywhereInverse A) :
    Function.Injective A := by
  intro x y hxy
  apply Subtype.ext
  calc
    (x : E) = hA.inv (A x) := (hA.inv_apply x).symm
    _ = hA.inv (A y) := congrArg hA.inv hxy
    _ = (y : E) := hA.inv_apply y

/-- A partial map with an everywhere-defined two-sided inverse is surjective
onto the ambient codomain. -/
theorem surjective {A : E →ₗ.[𝕜] E}
    (hA : HasBoundedEverywhereInverse A) :
    Function.Surjective A := by
  intro y
  exact ⟨⟨hA.inv y, hA.inv_mapsTo_domain y⟩, hA.apply_inv y⟩

end HasBoundedEverywhereInverse

end LinearPMap
end TauCeti

end

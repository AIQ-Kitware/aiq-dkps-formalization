/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Sylvester.ClosedSylvesterEquation

/-!
# Spectral gap configurations for the unbounded Sylvester equation

The interval/exterior configuration says one block has spectrum inside a compact
interval while the other stays a fixed distance away from it.  The predicate is
symmetric in the two blocks: either orientation is allowed.

`UnboundedSylvesterGap` collects every gap configuration the `sin Θ` endpoint
needs.  Its two ordered constructors let both diagonal blocks be genuinely
unbounded; only the interval/exterior constructor requires a bounded spectral
block.
-/

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open scoped InnerProductSpace

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Interval/exterior spectral configuration for two partial maps: one block has
real spectrum inside a compact interval and the other stays a distance `δ` away
from it.  The predicate is symmetric in the two blocks.

This is the canonical form.  It needs neither a dense domain nor a closed graph —
only the two real spectra — so it is stated over `LinearPMap` and the closedness
hypotheses live with the theorems that consume the gap. -/
def linearPMap_UnboundedIntervalExteriorGap
    (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F) (β α δ : ℝ) : Prop :=
  (TauCeti.LinearPMap.realSpectrum A ⊆ Set.Icc β α ∧
    TauCeti.LinearPMap.realSpectrum B ⊆ {x | x ≤ β - δ ∨ α + δ ≤ x}) ∨
  (TauCeti.LinearPMap.realSpectrum B ⊆ Set.Icc β α ∧
    TauCeti.LinearPMap.realSpectrum A ⊆ {x | x ≤ β - δ ∨ α + δ ≤ x})

/-- All source-faithful unbounded gap configurations needed by the `sin Θ`
endpoint, over the canonical partial-map representation.  The ordered
constructors allow both diagonal blocks to be genuinely unbounded; only the
interval/exterior constructor has a bounded spectral block. -/
inductive linearPMap_UnboundedSylvesterGap
    (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F) (δ : ℝ) : Prop where
  | intervalExterior
      {β α : ℝ}
      (hβα : β ≤ α)
      (hgap : linearPMap_UnboundedIntervalExteriorGap A B β α δ)
  | leftAboveRightBelow
      (c : ℝ)
      (hA : TauCeti.LinearPMap.SemiboundedBelow A (c + δ))
      (hB : TauCeti.LinearPMap.SemiboundedAbove B c)
  | leftBelowRightAbove
      (c : ℝ)
      (hA : TauCeti.LinearPMap.SemiboundedAbove A c)
      (hB : TauCeti.LinearPMap.SemiboundedBelow B (c + δ))

/-- Interval/exterior spectral configuration for two closed self-adjoint blocks.

Compatibility facade: `ClosedOperator.realSpectrum` is itself a facade for
`TauCeti.LinearPMap.realSpectrum` at `A.toLinearPMap`, so this is *definitionally*
the canonical predicate and the two are interchangeable by `Iff.rfl`. -/
abbrev UnboundedIntervalExteriorGap
    (A : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := E))
    (B : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := F))
    (β α δ : ℝ) : Prop :=
  linearPMap_UnboundedIntervalExteriorGap A.toLinearPMap B.toLinearPMap β α δ

/-- All source-faithful unbounded gap configurations needed by the `sin Θ`
endpoint.

Compatibility facade for the canonical partial-map predicate; every component
(`realSpectrum`, `SemiboundedBelow`, `SemiboundedAbove`) is already a facade over
the `TauCeti.LinearPMap` layer, so the two spellings are definitionally equal at
`A.toLinearPMap` and `cases`/`rcases` see the canonical constructors directly. -/
abbrev UnboundedSylvesterGap
    (A : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := E))
    (B : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := F))
    (δ : ℝ) : Prop :=
  linearPMap_UnboundedSylvesterGap A.toLinearPMap B.toLinearPMap δ

namespace UnboundedSylvesterGap

/-- Facade constructor: interval/exterior configuration. -/
alias intervalExterior := linearPMap_UnboundedSylvesterGap.intervalExterior

/-- Facade constructor: left block above, right block below. -/
alias leftAboveRightBelow := linearPMap_UnboundedSylvesterGap.leftAboveRightBelow

/-- Facade constructor: left block below, right block above. -/
alias leftBelowRightAbove := linearPMap_UnboundedSylvesterGap.leftBelowRightAbove

end UnboundedSylvesterGap

end ExactSinTheta
end Experimental
end DavisKahan
end TauCeti
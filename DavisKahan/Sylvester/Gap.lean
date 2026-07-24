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

/-- Interval/exterior spectral configuration for two closed self-adjoint blocks. -/
def UnboundedIntervalExteriorGap
    (A : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := E))
    (B : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := F))
    (β α δ : ℝ) : Prop :=
  (A.realSpectrum ⊆ Set.Icc β α ∧
    B.realSpectrum ⊆ {x | x ≤ β - δ ∨ α + δ ≤ x}) ∨
  (B.realSpectrum ⊆ Set.Icc β α ∧
    A.realSpectrum ⊆ {x | x ≤ β - δ ∨ α + δ ≤ x})

/-- All source-faithful unbounded gap configurations needed by the `sin Θ`
endpoint.  The ordered constructors allow both diagonal blocks to be genuinely
unbounded; the interval/exterior constructor has a bounded spectral block. -/
inductive UnboundedSylvesterGap
    (A : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := E))
    (B : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := F))
    (δ : ℝ) : Prop where
  | intervalExterior
      {β α : ℝ}
      (hβα : β ≤ α)
      (hgap : UnboundedIntervalExteriorGap A B β α δ)
  | leftAboveRightBelow
      (c : ℝ)
      (hA : SemiboundedBelow A (c + δ))
      (hB : SemiboundedAbove B c)
  | leftBelowRightAbove
      (c : ℝ)
      (hA : SemiboundedAbove A c)
      (hB : SemiboundedBelow B (c + δ))

end ExactSinTheta
end Experimental
end DavisKahan
end TauCeti
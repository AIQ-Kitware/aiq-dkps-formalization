/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.Interop.Spectra.SpectralRestriction
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Circle Riesz projection and spectral separation by a circle

Grounded declarations promoted out of the experimental Davis--Kahan frontier.
`CircleSeparatesRealSpectrum` records that a circle in the complex plane isolates
a chosen measurable part of the real spectrum of a self-adjoint operator, while
`circleRieszProjection` is the corresponding circle-integral Riesz projection
`(2 π i)⁻¹ ∮_{|z-c|=r} (z - A)⁻¹ dz`.
-/

open scoped InnerProductSpace

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace Frontier

open SpectraBridge

universe u

section CircleRieszInterface

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A circle separates a chosen measurable subset of the real spectrum of a
self-adjoint closed operator. -/
structure CircleSeparatesRealSpectrum
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A)
    (B : Set ℝ) (center radius : ℝ) : Prop where
  radius_pos : 0 < radius
  contour_resolvent :
    ∀ z : ℂ, ‖z - (center : ℂ)‖ = radius →
      z ∉ spectrum ℂ A
  inside_iff_mem :
    ∀ x : ℝ, (x : ℂ) ∈ spectrum ℂ A →
      (‖(x : ℂ) - (center : ℂ)‖ < radius ↔ x ∈ B)

/-- Circle-integral Riesz projection for a bounded operator, through Mathlib's
circle integral: `(2 π i)⁻¹ ∮_{|z-c|=r} (z - A)⁻¹ dz`, with the resolvent
taken through the total `Ring.inverse` so the definition needs no separation
hypothesis. -/
noncomputable def circleRieszProjection
    (A : H →L[ℂ] H) (center radius : ℝ) : H →L[ℂ] H :=
  (2 * Real.pi * Complex.I)⁻¹ •
    ∮ z in C((center : ℂ), radius),
      Ring.inverse (z • (1 : H →L[ℂ] H) - A)

end CircleRieszInterface

end Frontier
end Experimental
end DavisKahan
end ForMathlib

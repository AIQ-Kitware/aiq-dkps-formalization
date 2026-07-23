/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.Experimental.Frontier.Core
import DavisKahan.Experimental.InfiniteDimensional.Core.SpectralProjection
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Circle Riesz projections for the Section 8 continuation argument

Only circles separating subsets of the real spectrum are exposed here.  This
is the minimum analytic surface required by the Davis--Kahan continuation
stack and intentionally avoids an abstract contour, rectifiability, or winding
number framework.
-/

open scoped InnerProductSpace Topology
open Set Filter

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace Frontier
namespace RieszCircle

open DavisKahanExt

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The circle resolvent integrand: the resolvent at the parametrized circle
point, weighted by the derivative of the parametrization, exactly as in
Mathlib's `circleIntegral`. -/
noncomputable def circleResolventIntegrand
    (A : H →L[ℂ] H) (center radius θ : ℝ) : H →L[ℂ] H :=
  deriv (circleMap (center : ℂ) radius) θ •
    Ring.inverse (circleMap (center : ℂ) radius θ • (1 : H →L[ℂ] H) - A)

/-- The operator-valued circle integral defining the Riesz projection. -/
noncomputable def circleRieszProjectionIntegral
    (A : H →L[ℂ] H) (center radius : ℝ) : H →L[ℂ] H :=
  (2 * Real.pi * Complex.I)⁻¹ •
    ∫ θ : ℝ in (0 : ℝ)..2 * Real.pi, circleResolventIntegrand A center radius θ

/-- The core definition in `Core` agrees with the explicit operator-valued
circle integral. -/
theorem circleRieszProjection_eq_integral
    (A : H →L[ℂ] H) (center radius : ℝ) :
    Frontier.circleRieszProjection A center radius =
      circleRieszProjectionIntegral A center radius :=
  rfl

/-- The resolvent integrand is continuous around a separating circle. -/
theorem continuous_circleResolventIntegrand
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A)
    (B : Set ℝ) (center radius : ℝ)
    (hsep : CircleSeparatesRealSpectrum A hA B center radius) :
    Continuous (circleResolventIntegrand A center radius) := by
  sorry

/-- Cauchy's formula identifies the scalar circle integral with the indicator
of being inside the circle on the real spectrum. -/
theorem scalar_circleIntegral_resolvent_indicator
    (x center radius : ℝ) (hr : 0 < radius)
    (hboundary : |x - center| ≠ radius) :
    (circleIntegral (fun z : ℂ => (z - x)⁻¹) center radius) /
        (2 * Real.pi * Complex.I) =
      if |x - center| < radius then 1 else 0 := by
  sorry

/-- The circle Riesz projection equals the genuine measurable spectral
projection selected by the inside of the circle. -/
theorem circleRieszProjection_eq_boundedSelfAdjointSpectralProjection
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A)
    (B : Set ℝ) (hB : MeasurableSet B) (center radius : ℝ)
    (hsep : CircleSeparatesRealSpectrum A hA B center radius) :
    Frontier.circleRieszProjection A center radius =
      boundedSelfAdjointSpectralProjection A hA B hB := by
  sorry

/-- Resolvent-identity norm bound for two circle Riesz projections. -/
theorem norm_circleRieszProjection_sub_le
    (A E : H →L[ℂ] H) (center radius margin : ℝ)
    (hmargin : 0 < margin)
    (hAres : ∀ z : ℂ, ‖z - (center : ℂ)‖ = radius →
      ‖Ring.inverse (z • (1 : H →L[ℂ] H) - A)‖ ≤ margin⁻¹)
    (hAEres : ∀ z : ℂ, ‖z - (center : ℂ)‖ = radius →
      ‖Ring.inverse (z • (1 : H →L[ℂ] H) - (A + E))‖ ≤ margin⁻¹) :
    ‖Frontier.circleRieszProjection (A + E) center radius -
        Frontier.circleRieszProjection A center radius‖ ≤
      radius * ‖E‖ / margin ^ 2 := by
  sorry

/-- Norm continuity of the selected projection along a bounded affine
self-adjoint path. -/
theorem continuous_circleRieszProjection_path
    (A E : H →L[ℂ] H) (center radius : ℝ)
    (hres : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ z : ℂ, ‖z - (center : ℂ)‖ = radius →
        IsUnit (z • (1 : H →L[ℂ] H) - (A + t • E))) :
    ContinuousOn
      (fun t : ℝ => Frontier.circleRieszProjection (A + t • E) center radius)
      (Set.Icc 0 1) := by
  sorry

end RieszCircle
end Frontier
end Experimental
end DavisKahan
end ForMathlib

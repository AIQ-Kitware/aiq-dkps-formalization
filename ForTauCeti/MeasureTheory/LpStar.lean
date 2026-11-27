/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5, GPT-5.6 Sol
-/
module

public import TauCeti.MeasureTheory.Function.Lp.Star

/-!
# Norm of pointwise star on `Lᵖ`

Pointwise star preserves the `Lᵖ` norm at every exponent. TauCeti uses this
identity for the normed star group instance at `1 ≤ p`.

The original complex `L²` identity came from
`DavisKahan/SpectralTheory/Real/RealCyclicDecomposition.lean`.
-/

public section

open MeasureTheory

namespace TauCeti

variable {α R : Type*} [MeasurableSpace α]
variable [NormedAddCommGroup R] [StarAddMonoid R] [NormedStarGroup R]
variable {μ : Measure α} {p : ENNReal}

/-- Pointwise star preserves the `Lᵖ` norm for every exponent. -/
theorem norm_star_lp (F : Lp R p μ) : ‖star F‖ = ‖F‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (Lp.coeFn_star F), eLpNorm_star]

end TauCeti

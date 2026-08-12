/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.SpectralTheory.ClosedOperator.Basic

/-!
# Complex closed operators

The complex scalar field is the setting for the Cayley transform and for the
vendored Spectra calculus, so it gets its own abbreviation.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

universe v

variable {H : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Local shorthand for a complex closed operator on `H`. -/
abbrev ComplexClosedOperatorH :=
  TauCeti.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := H)

end ExactSinTheta
end DavisKahan
end TauCeti
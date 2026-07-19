/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.Core.Unbounded
import Spectra.Resolvent.Spectrum

/-!
# Closed-operator real spectrum and the Spectra spectrum

The low-level closed-operator API defines the real resolvent without importing
Spectra, so it remains available over every `RCLike` scalar field.  This file
identifies its complex specialization with the real spectrum used by Spectra.
The bridge is intentionally kept above both foundations to avoid an import
cycle.
-/

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta
namespace SpectraBridge

open scoped InnerProductSpace

universe v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Membership in the closed-operator real resolvent is exactly membership of
the real scalar in the Spectra resolvent. -/
theorem mem_realResolventSet_iff_mem_spectraResolvent
    (A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := E))
    (lam : ℝ) :
    lam ∈ A.realResolventSet ↔
      (lam : ℂ) ∈ Spectra.Resolvent.resolventSet A.toLinearPMap := by
  rfl

/-- The generic closed-operator real spectrum agrees with the genuine Spectra
spectrum after specializing the scalar field to `ℂ`. -/
theorem realSpectrum_eq_spectraSpectrum
    (A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := E)) :
    A.realSpectrum = Spectra.Resolvent.spectrum A.toLinearPMap := by
  ext lam
  rfl

end SpectraBridge
end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib

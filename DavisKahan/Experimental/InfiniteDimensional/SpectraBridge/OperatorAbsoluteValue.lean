/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import Spectra.QuantumMechanics.Channels.PolarDecomp

/-!
# Spectra-backed bounded operator absolute value and polar factor

This module exposes Spectra's proof-complete bounded complex polar
decomposition under bridge-specific names. It is independent of Spectra's
Stone and spectral-PVM construction and therefore provides an immediately
usable alternate route for the Davis--Kahan operator-angle and direct-rotation
programs.
-/

open scoped InnerProductSpace

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace SpectraBridge

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Spectra's bounded operator modulus, kept under a bridge-specific name until
it is compared with the independent DKPS construction. -/
noncomputable def spectraOperatorAbsoluteValue (T : H →L[ℂ] H) : H →L[ℂ] H :=
  Spectra.QuantumMechanics.Channels.absOp T

/-- The Spectra-backed modulus is positive. -/
theorem spectraOperatorAbsoluteValue_nonneg (T : H →L[ℂ] H) :
    0 ≤ spectraOperatorAbsoluteValue T :=
  Spectra.QuantumMechanics.Channels.absOp_nonneg T

/-- The Spectra-backed modulus is self-adjoint. -/
theorem spectraOperatorAbsoluteValue_isSelfAdjoint (T : H →L[ℂ] H) :
    IsSelfAdjoint (spectraOperatorAbsoluteValue T) :=
  Spectra.QuantumMechanics.Channels.absOp_isSelfAdjoint T

/-- Squaring the modulus gives `T⋆T`. -/
theorem spectraOperatorAbsoluteValue_mul_self (T : H →L[ℂ] H) :
    spectraOperatorAbsoluteValue T * spectraOperatorAbsoluteValue T =
      star T * T :=
  Spectra.QuantumMechanics.Channels.absOp_mul_absOp T

/-- The modulus and the original operator have equal pointwise norms. -/
theorem norm_spectraOperatorAbsoluteValue_apply (T : H →L[ℂ] H) (x : H) :
    ‖spectraOperatorAbsoluteValue T x‖ = ‖T x‖ :=
  Spectra.QuantumMechanics.Channels.norm_absOp_apply T x

/-- Spectra's partial isometry in the bounded polar decomposition. -/
noncomputable def spectraPolarIsometry (T : H →L[ℂ] H) : H →L[ℂ] H :=
  Spectra.QuantumMechanics.Channels.polarIsometry T

/-- The bounded polar decomposition `T = U |T|`. -/
theorem spectraPolar_decomposition (T : H →L[ℂ] H) :
    spectraPolarIsometry T ∘L spectraOperatorAbsoluteValue T = T :=
  Spectra.QuantumMechanics.Channels.polar_decomposition T

end SpectraBridge
end Experimental
end DavisKahan
end ForMathlib

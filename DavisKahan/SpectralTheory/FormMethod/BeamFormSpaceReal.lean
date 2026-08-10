/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Sol
-/

import DavisKahan.SpectralTheory.FormMethod.BeamFormSpaceScalar

/-!
# The real free-beam form model

This file is the explicit real-scalar instantiation of the scalar-generic concrete free-beam
form construction.  Davis--Kahan Section 9 uses the real Hilbert space `L²(0,1)`, so these
names provide the source-facing real model without duplicating the analytic proof.
-/

open scoped InnerProductSpace ENNReal
open MeasureTheory TauCeti

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace MathAhead
namespace HiddenFoundations
namespace FreeBeam
namespace Model
namespace Real

noncomputable section

abbrev BeamL2 : Type := Scalar.BeamL2 (𝕜 := ℝ)
abbrev BeamPairSpace : Type := Scalar.BeamPairSpace (𝕜 := ℝ)
abbrev BeamV : Type := Scalar.BeamV (𝕜 := ℝ)

abbrev beamEmbed : BeamV →L[ℝ] BeamL2 := Scalar.beamEmbed (𝕜 := ℝ)
abbrev beamSnd : BeamV →L[ℝ] BeamL2 := Scalar.beamSnd (𝕜 := ℝ)

abbrev beamCoerciveFormData := Scalar.beamCoerciveFormData (𝕜 := ℝ)
abbrev beamShiftedFormData := Scalar.beamShiftedFormData (𝕜 := ℝ)

/-- The real `L²(0,1]` free-beam operator represented by the shifted bending form. -/
abbrev beamOperator : DavisKahanExt.ClosedOperator (𝕜 := ℝ) (E := BeamL2) :=
  Scalar.beamOperator (𝕜 := ℝ)

/-- The real free-beam realization is self-adjoint. -/
theorem beamOperator_isSelfAdjoint : beamOperator.IsSelfAdjoint :=
  Scalar.beamOperator_isSelfAdjoint (𝕜 := ℝ)

/-- The real free-beam realization is nonnegative. -/
theorem beamOperator_nonneg (x : beamOperator.domain) :
    0 ≤ RCLike.re ⟪beamOperator.toLinearMap x, (x : BeamL2)⟫_ℝ :=
  Scalar.beamOperator_nonneg (𝕜 := ℝ) x

/-- The real form-domain embedding is compact. -/
theorem isCompactOperator_beamEmbed : IsCompactOperator beamEmbed :=
  Scalar.isCompactOperator_beamEmbed (𝕜 := ℝ)

end

end Real
end Model
end FreeBeam
end HiddenFoundations
end MathAhead
end Experimental
end DavisKahan
end TauCeti

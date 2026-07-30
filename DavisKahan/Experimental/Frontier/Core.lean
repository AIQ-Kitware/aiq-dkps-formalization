/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.Geometry.Halmos.TwoProjections
import DavisKahan.SpectralTheory.SpectralRestriction
-- supplies `compressOperator`
import DavisKahan.Sylvester.GenuineSpectrum
import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.Basic
import Mathlib.MeasureTheory.Integral.CircleIntegral
-- grounded Section-3 predicates promoted out of the experimental frontier;
-- re-exported here so Core's remaining declarations keep seeing their names
import DavisKahan.Geometry.Halmos.GenericRotationPredicates
-- grounded relational/projection declarations promoted out of this stub;
-- re-exported here so Core's importers keep seeing their names
import DavisKahan.Geometry.Halmos.UnitaryEquivalence
import DavisKahan.SpectralTheory.CircleRieszProjection

/-!
# Experimental frontier interfaces for the remaining Davis--Kahan 1970 proof

This module isolates reusable signatures needed by several uncompleted source
results.  The declarations deliberately live under `Experimental.Frontier` and
are not imported by the supported library target.

The purpose is to make the remaining dependency graph explicit.  Each
interface is intended to be replaced by a concrete construction or theorem,
not treated as a permanent hypothesis in the source-facing API.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace Frontier


universe u v

section CrossSpaceClassification

variable {H₁ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [CompleteSpace H₁]
variable {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
  [CompleteSpace H₂]

/-- Abstract equality of spectral multiplicity data.  A concrete definition
must encode the measure class and the cardinal-valued multiplicity function,
not merely point-spectrum multiplicities. -/
noncomputable def SameSpectralMultiplicity
    (A : H₁ →L[ℂ] H₁) (B : H₂ →L[ℂ] H₂) : Prop := by
  sorry

/-- Spectral multiplicity data classify self-adjoint bounded operators up to
unitary equivalence.  This is the missing spectral-theorem bridge in the
paper's formulation of Theorem 3.1. -/
theorem sameSpectralMultiplicity_iff_unitarilyEquivalent
    (A : H₁ →L[ℂ] H₁) (B : H₂ →L[ℂ] H₂)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    SameSpectralMultiplicity A B ↔
      BoundedOperatorsUnitaryEquivalent A B := by
  sorry

end CrossSpaceClassification

end Frontier
end Experimental
end DavisKahan
end TauCeti
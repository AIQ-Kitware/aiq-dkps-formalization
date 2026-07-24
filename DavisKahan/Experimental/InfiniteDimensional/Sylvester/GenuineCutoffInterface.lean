/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Sylvester.CutoffInterface
import DavisKahan.Experimental.InfiniteDimensional.Core.UnboundedSpectral

/-!
# Legacy implementations of the cutoff interfaces

The interfaces live in `DavisKahan.Sylvester.CutoffInterface`.  The two
implementations below are assembled from the legacy generic spectral truncation
API, whose declarations are still open obligations.  The production
implementation comes from the vendored Spectra calculus instead.
-/

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open scoped InnerProductSpace Topology
open Filter


universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- Package the current cutoff declarations behind the coherent interface. -/
noncomputable def legacySpectralCutoffInterface
    (A : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) :
    GenuineSpectralCutoffInterface A hA where
  cutoff := spectralCutoff A hA
  isOrthogonalProjection := spectralCutoff_isOrthogonalProjection A hA
  range_le_domain := spectralCutoff_range_le_domain A hA
  commutes_on_domain := spectralCutoff_commutes_on_domain A hA
  tendsto_identity := spectralCutoff_tendsto_identity A hA

/-- Package the current bounded truncation declarations behind the coherent
interface. -/
noncomputable def legacyBoundedTruncationInterface
    (A : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) :
    GenuineBoundedTruncationInterface A hA
      (legacySpectralCutoffInterface A hA) where
  truncation := boundedSpectralTruncation A hA
  isSymmetric := boundedSpectralTruncation_isSymmetric A hA
  eq_on_cutoff := boundedSpectralTruncation_eq_on_cutoff A hA
  tendsto_on_domain := boundedSpectralTruncation_tendsto_on_domain A hA
  lowerBound := by
    intro c hLower τ hτ x
    exact boundedSpectralTruncation_lowerBound A hA hLower hτ x
  upperBound := by
    intro c hUpper τ hτ x
    exact boundedSpectralTruncation_upperBound A hA hUpper hτ x
  commutes_cutoff := boundedSpectralTruncation_commutes_cutoff A hA

end ExactSinTheta
end Experimental
end DavisKahan
end TauCeti
/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import DavisKahan.SpectralTheory.Compatibility
import DavisKahan.Experimental.InfiniteDimensional.Core.AbstractSpectrum
import DavisKahan.FiniteDimensional.Core.AngleGeometry

/-!
# Compatibility re-export that still reaches an open obligation

Every other re-export in `DavisKahan.SpectralTheory.Compatibility` names a
proved declaration.  This one names the provisional double-angle residual map,
which is still unresolved, so it is kept here rather than in the production
shim.
-/

namespace ForMathlib
namespace DavisKahanExt

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Infinite-dimensional double-angle residual embedding.  Open obligation:
the provisional construction `Foundation.sinTwoThetaEmbedding` was never
written.  It should be built from the sine and cosine blocks so that
`sinTwoThetaEmbedding_eq_rangeAngle` below holds by definition. -/
noncomputable def sinTwoThetaEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (_X : F →L[𝕜] E) : E →ₗ[𝕜] E :=
  sorry

/-- The double-angle embedding is the double-angle sine operator of the trial
range.  Open obligation, pending the construction above. -/
theorem sinTwoThetaEmbedding_eq_rangeAngle (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →L[𝕜] E)
    (_hX : DavisKahan.IsometricEmbedding X)
    [(LinearMap.range X.toLinearMap).HasOrthogonalProjection] :
    sinTwoThetaEmbedding U X =
      DavisKahanTheory.sinTwoAngleOperator U (LinearMap.range X.toLinearMap) :=
  sorry

end DavisKahanExt
end ForMathlib

/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import DavisKahan.SpectralTheory.Compatibility
import DavisKahan.Experimental.InfiniteDimensional.Core.AbstractSpectrum

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

noncomputable abbrev sinTwoThetaEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →L[𝕜] E) :=
  DavisKahan.Experimental.Foundation.sinTwoThetaEmbedding U X

end DavisKahanExt
end ForMathlib

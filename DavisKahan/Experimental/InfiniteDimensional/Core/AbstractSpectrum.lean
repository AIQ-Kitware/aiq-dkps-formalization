/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import DavisKahan.SpectralTheory.AbstractSpectrum

/-!
# Open obligation of the abstract spectrum layer

The proved part of this development now lives in
`DavisKahan.SpectralTheory.AbstractSpectrum`.  Only the provisional
double-angle residual map remains unresolved, and it stays here so the
admission closure is confined to the Experimental tree.
-/

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace Foundation

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Provisional double-angle residual map for an isometric embedding.

Construction route: write `S = P_{Uᗮ} X` for the sine block and
`C = sqrt (X⋆ P_U X)` for the positive cosine block on the coordinate space,
and set the map to `2 S C`; in principal coordinates its singular values are
`sin (2 θ_i)`.  The required square root is a positive-operator square root of
`X⋆ P_U X : F →L[𝕜] F` valid for `RCLike` scalars in infinite dimension.  The
pinned Mathlib registers the continuous-functional-calculus instances on
`F →L[𝕜] F` only for `𝕜 = ℂ` (`CFC.sqrt`), and the local
`LinearMap.IsPositive.sqrt` is finite-dimensional, so no such square root is
available yet; the definition remains open pending that bridge (or a
complexification transport).  The eventual definition should reuse the
supported projection-block API rather than introduce an independent angle
calculus, and should come with the identity
`C ∘L C = X⋆ ∘L P_U ∘L X` from positivity of the compressed projection. -/
noncomputable def sinTwoThetaEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →L[𝕜] E) : F →L[𝕜] E := by
  classical
  let cosineGram : F →L[𝕜] F :=
    X.adjoint ∘L projection U ∘L X
  let cosineBlock : F →L[𝕜] F :=
    RCLikeContinuousFunctionalCalculus.sqrt cosineGram
  exact (2 : 𝕜) •
    (complementaryProjection U ∘L X ∘L cosineBlock)

end Foundation
end Experimental
end DavisKahan
end ForMathlib

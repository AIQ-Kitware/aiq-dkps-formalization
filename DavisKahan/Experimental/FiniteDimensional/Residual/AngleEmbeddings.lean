/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import DavisKahan.FiniteDimensional.Residual.AngleEmbedding

/-!
# Compatibility surface for unfinished coordinate angle maps

The proved compression, residual, and sine-embedding API moved to
`DavisKahan.FiniteDimensional.Residual.AngleEmbedding`.

For an isometric trial map `X : F → E`, the cosine and sine blocks are
`P_U X` and `P_{Uᗮ} X`.  The tangent is the sine block composed with the
Moore--Penrose inverse of the cosine block; that inverse is not yet available
in this development or the pinned Mathlib, so the tangent maps below remain
open constructions.  Two intended theorems are recorded here rather than
stated because their statements require the missing transverse-embedding
predicate and the simultaneous (CS) singular value decomposition of the
cosine/sine blocks:

* `singularValues_tanThetaEmbedding`: under transversality, the singular
  values of the trial-coordinate tangent are the tangents of the principal
  angles between `U` and the trial range.
* `singularValues_tanTwoThetaEmbedding`: under quarter-turn avoidance, the
  singular values of the totalized double-angle tangent are
  `|tan (2 θ_i)|`.
-/

namespace ForMathlib
namespace DavisKahanTheory

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-! Construction route: build the two remaining coordinate maps from the
cosine/sine blocks.  Under transversality, invert `cosThetaEmbedding` on its
range and define tangent as sine after that inverse (equivalently, compose
with the Moore--Penrose inverse once it exists).  Define double-angle tangent
only after quarter-turn avoidance makes the corresponding cosine block
invertible.  Each definition should come with a singular-value identification
before it is used in a norm theorem. -/

/-- Tangent map in approximate coordinates. -/
noncomputable def tanThetaEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) : F →ₗ[𝕜] E :=
  sinThetaEmbedding U X ∘ₗ
    FiniteDimensional.moorePenroseInverse (cosThetaEmbedding U X)

/-- Double-angle sine block `2 S C⋆`, written in trial coordinates. -/
noncomputable def sinTwoThetaEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) : F →ₗ[𝕜] E :=
  (2 : 𝕜) •
    (sinThetaEmbedding U X ∘ₗ
      LinearMap.adjoint (cosThetaEmbedding U X)) ∘ₗ X.toLinearMap

/-- Double-angle tangent map in approximate coordinates. -/
noncomputable def tanTwoThetaEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) : F →ₗ[𝕜] E :=
  sinTwoThetaEmbedding U X ∘ₗ
    FiniteDimensional.moorePenroseInverse
      (FiniteDimensional.cosTwoThetaEmbedding U X)

end DavisKahanTheory
end ForMathlib

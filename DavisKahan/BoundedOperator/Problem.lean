/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.Projection.Gap
public import TauCeti.Analysis.InnerProductSpace.Sylvester.Basic

/-!
# Bounded invariant-pair problems

The sine block belongs to an approximate invariant pair. The residual is
`A.sylvester M X`. Projection, reducing-subspace, symmetry, and norm estimates
use the canonical `Submodule` and `ContinuousLinearMap` APIs.
-/

public section

namespace TauCeti
namespace DavisKahan

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Uniform acuteness bounds the projection gap strictly below one. In infinite
 dimension it is stronger than vanishing crossed intersections, which permits
 angles tending to a right angle. -/
@[expose]
def IsUniformlyAcute (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : Prop :=
  U.projectionGap V < 1

/-- The projection gap lies below the quarter-angle threshold. -/
@[expose]
def IsQuarterAcute (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : Prop :=
  U.projectionGap V < Real.sqrt 2 / 2

/-- An isometric bounded embedding. -/
@[expose]
def IsometricEmbedding (X : F →L[𝕜] E) : Prop := ∀ x, ‖X x‖ = ‖x‖

/-- Directed sine block for an approximate subspace embedding. -/
@[expose]
noncomputable def sinThetaEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →L[𝕜] E) : F →L[𝕜] E :=
  Uᗮ.starProjection ∘L X

end DavisKahan
end TauCeti

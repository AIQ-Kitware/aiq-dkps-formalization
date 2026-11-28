/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import DavisKahan.Geometry.Angle.OperatorAngleComplex
public import DavisKahan.Geometry.Angle.OperatorAngleReal
public import DavisKahan.Geometry.Angle.AngleFunctionalCalculus
public import ForTauCeti.Analysis.InnerProductSpace.Projection.Gap
public import TauCeti.Analysis.InnerProductSpace.Projection.SinTheta
public import ForTauCeti.Analysis.InnerProductSpace.Projection.Blocks
public import DavisKahan.BoundedOperator.Problem

public section

open TauCeti.DavisKahan.Angle


/-!
# Maximal angle from the projection gap

The scalar maximal angle is defined over real and complex inner product spaces.
The imported complex and real-complexified modules construct the operator angles.
-/

namespace TauCeti
namespace DavisKahanExt

open DavisKahan

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- Maximal angle represented by the projection gap.  This scalar definition
is valid over every `RCLike` field and needs no operator functional calculus. -/
@[expose]
noncomputable def maximalAngle (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : ℝ :=
  Real.arcsin (U.projectionGap V)

end DavisKahanExt
end TauCeti

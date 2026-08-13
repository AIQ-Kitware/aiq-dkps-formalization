/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/

import DavisKahan.Geometry.Polar.Section3Nonacute

/-!
# Davis--Kahan 1970, Proposition 3.2 crossing-space quarter turns

The proof of Proposition 3.2 records a property of every direct rotation on
the two crossed defect spaces: applying the rotation twice gives minus the
original vector.  This file exposes that established source claim directly.
-/

namespace TauCeti
namespace DavisKahan1970

open scoped InnerProductSpace
open TauCeti.DavisKahan

noncomputable section

universe u

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]
variable [Algebra ℝ (H →L[𝕜] H)] [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)]
  [ContinuousFunctionalCalculus ℝ (H →L[𝕜] H) IsSelfAdjoint]
variable (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection]
  [V.HasOrthogonalProjection]

/-- **Davis--Kahan 1970, Proposition 3.2, crossing-space property.**
Every paper direct rotation squares to minus the identity on each of the two
crossed defect spaces.  No acuteness or finite-dimensional hypothesis is
added. -/
theorem proposition3_2_crossing_square_minus_one
    (T : H →L[𝕜] H) (hT : TauCeti.DavisKahan.Frontier.IsPaperDirectRotation U V T) :
    (∀ x : halmosSourceDefect U V, T (T (x : H)) = -(x : H)) ∧
      (∀ y : halmosTargetDefect U V, T (T (y : H)) = -(y : H)) := by
  constructor
  · intro x
    exact TauCeti.DavisKahan.paperDirectRotation_sq_apply_sourceDefect U V T hT x.property
  · intro y
    exact TauCeti.DavisKahan.paperDirectRotation_sq_apply_targetDefect U V T hT y.property

end

end DavisKahan1970
end TauCeti

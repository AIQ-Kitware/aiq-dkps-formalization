/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
import DavisKahan.Experimental.InfiniteDimensional.Core.Compatibility
import ForMathlib.Analysis.InnerProductSpace.OperatorAbsoluteValue

/-!
# The complex operator angle calculus: honest first rungs

The scalar-generic ladder in `Core/OperatorAngle.lean` is blocked on an
`RCLike`-generic positive operator square root.  Per the route decision
recorded in `docs/planning/davis-kahan-full-paper-goal.md`, this module
specializes to `ℂ`, where the continuous-functional-calculus square root is
available (`ForMathlib/Analysis/InnerProductSpace/OperatorAbsoluteValue.lean`),
with a real-scalar bridge by complexification expected later.

* `sinAngleOperatorC U V = |P_U - P_V|`: the sine of the operator angle as
  the absolute value of the projector difference — the definition the
  generic ladder reaches only after the Halmos decomposition.
* `norm_sinAngleOperatorC`: `‖sin Θ(U, V)‖ = subspaceGap U V`, immediate
  from the absolute-value norm identity.
* `norm_sinAngleOperatorC_apply`: the pointwise identity
  `‖sin Θ(U, V) x‖ = ‖(P_U - P_V) x‖`.
-/

namespace ForMathlib
namespace DavisKahanExt

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- Sine of the operator angle between two subspaces at complex scalars:
the absolute value of the projector difference. -/
noncomputable def sinAngleOperatorC (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[ℂ] E :=
  ForMathlib.operatorAbs (U.starProjection - V.starProjection)

/-- The sine operator is nonnegative. -/
theorem sinAngleOperatorC_nonneg (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    0 ≤ sinAngleOperatorC U V :=
  ForMathlib.operatorAbs_nonneg _

/-- The sine operator is self-adjoint. -/
theorem isSelfAdjoint_sinAngleOperatorC (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    IsSelfAdjoint (sinAngleOperatorC U V) :=
  ForMathlib.isSelfAdjoint_operatorAbs _

/-- **The norm of the sine operator is the subspace gap.** -/
theorem norm_sinAngleOperatorC (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖sinAngleOperatorC U V‖ = subspaceGap U V :=
  ForMathlib.norm_operatorAbs _

/-- Pointwise identity: the sine operator is a pointwise isometry of the
projector difference. -/
theorem norm_sinAngleOperatorC_apply (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (x : E) :
    ‖sinAngleOperatorC U V x‖ =
      ‖(U.starProjection - V.starProjection) x‖ :=
  ForMathlib.norm_operatorAbs_apply _ x

end DavisKahanExt
end ForMathlib

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

open scoped InnerProductSpace

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

/-- Cosine of the directed operator angle at complex scalars: the absolute
value of the projection composition `P_V P_U`.  Its singular values are the
cosines of the principal angles of `U` against `V`. -/
noncomputable def cosAngleOperatorC (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[ℂ] E :=
  ForMathlib.operatorAbs (V.starProjection ∘L U.starProjection)

/-- The cosine operator is nonnegative. -/
theorem cosAngleOperatorC_nonneg (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    0 ≤ cosAngleOperatorC U V :=
  ForMathlib.operatorAbs_nonneg _

/-- The cosine operator is self-adjoint. -/
theorem isSelfAdjoint_cosAngleOperatorC (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    IsSelfAdjoint (cosAngleOperatorC U V) :=
  ForMathlib.isSelfAdjoint_operatorAbs _

/-- The norm of the cosine operator is the norm of the directed projection
composition — the largest principal cosine. -/
theorem norm_cosAngleOperatorC (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖cosAngleOperatorC U V‖ = ‖V.starProjection ∘L U.starProjection‖ :=
  ForMathlib.norm_operatorAbs _

/-- The cosine operator is a contraction. -/
theorem norm_cosAngleOperatorC_le_one (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖cosAngleOperatorC U V‖ ≤ 1 := by
  rw [norm_cosAngleOperatorC]
  calc ‖V.starProjection ∘L U.starProjection‖
      ≤ ‖V.starProjection‖ * ‖U.starProjection‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 :=
        mul_le_mul V.starProjection_norm_le U.starProjection_norm_le
          (norm_nonneg _) zero_le_one
    _ = 1 := by ring

/-- **Pointwise Pythagoras for the directed sine and cosine.**  On vectors
of `U`, the squared norms of the directed sine (`P_{Vᗮ} x`) and cosine
(`P_V x`) data add to `‖x‖²` — the operator-level `sin² + cos² = 1` on the
source subspace. -/
theorem sq_norm_sin_add_sq_norm_cos (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {x : E} (hx : x ∈ U) :
    ‖(Vᗮ.starProjection ∘L U.starProjection) x‖ ^ 2 +
      ‖(V.starProjection ∘L U.starProjection) x‖ ^ 2 = ‖x‖ ^ 2 := by
  have hP : U.starProjection x = x := Submodule.starProjection_eq_self_iff.mpr hx
  have hVc : Vᗮ.starProjection x = x - V.starProjection x :=
    V.starProjection_orthogonal_apply x
  have horth : ⟪V.starProjection x, x - V.starProjection x⟫_ℂ = 0 := by
    have h1 : x - V.starProjection x ∈ Vᗮ := by
      rw [← hVc]
      exact Vᗮ.starProjection_apply_mem x
    have h2 : V.starProjection x ∈ V := V.starProjection_apply_mem x
    exact (Submodule.mem_orthogonal V _).mp h1 _ h2
  have hpyth : ‖V.starProjection x‖ ^ 2 + ‖x - V.starProjection x‖ ^ 2 =
      ‖x‖ ^ 2 := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      (V.starProjection x) (x - V.starProjection x) horth
    rw [show V.starProjection x + (x - V.starProjection x) = x from by abel]
      at h
    rw [sq, sq, sq]
    linarith
  simp only [ContinuousLinearMap.comp_apply, hP]
  rw [hVc]
  linarith

end DavisKahanExt
end ForMathlib

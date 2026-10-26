/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import TauCeti.Analysis.InnerProductSpace.InvariantSubspace
public import ForTauCeti.Analysis.InnerProductSpace.BoundedOperator.SinTheta
public import ForTauCeti.Analysis.InnerProductSpace.Projection.Gap

/-!
# Sharp projector geometry for bounded Davis--Kahan theory

The two-projection norm identity and the sharp factor-one coercive projector
theorem over arbitrary `RCLike` scalars.

## Provenance

*Moved, not restated.*  This file was
`DavisKahan/BoundedOperator/Projector.lean`
before the dependency-closed base of the sin-Θ core moved
into the staging layer.

**Renamespaced,** for the reason its sibling
`SinTheta.lean` records: the sharp projector bound is generic operator geometry
and was filed under the paper's namespace.  It now lives in `Submodule`, the
namespace of its conclusion's head symbol.

The gap geometry used here is owned by Tau Ceti's
`Submodule.projectionGap_eq_max`; the paper theorem is stated directly in terms
of the source-facing projector norm below.
-/

public section

namespace Submodule

open TauCeti
open scoped InnerProductSpace

variable {𝕜 H : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- **The sharp (factor-one) operator-norm Davis--Kahan projector theorem.**  With
a two-sided coercive spectral gap — `A`'s form `≥ (c+g)` on `U` and `≤ c` on
`Uᗮ`, `B`'s form `≥ (c+g)` on `W` and `≤ c` on `Wᗮ` — the orthogonal
projectors onto these reducing subspaces on an arbitrary `RCLike` Hilbert space
satisfy the sharp bound

`‖P_U − P_W‖ ≤ ‖B − A‖ / g`

with constant one and no equal-rank hypothesis. Combines Tau Ceti's canonical
projector-gap identity with the two dimension-free
directed `sin Θ` estimates `Submodule.sinTheta_directed_coercive`. -/
theorem opNorm_starProjection_sub_le_of_coercive
    {A B : H →L[𝕜] H} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U W : Submodule 𝕜 H} [U.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (hU : Submodule.IsReducing U A) (hW : Submodule.IsReducing W B)
    {c g : ℝ} (hg : 0 < g)
    (hUc : ∀ x ∈ U, (c + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hUlo : ∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2)
    (hWc : ∀ x ∈ W, (c + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪B x, x⟫_𝕜)
    (hWlo : ∀ x ∈ Wᗮ, RCLike.re ⟪B x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2) :
    ‖(U.starProjection - W.starProjection : H →L[𝕜] H)‖ ≤ ‖B - A‖ / g := by
  rw [← Submodule.projectionGap_def U W,
    Submodule.projectionGap_eq_max,
    Submodule.directedProjectionGap_def,
    Submodule.directedProjectionGap_def]
  refine max_le ?_ ?_
  · exact sinTheta_directed_coercive hA hB hU
      ((LinearMap.IsSymmetric.isReducing_iff_mem_invtSubmodule hB _).mpr
        hW.orthogonal_mem_invtSubmodule) hg hUc hWlo
  · have h := sinTheta_directed_coercive hB hA hW
      ((LinearMap.IsSymmetric.isReducing_iff_mem_invtSubmodule hA _).mpr
        hU.orthogonal_mem_invtSubmodule) hg hWc hUlo
    rwa [show ‖A - B‖ = ‖B - A‖ from by rw [← neg_sub, norm_neg]] at h


/-- Sharp projector bound stated with reusable subspace form-bound predicates. -/
theorem opNorm_starProjection_sub_le_of_formBounds
    {A B : H →L[𝕜] H} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U W : Submodule 𝕜 H} [U.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (hU : Submodule.IsReducing U A) (hW : Submodule.IsReducing W B)
    {c g : ℝ} (hg : 0 < g)
    (hUhi : A.LowerFormBoundOn U (c + g))
    (hUlo : A.UpperFormBoundOn Uᗮ c)
    (hWhi : B.LowerFormBoundOn W (c + g))
    (hWlo : B.UpperFormBoundOn Wᗮ c) :
    ‖(U.starProjection - W.starProjection : H →L[𝕜] H)‖ ≤ ‖B - A‖ / g :=
  opNorm_starProjection_sub_le_of_coercive hA hB hU hW hg
    ((_root_.ContinuousLinearMap.lowerFormBoundOn_iff A U (c + g)).1 hUhi)
    ((_root_.ContinuousLinearMap.upperFormBoundOn_iff A Uᗮ c).1 hUlo)
    ((_root_.ContinuousLinearMap.lowerFormBoundOn_iff B W (c + g)).1 hWhi)
    ((_root_.ContinuousLinearMap.upperFormBoundOn_iff B Wᗮ c).1 hWlo)


end Submodule

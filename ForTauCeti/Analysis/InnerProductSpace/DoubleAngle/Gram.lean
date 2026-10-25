/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.AngleGeometry
public import TauCeti.Analysis.InnerProductSpace.DoubleAngle.Gram
import Mathlib.Tactic.Module

/-!
# The ambient double-angle Gram identity

The rectangular Gram identities, complementary-isometry block formulas, and
scalar double-angle identities are maintained in Tau Ceti (PR #19299).
This donor retains only the ambient projector formula for the local
`TauCeti.sinTwoAngleOperator`.

## Provenance

The rectangular part of the original DKPS donor was adapted upstream in
commit `69cd1ab4dcfbb6676e344f3f193e63473eab5a3d`. Consumers use those
accepted declarations directly; no compatibility names are retained here.
-/

public section

namespace TauCeti

open scoped InnerProductSpace

section Projectors

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- **`sin 2Θ = 2 sin Θ cos Θ` for a pair of subspaces, at the Gram level.**
The Gram operator of the one-sided double-angle map `2 P_{Uᗮ} P_V P_U` is
`4 (M - M²)`, where `M` is the Gram operator of the cosine cross projection
`P_V P_U`.

Since the eigenvalues of `M` are the squared principal cosines `c²`, the squared
singular values of `sinTwoAngleOperator U V` are `4 c² (1 - c²) = sin² 2θ`.

**There is no equal-dimension hypothesis**, and none is available: `U` and `V`
are arbitrary.  This is the projector-side statement of the same fact that
the accepted reflected-block Gram identity records in isometry-block
coordinates. -/
theorem gram_sinTwoAngleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    LinearMap.adjoint (sinTwoAngleOperator U V) ∘ₗ sinTwoAngleOperator U V =
      (4 : 𝕜) • ((LinearMap.adjoint (cosThetaMap U V) ∘ₗ cosThetaMap U V) -
        (LinearMap.adjoint (cosThetaMap U V) ∘ₗ cosThetaMap U V) ∘ₗ
          (LinearMap.adjoint (cosThetaMap U V) ∘ₗ cosThetaMap U V)) := by
  have hidem : ∀ (W : Submodule 𝕜 E) [W.HasOrthogonalProjection] (x : E),
      projection W (projection W x) = projection W x := by
    intro W _ x
    exact Submodule.starProjection_eq_self_iff.mpr (W.starProjection_apply_mem x)
  have hcomp : ∀ (W : Submodule 𝕜 E) [W.HasOrthogonalProjection] (x : E),
      complementaryProjection W x = x - projection W x := by
    intro W _ x
    rw [complementaryProjection, projection, projection,
      Submodule.starProjection_orthogonal]
    simp
  have hadjCos : LinearMap.adjoint (cosThetaMap U V) =
      projection U ∘ₗ projection V := by
    rw [cosThetaMap, LinearMap.adjoint_comp, projection_adjoint, projection_adjoint]
  have hadjSin : LinearMap.adjoint (sinTwoAngleOperator U V) =
      (2 : 𝕜) • (projection U ∘ₗ projection V ∘ₗ complementaryProjection U) := by
    rw [sinTwoAngleOperator_eq_two_smul_cross, map_smulₛₗ, map_ofNat,
      LinearMap.adjoint_comp, LinearMap.adjoint_comp, complementaryProjection,
      projection_adjoint, projection_adjoint, projection_adjoint]
    rfl
  rw [hadjSin, hadjCos, sinTwoAngleOperator_eq_two_smul_cross]
  ext x
  simp only [cosThetaMap, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.sub_apply, map_smul, hcomp, map_sub, hidem]
  module

end Projectors

end TauCeti

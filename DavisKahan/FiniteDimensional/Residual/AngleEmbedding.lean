/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import DavisKahan.FiniteDimensional.Core.AngleGeometry
import DavisKahan.FiniteDimensional.Residual.TrialMap

/-!
# Principal-angle embeddings for trial subspaces

Coordinate-space sine and cosine embeddings, their projected residual identity,
and the singular-value dictionary relating them to directed principal angles.
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
/-- Sine map from approximate coordinates into the orthogonal complement of
an exact subspace. -/
noncomputable def sinThetaEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) : F →ₗ[𝕜] E :=
  complementaryProjection U ∘ₗ X.toLinearMap

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
@[simp] theorem complementaryTrialBlock_toLinearMap (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) :
    complementaryTrialBlock U X.toLinearMap = sinThetaEmbedding U X :=
  rfl

/-- Cosine map from approximate coordinates into an exact subspace. -/
noncomputable def cosThetaEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) : F →ₗ[𝕜] E :=
  projection U ∘ₗ X.toLinearMap

/-- Provisional double-angle cosine block in trial coordinates.

Angle semantics are open: this body is **not** the trial-coordinate `cos 2Θ`
map and must not be used to prove a singular-value identification.  The blocks
`C = cosThetaEmbedding` and `S = sinThetaEmbedding` go `F →ₗ E`, so it is the
*source-side* Gram blocks that carry the principal angles: `C⋆C` and `S⋆S` act
on `F` with eigenvalues `cos²θᵢ` and `sin²θᵢ`.  The correct trial-coordinate
double-angle cosine is therefore built from

  `C⋆C - S⋆S`   (eigenvalues `cos 2θᵢ`),

optionally embedded into `E` by `X`.  The ambient combination `C C⋆ - S S⋆`
used below pads with zeros on the orthogonal complement of `range X`, and
postcomposing that with `X` does not recover the source-side map.

Retained only so that the guarded double-angle signatures elaborate; see the
companion note on `sinTwoThetaEmbedding`. -/
noncomputable def cosTwoThetaEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) : F →ₗ[𝕜] E :=
  (cosThetaEmbedding U X ∘ₗ LinearMap.adjoint (cosThetaEmbedding U X) -
      sinThetaEmbedding U X ∘ₗ LinearMap.adjoint (sinThetaEmbedding U X)) ∘ₗ
    X.toLinearMap

/-- No principal angle between `U` and `range X` is `π/4`. -/
def AvoidsQuarterTurnEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) : Prop :=
  AvoidsQuarterTurn U (approximateSubspace X)

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
/-- **The projected-residual (cross-block) Sylvester identity for an isometric
trial map.**  This is the normalized specialization of
`sylvester_complementaryTrialBlock_eq_projectedGeneralResidual`. -/
theorem sylvester_sinThetaEmbedding_eq_projectedResidual
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : Reduces A U)
    (X : F →ₗᵢ[𝕜] E) (M : F →ₗ[𝕜] F) :
    A ∘ₗ sinThetaEmbedding U X - sinThetaEmbedding U X ∘ₗ M =
      complementaryProjection U ∘ₗ residual A X M := by
  simpa only [complementaryTrialBlock_toLinearMap, generalResidual_toLinearMap] using
    sylvester_complementaryTrialBlock_eq_projectedGeneralResidual
      hA hU X.toLinearMap M

/-- The orthogonal projection onto the range of an isometric embedding is
`X X⋆`. -/
theorem projection_approximateSubspace_eq_comp_adjoint (X : F →ₗᵢ[𝕜] E) :
    projection (approximateSubspace X) =
      X.toLinearMap ∘ₗ X.toLinearMap.adjoint := by
  ext y
  change (approximateSubspace X).starProjection y =
    X.toLinearMap (X.toLinearMap.adjoint y)
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · change X.toLinearMap (X.toLinearMap.adjoint y) ∈
      LinearMap.range X.toLinearMap
    exact ⟨X.toLinearMap.adjoint y, rfl⟩
  · intro w hw
    change w ∈ LinearMap.range X.toLinearMap at hw
    rcases hw with ⟨z, rfl⟩
    rw [inner_sub_left]
    apply sub_eq_zero.mpr
    change ⟪y, X z⟫_𝕜 =
      ⟪X (X.toLinearMap.adjoint y), X z⟫_𝕜
    exact (LinearMap.adjoint_inner_left X.toLinearMap z y).symm |>.trans
      (X.inner_map_map (X.toLinearMap.adjoint y) z).symm

/-- The singular values of `sinThetaEmbedding U X = P_{Uᗮ}X` are the
principal sines directed from `range X` toward `U`.

The proof identifies the projection onto `range X` with `X X⋆`, precomposes by
`X⋆`, and uses coisometry padding to show that the ambient cross projection has
exactly the same singular-value sequence as the rectangular embedding map.
-/
theorem singularValues_sinThetaEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) :
    (sinThetaEmbedding U X).singularValues =
      principalSines (approximateSubspace X) U := by
  have hmap :
      sinThetaEmbedding U X ∘ₗ X.toLinearMap.adjoint =
        sinThetaMap (approximateSubspace X) U := by
    rw [sinThetaEmbedding, sinThetaMap,
      projection_approximateSubspace_eq_comp_adjoint X]
    simp only [LinearMap.comp_assoc]
  calc
    (sinThetaEmbedding U X).singularValues =
        (sinThetaEmbedding U X ∘ₗ X.toLinearMap.adjoint).singularValues :=
      (singularValues_comp_adjoint_linearIsometry X (sinThetaEmbedding U X)).symm
    _ = (sinThetaMap (approximateSubspace X) U).singularValues := by rw [hmap]
    _ = principalSines (approximateSubspace X) U :=
      singularValues_sinThetaMap (approximateSubspace X) U

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
/-- The tangent map is finite exactly when the represented subspace is
transverse to `U`.

Signature audit: Valid because `IsTransverse (range X) U` is the one-sided injectivity of
`P_U` on `range X`, exactly the kernel statement on the right.
-/
theorem tanThetaEmbedding_defined_iff (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) :
    IsTransverse (approximateSubspace X) U ↔
      LinearMap.ker (cosThetaEmbedding U X) = ⊥ := by
  constructor
  · intro htrans
    rw [LinearMap.ker_eq_bot]
    intro x y hxy
    have hproj : U.starProjection (X (x - y)) = 0 := by
      change cosThetaEmbedding U X (x - y) = 0
      rw [map_sub, hxy, sub_self]
    have hXzero : X (x - y) = 0 :=
      htrans (X (x - y)) ⟨x - y, rfl⟩ hproj
    have hxyzero : x - y = 0 := by
      apply X.injective
      simpa using hXzero
    exact sub_eq_zero.mp hxyzero
  · intro hker x hx hproj
    rcases hx with ⟨y, rfl⟩
    have hyker : y ∈ LinearMap.ker (cosThetaEmbedding U X) := by
      simpa [cosThetaEmbedding, projection, LinearMap.comp_apply] using hproj
    rw [hker] at hyker
    have hy : y = 0 := by simpa using hyker
    rw [hy, map_zero]


end DavisKahanTheory
end ForMathlib

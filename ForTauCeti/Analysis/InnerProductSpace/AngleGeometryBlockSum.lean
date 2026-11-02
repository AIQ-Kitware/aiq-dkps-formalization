/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Sol
-/
module

public import TauCeti.Analysis.InnerProductSpace.Projection.AngleOperator
public import TauCeti.Analysis.InnerProductSpace.FunctionalCalculusComparison

public import ForTauCeti.Analysis.InnerProductSpace.AngleGeometry
public import ForTauCeti.Analysis.InnerProductSpace.SelfAdjointFunctionalCalculus
public import ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.BlockSum

/-!
# Orthogonal block sums and finite angle functional calculus

Reusable compatibility results for orthogonal direct sums.  The projector, modulus, and finite
self-adjoint functional calculus all preserve block-diagonal decompositions, so the angle operator
of a direct sum of subspace pairs is the block sum of the two angle operators.

This is paper-independent operator geometry.  Davis--Kahan sharpness uses it to turn block-matrix
model equalities into equalities for an actual pair of direct-sum subspaces.
-/

public section

local instance {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] : CompleteSpace E :=
  FiniteDimensional.complete 𝕜 E


attribute [local instance] ContinuousLinearMap.realAlgebra ContinuousLinearMap.realIsScalarTower

namespace TauCeti

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]

private noncomputable def blockInlLinear
    {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] :
    E₁ →ₗ[𝕜] WithLp 2 (E₁ × E₂) :=
  (WithLp.linearEquiv 2 𝕜 (E₁ × E₂)).symm.toLinearMap ∘ₗ LinearMap.inl 𝕜 E₁ E₂

private noncomputable def blockInrLinear
    {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] :
    E₂ →ₗ[𝕜] WithLp 2 (E₁ × E₂) :=
  (WithLp.linearEquiv 2 𝕜 (E₁ × E₂)).symm.toLinearMap ∘ₗ LinearMap.inr 𝕜 E₁ E₂

@[simp] private theorem blockInlLinear_apply
    {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
    (x : E₁) :
    blockInlLinear (𝕜 := 𝕜) (E₂ := E₂) x = WithLp.toLp 2 (x, (0 : E₂)) := rfl

@[simp] private theorem blockInrLinear_apply
    {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
    (x : E₂) :
    blockInrLinear (𝕜 := 𝕜) (E₁ := E₁) x = WithLp.toLp 2 ((0 : E₁), x) := rfl

private theorem blockInlLinear_intertwines
    {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
    (A : E₁ →ₗ[𝕜] E₁) (B : E₂ →ₗ[𝕜] E₂) :
    blockInlLinear (𝕜 := 𝕜) (E₂ := E₂) ∘ₗ A =
      (A.prodMap B).withLpMap 2 ∘ₗ
        blockInlLinear (𝕜 := 𝕜) (E₂ := E₂) := by
  ext x
  apply WithLp.ofLp_injective 2
  simp [LinearMap.coe_withLpMap, WithLp.map, LinearMap.prodMap_apply]

private theorem blockInrLinear_intertwines
    {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
    (A : E₁ →ₗ[𝕜] E₁) (B : E₂ →ₗ[𝕜] E₂) :
    blockInrLinear (𝕜 := 𝕜) (E₁ := E₁) ∘ₗ B =
      (A.prodMap B).withLpMap 2 ∘ₗ
        blockInrLinear (𝕜 := 𝕜) (E₁ := E₁) := by
  ext x
  apply WithLp.ofLp_injective 2
  simp [LinearMap.coe_withLpMap, WithLp.map, LinearMap.prodMap_apply]

/-- **Finite self-adjoint functional calculus preserves an orthogonal block sum.** -/
theorem selfAdjointFunctionalCalculus_orthogonalBlockSum
    {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [FiniteDimensional 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] [FiniteDimensional 𝕜 E₂]
    {A : E₁ →ₗ[𝕜] E₁} (hA : A.IsSymmetric)
    {B : E₂ →ₗ[𝕜] E₂} (hB : B.IsSymmetric) (f : ℝ → ℝ) :
    let hAB := UnitarilyInvariantSeminorm.orthogonalBlockSum_isSymmetric hA hB
    LinearMap.IsSymmetric.cfc hAB f =
      ((LinearMap.IsSymmetric.cfc hA f).prodMap (LinearMap.IsSymmetric.cfc hB f)).withLpMap 2 := by
  dsimp only
  let J₁ : E₁ →ₗ[𝕜] WithLp 2 (E₁ × E₂) :=
    blockInlLinear (𝕜 := 𝕜) (E₁ := E₁) (E₂ := E₂)
  let J₂ : E₂ →ₗ[𝕜] WithLp 2 (E₁ × E₂) :=
    blockInrLinear (𝕜 := 𝕜) (E₁ := E₁) (E₂ := E₂)
  let T : WithLp 2 (E₁ × E₂) →ₗ[𝕜] WithLp 2 (E₁ × E₂) :=
    (A.prodMap B).withLpMap 2
  let hT : T.IsSymmetric :=
    UnitarilyInvariantSeminorm.orthogonalBlockSum_isSymmetric hA hB
  have hJ₁ : J₁ ∘ₗ A = T ∘ₗ J₁ := blockInlLinear_intertwines A B
  have hJ₂ : J₂ ∘ₗ B = T ∘ₗ J₂ := blockInrLinear_intertwines A B
  have hfc₁ := hA.comp_cfc_eq_cfc_comp hT hJ₁ f
  have hfc₂ := hB.comp_cfc_eq_cfc_comp hT hJ₂ f
  apply LinearMap.ext
  intro x
  have hx : x = J₁ x.ofLp.1 + J₂ x.ofLp.2 := by
    apply (WithLp.ext_iff (p := 2)).mpr
    apply Prod.ext_iff.mpr
    constructor <;> simp [J₁, J₂]
  have h₁ :
      LinearMap.IsSymmetric.cfc hT f (J₁ x.ofLp.1) =
        J₁ (LinearMap.IsSymmetric.cfc hA f x.ofLp.1) := by
    simpa only [LinearMap.comp_apply] using
      (LinearMap.congr_fun hfc₁ x.ofLp.1).symm
  have h₂ :
      LinearMap.IsSymmetric.cfc hT f (J₂ x.ofLp.2) =
        J₂ (LinearMap.IsSymmetric.cfc hB f x.ofLp.2) := by
    simpa only [LinearMap.comp_apply] using
      (LinearMap.congr_fun hfc₂ x.ofLp.2).symm
  calc
    LinearMap.IsSymmetric.cfc hT f x
        = LinearMap.IsSymmetric.cfc hT f (J₁ x.ofLp.1 + J₂ x.ofLp.2) := by rw [← hx]
    _ = LinearMap.IsSymmetric.cfc hT f (J₁ x.ofLp.1) +
          LinearMap.IsSymmetric.cfc hT f (J₂ x.ofLp.2) := map_add _ _ _
    _ = J₁ (LinearMap.IsSymmetric.cfc hA f x.ofLp.1) +
          J₂ (LinearMap.IsSymmetric.cfc hB f x.ofLp.2) := by rw [h₁, h₂]
    _ = ((LinearMap.IsSymmetric.cfc hA f).prodMap
      (LinearMap.IsSymmetric.cfc hB f)).withLpMap 2 x := by
        apply WithLp.ofLp_injective 2
        simp [J₁, J₂, LinearMap.coe_withLpMap, WithLp.map, LinearMap.prodMap_apply,
          WithLp.ofLp_fst, WithLp.ofLp_snd]

/-- The projector onto an orthogonal block sum of subspaces is the block sum of the
projectors, in the canonical `projection` spelling used by finite angle geometry. -/
theorem projection_orthogonalBlockSumSubmodule
    {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [FiniteDimensional 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] [FiniteDimensional 𝕜 E₂]
    (U₁ : Submodule 𝕜 E₁) (U₂ : Submodule 𝕜 E₂) :
    projection
        (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule U₁ U₂) =
      ((projection U₁).prodMap (projection U₂)).withLpMap 2 :=
  UnitarilyInvariantSeminorm.starProjection_orthogonalBlockSumSubmodule U₁ U₂

/-- **The sine-angle operator of an orthogonal sum of subspace pairs is block-diagonal.** -/
theorem sinAngleOperator_orthogonalBlockSumSubmodule
    {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [FiniteDimensional 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] [FiniteDimensional 𝕜 E₂]
    (U₁ V₁ : Submodule 𝕜 E₁) (U₂ V₂ : Submodule 𝕜 E₂) :
    (Submodule.sinAngleOperator
      (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule U₁ U₂)
      (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule V₁ V₂)).toLinearMap =
      (((Submodule.sinAngleOperator U₁ V₁).toLinearMap).prodMap
        ((Submodule.sinAngleOperator U₂ V₂).toLinearMap)).withLpMap 2 := by
  have h₁ : (Submodule.sinAngleOperator U₁ V₁).toLinearMap =
      (projection U₁ - projection V₁).operatorAbs := by
    symm
    apply (LinearMap.toContinuousLinearMap_eq_iff_eq_toLinearMap _ _).mp
    rw [LinearMap.toContinuousLinearMap_operatorAbs_eq_modulus, Submodule.sinAngleOperator_def]
    congr 1
  have h₂ : (Submodule.sinAngleOperator U₂ V₂).toLinearMap =
      (projection U₂ - projection V₂).operatorAbs := by
    symm
    apply (LinearMap.toContinuousLinearMap_eq_iff_eq_toLinearMap _ _).mp
    rw [LinearMap.toContinuousLinearMap_operatorAbs_eq_modulus, Submodule.sinAngleOperator_def]
    congr 1
  have h₃ : (Submodule.sinAngleOperator
      (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule U₁ U₂)
      (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule V₁ V₂)).toLinearMap =
      (projection (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule U₁ U₂) -
        projection (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule V₁ V₂)).operatorAbs := by
    symm
    apply (LinearMap.toContinuousLinearMap_eq_iff_eq_toLinearMap _ _).mp
    rw [LinearMap.toContinuousLinearMap_operatorAbs_eq_modulus, Submodule.sinAngleOperator_def]
    congr 1
  rw [h₃, h₁, h₂,
    projection_orthogonalBlockSumSubmodule U₁ U₂,
    projection_orthogonalBlockSumSubmodule V₁ V₂]
  change (((projection U₁ - projection V₁).prodMap
    (projection U₂ - projection V₂)).withLpMap 2).operatorAbs = _
  exact UnitarilyInvariantSeminorm.operatorAbs_orthogonalBlockSum _ _

end TauCeti

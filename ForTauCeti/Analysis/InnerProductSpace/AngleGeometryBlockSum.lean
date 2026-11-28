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
import TauCeti.Analysis.InnerProductSpace.Spectral.BlockSum

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
  FiniteDimensional.completeSpace 𝕜 E


attribute [local instance] ContinuousLinearMap.realAlgebra ContinuousLinearMap.realIsScalarTower

namespace TauCeti

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]

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
  apply LinearMap.toContinuousLinearMap.injective
  rw [(UnitarilyInvariantSeminorm.orthogonalBlockSum_isSymmetric hA hB).toContinuousLinearMap_cfc]
  have hAc : IsSelfAdjoint A.toContinuousLinearMap :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA
  have hBc : IsSelfAdjoint B.toContinuousLinearMap :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hB
  have toContinuousBlock (P : E₁ →ₗ[𝕜] E₁) (Q : E₂ →ₗ[𝕜] E₂) :
      ((P.prodMap Q).withLpMap 2).toContinuousLinearMap =
        P.toContinuousLinearMap.withLpProdMap 2 Q.toContinuousLinearMap := by
    apply (LinearMap.toContinuousLinearMap_eq_iff_eq_toLinearMap _ _).mpr
    exact (ContinuousLinearMap.coe_withLpProdMap (p := 2)
      P.toContinuousLinearMap Q.toContinuousLinearMap).symm
  rw [toContinuousBlock A B,
    ContinuousLinearMap.cfc_withLpProdMap A.toContinuousLinearMap B.toContinuousLinearMap
    f hAc hBc
    (((A.toContinuousLinearMap.finite_spectrum ℝ).union
      (B.toContinuousLinearMap.finite_spectrum ℝ)).continuousOn f),
    ← hA.toContinuousLinearMap_cfc, ← hB.toContinuousLinearMap_cfc,
    toContinuousBlock (hA.cfc f) (hB.cfc f)]

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
      (U₁.starProjection.toLinearMap - V₁.starProjection.toLinearMap).operatorAbs := by
    symm
    apply (LinearMap.toContinuousLinearMap_eq_iff_eq_toLinearMap _ _).mp
    rw [LinearMap.toContinuousLinearMap_operatorAbs_eq_modulus, Submodule.sinAngleOperator_def]
    congr 1
  have h₂ : (Submodule.sinAngleOperator U₂ V₂).toLinearMap =
      (U₂.starProjection.toLinearMap - V₂.starProjection.toLinearMap).operatorAbs := by
    symm
    apply (LinearMap.toContinuousLinearMap_eq_iff_eq_toLinearMap _ _).mp
    rw [LinearMap.toContinuousLinearMap_operatorAbs_eq_modulus, Submodule.sinAngleOperator_def]
    congr 1
  have h₃ : (Submodule.sinAngleOperator
      (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule U₁ U₂)
      (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule V₁ V₂)).toLinearMap =
      (((UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule U₁ U₂)).starProjection.toLinearMap -
        ((UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule V₁
            V₂)).starProjection.toLinearMap).operatorAbs := by
    symm
    apply (LinearMap.toContinuousLinearMap_eq_iff_eq_toLinearMap _ _).mp
    rw [LinearMap.toContinuousLinearMap_operatorAbs_eq_modulus, Submodule.sinAngleOperator_def]
    congr 1
  rw [h₃, h₁, h₂,
    UnitarilyInvariantSeminorm.starProjection_orthogonalBlockSumSubmodule U₁ U₂,
    UnitarilyInvariantSeminorm.starProjection_orthogonalBlockSumSubmodule V₁ V₂]
  change (((U₁.starProjection.toLinearMap - V₁.starProjection.toLinearMap).prodMap
    (U₂.starProjection.toLinearMap - V₂.starProjection.toLinearMap)).withLpMap 2).operatorAbs = _
  exact UnitarilyInvariantSeminorm.operatorAbs_orthogonalBlockSum _ _

end TauCeti

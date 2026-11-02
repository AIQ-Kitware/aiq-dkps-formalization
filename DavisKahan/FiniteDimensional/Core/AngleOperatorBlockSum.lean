/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Sol
-/
module

public import TauCeti.Analysis.InnerProductSpace.Projection.AngleOperator

public import DavisKahan.FiniteDimensional.Core.AngleOperators
public import ForTauCeti.Analysis.InnerProductSpace.AngleGeometryBlockSum

/-!
# Finite angle operators on orthogonal block sums

The canonical finite angle operator and its totalized tangent functions preserve orthogonal direct
sums.  The sine-angle statement lives in `ForTauCeti`; this file lifts that paper-independent
operator geometry through the Davis--Kahan finite functional-calculus definitions of `Theta`,
`tan Theta`, and `tan (2 Theta)`.
-/

public section

local instance {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] : CompleteSpace E :=
  FiniteDimensional.complete 𝕜 E


namespace TauCeti
namespace DavisKahan.FiniteDimensional

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The canonical finite angle operator preserves orthogonal direct sums. -/
theorem angleOperator_orthogonalBlockSumSubmodule
    {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [FiniteDimensional 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] [FiniteDimensional 𝕜 E₂]
    (U₁ V₁ : Submodule 𝕜 E₁) (U₂ V₂ : Submodule 𝕜 E₂) :
    angleOperator
        (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule U₁ U₂)
        (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule V₁ V₂) =
      ((angleOperator U₁ V₁).prodMap (angleOperator U₂ V₂)).withLpMap 2 := by
  let S₁ := (Submodule.sinAngleOperator U₁ V₁).toLinearMap
  let S₂ := (Submodule.sinAngleOperator U₂ V₂).toLinearMap
  have hS₁ : S₁.IsSymmetric := by
    exact (U₁.isPositive_sinAngleOperator V₁).isSelfAdjoint.isSymmetric
  have hS₂ : S₂.IsSymmetric := by
    exact (U₂.isPositive_sinAngleOperator V₂).isSelfAdjoint.isSymmetric
  let hblock :=
    UnitarilyInvariantSeminorm.orthogonalBlockSum_isSymmetric hS₁ hS₂
  have hsin :
      (Submodule.sinAngleOperator (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule U₁ U₂) (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule V₁ V₂)).toLinearMap =
        (S₁.prodMap S₂).withLpMap 2 :=
    TauCeti.sinAngleOperator_orthogonalBlockSumSubmodule U₁ V₁ U₂ V₂
  have hsum : LinearMap.IsSymmetric
      ((Submodule.sinAngleOperator (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule U₁ U₂) (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule V₁ V₂)).toLinearMap) := by
    rw [hsin]
    exact hblock
  calc
    angleOperator
        (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule U₁ U₂)
        (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule V₁ V₂) =
      LinearMap.IsSymmetric.cfc hblock Real.arcsin := by
        unfold angleOperator
        exact TauCeti.cfc_congr_operator hsum hblock hsin Real.arcsin
    _ = ((LinearMap.IsSymmetric.cfc hS₁ Real.arcsin).prodMap
      (LinearMap.IsSymmetric.cfc hS₂ Real.arcsin)).withLpMap 2 :=
      TauCeti.selfAdjointFunctionalCalculus_orthogonalBlockSum hS₁ hS₂ Real.arcsin
    _ = ((angleOperator U₁ V₁).prodMap (angleOperator U₂ V₂)).withLpMap 2 := rfl

/-- The canonical finite `tan Theta` operator preserves orthogonal direct sums. -/
theorem tanAngleOperator_orthogonalBlockSumSubmodule
    {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [FiniteDimensional 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] [FiniteDimensional 𝕜 E₂]
    (U₁ V₁ : Submodule 𝕜 E₁) (U₂ V₂ : Submodule 𝕜 E₂) :
    tanAngleOperator
        (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule U₁ U₂)
        (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule V₁ V₂) =
      ((tanAngleOperator U₁ V₁).prodMap (tanAngleOperator U₂ V₂)).withLpMap 2 := by
  have hangle := angleOperator_orthogonalBlockSumSubmodule U₁ V₁ U₂ V₂
  have hA₁ : (angleOperator U₁ V₁).IsSymmetric := by
    unfold angleOperator
    exact LinearMap.IsSymmetric.isSymmetric_cfc _ _
  have hA₂ : (angleOperator U₂ V₂).IsSymmetric := by
    unfold angleOperator
    exact LinearMap.IsSymmetric.isSymmetric_cfc _ _
  let hblock :=
    UnitarilyInvariantSeminorm.orthogonalBlockSum_isSymmetric hA₁ hA₂
  have hsum : LinearMap.IsSymmetric
      (angleOperator
        (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule U₁ U₂)
        (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule V₁ V₂)) := by
    unfold angleOperator
    exact LinearMap.IsSymmetric.isSymmetric_cfc _ _
  calc
    tanAngleOperator
        (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule U₁ U₂)
        (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule V₁ V₂) =
      LinearMap.IsSymmetric.cfc hblock safeTan := by
        unfold tanAngleOperator
        exact TauCeti.cfc_congr_operator hsum hblock hangle safeTan
    _ = ((LinearMap.IsSymmetric.cfc hA₁ safeTan).prodMap
      (LinearMap.IsSymmetric.cfc hA₂ safeTan)).withLpMap 2 :=
      TauCeti.selfAdjointFunctionalCalculus_orthogonalBlockSum hA₁ hA₂ safeTan
    _ = ((tanAngleOperator U₁ V₁).prodMap (tanAngleOperator U₂ V₂)).withLpMap 2 := rfl

/-- The canonical finite `tan (2 Theta)` operator preserves orthogonal direct sums. -/
theorem tanTwoAngleOperator_orthogonalBlockSumSubmodule
    {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [FiniteDimensional 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] [FiniteDimensional 𝕜 E₂]
    (U₁ V₁ : Submodule 𝕜 E₁) (U₂ V₂ : Submodule 𝕜 E₂) :
    tanTwoAngleOperator
        (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule U₁ U₂)
        (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule V₁ V₂) =
      ((tanTwoAngleOperator U₁ V₁).prodMap (tanTwoAngleOperator U₂ V₂)).withLpMap 2 := by
  have hangle := angleOperator_orthogonalBlockSumSubmodule U₁ V₁ U₂ V₂
  have hA₁ : (angleOperator U₁ V₁).IsSymmetric := by
    unfold angleOperator
    exact LinearMap.IsSymmetric.isSymmetric_cfc _ _
  have hA₂ : (angleOperator U₂ V₂).IsSymmetric := by
    unfold angleOperator
    exact LinearMap.IsSymmetric.isSymmetric_cfc _ _
  let hblock :=
    UnitarilyInvariantSeminorm.orthogonalBlockSum_isSymmetric hA₁ hA₂
  have hsum : LinearMap.IsSymmetric
      (angleOperator
        (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule U₁ U₂)
        (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule V₁ V₂)) := by
    unfold angleOperator
    exact LinearMap.IsSymmetric.isSymmetric_cfc _ _
  calc
    tanTwoAngleOperator
        (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule U₁ U₂)
        (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule V₁ V₂) =
      LinearMap.IsSymmetric.cfc hblock safeTanTwo := by
        unfold tanTwoAngleOperator
        exact TauCeti.cfc_congr_operator hsum hblock hangle safeTanTwo
    _ = ((LinearMap.IsSymmetric.cfc hA₁ safeTanTwo).prodMap
      (LinearMap.IsSymmetric.cfc hA₂ safeTanTwo)).withLpMap 2 :=
      TauCeti.selfAdjointFunctionalCalculus_orthogonalBlockSum hA₁ hA₂ safeTanTwo
    _ = ((tanTwoAngleOperator U₁ V₁).prodMap (tanTwoAngleOperator U₂ V₂)).withLpMap 2 := rfl

end DavisKahan.FiniteDimensional
end TauCeti

/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Sol
-/
module

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
      UnitarilyInvariantSeminorm.orthogonalBlockSum
        (angleOperator U₁ V₁) (angleOperator U₂ V₂) := by
  let S₁ := sinAngleOperator U₁ V₁
  let S₂ := sinAngleOperator U₂ V₂
  have hS₁ : S₁.IsSymmetric := by
    dsimp only [S₁]
    rw [TauCeti.sinAngleOperator_eq_operatorAbs]
    exact (LinearMap.isPositive_operatorAbs (projection U₁ - projection V₁)).isSymmetric
  have hS₂ : S₂.IsSymmetric := by
    dsimp only [S₂]
    rw [TauCeti.sinAngleOperator_eq_operatorAbs]
    exact (LinearMap.isPositive_operatorAbs (projection U₂ - projection V₂)).isSymmetric
  let hblock :=
    UnitarilyInvariantSeminorm.orthogonalBlockSum_isSymmetric hS₁ hS₂
  have hsin :
      sinAngleOperator
          (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule U₁ U₂)
          (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule V₁ V₂) =
        UnitarilyInvariantSeminorm.orthogonalBlockSum S₁ S₂ :=
    TauCeti.sinAngleOperator_orthogonalBlockSumSubmodule U₁ V₁ U₂ V₂
  have hsum : LinearMap.IsSymmetric
      (sinAngleOperator
        (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule U₁ U₂)
        (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule V₁ V₂)) := by
    rw [hsin]
    exact hblock
  calc
    angleOperator
        (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule U₁ U₂)
        (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule V₁ V₂) =
      LinearMap.IsSymmetric.cfc hblock Real.arcsin := by
        unfold angleOperator
        exact TauCeti.cfc_congr_operator hsum hblock hsin Real.arcsin
    _ = UnitarilyInvariantSeminorm.orthogonalBlockSum
          (LinearMap.IsSymmetric.cfc hS₁ Real.arcsin)
          (LinearMap.IsSymmetric.cfc hS₂ Real.arcsin) :=
      TauCeti.selfAdjointFunctionalCalculus_orthogonalBlockSum hS₁ hS₂ Real.arcsin
    _ = UnitarilyInvariantSeminorm.orthogonalBlockSum
          (angleOperator U₁ V₁) (angleOperator U₂ V₂) := rfl

/-- The canonical finite `tan Theta` operator preserves orthogonal direct sums. -/
theorem tanAngleOperator_orthogonalBlockSumSubmodule
    {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [FiniteDimensional 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] [FiniteDimensional 𝕜 E₂]
    (U₁ V₁ : Submodule 𝕜 E₁) (U₂ V₂ : Submodule 𝕜 E₂) :
    tanAngleOperator
        (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule U₁ U₂)
        (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule V₁ V₂) =
      UnitarilyInvariantSeminorm.orthogonalBlockSum
        (tanAngleOperator U₁ V₁) (tanAngleOperator U₂ V₂) := by
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
    _ = UnitarilyInvariantSeminorm.orthogonalBlockSum
          (LinearMap.IsSymmetric.cfc hA₁ safeTan)
          (LinearMap.IsSymmetric.cfc hA₂ safeTan) :=
      TauCeti.selfAdjointFunctionalCalculus_orthogonalBlockSum hA₁ hA₂ safeTan
    _ = UnitarilyInvariantSeminorm.orthogonalBlockSum
          (tanAngleOperator U₁ V₁) (tanAngleOperator U₂ V₂) := rfl

/-- The canonical finite `tan (2 Theta)` operator preserves orthogonal direct sums. -/
theorem tanTwoAngleOperator_orthogonalBlockSumSubmodule
    {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [FiniteDimensional 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] [FiniteDimensional 𝕜 E₂]
    (U₁ V₁ : Submodule 𝕜 E₁) (U₂ V₂ : Submodule 𝕜 E₂) :
    tanTwoAngleOperator
        (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule U₁ U₂)
        (UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule V₁ V₂) =
      UnitarilyInvariantSeminorm.orthogonalBlockSum
        (tanTwoAngleOperator U₁ V₁) (tanTwoAngleOperator U₂ V₂) := by
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
    _ = UnitarilyInvariantSeminorm.orthogonalBlockSum
          (LinearMap.IsSymmetric.cfc hA₁ safeTanTwo)
          (LinearMap.IsSymmetric.cfc hA₂ safeTanTwo) :=
      TauCeti.selfAdjointFunctionalCalculus_orthogonalBlockSum hA₁ hA₂ safeTanTwo
    _ = UnitarilyInvariantSeminorm.orthogonalBlockSum
          (tanTwoAngleOperator U₁ V₁) (tanTwoAngleOperator U₂ V₂) := rfl

end DavisKahan.FiniteDimensional
end TauCeti

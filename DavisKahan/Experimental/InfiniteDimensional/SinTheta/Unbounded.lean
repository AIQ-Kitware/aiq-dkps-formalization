/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.SinTheta.Unbounded.Core
import DavisKahan.Experimental.InfiniteDimensional.Sylvester.Unbounded

/-!
# Unbounded Davis--Kahan `sin Θ` endpoints

The problem data and the residual block identity now live in
`DavisKahan.SinTheta.Unbounded.Core`.  The endpoints below consume an unbounded
Sylvester estimate; the finite-interval branch is stated through the legacy
generic truncation API, which is still an open obligation.
-/

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open scoped InnerProductSpace

section GenericCore

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- Isometric finite-interval/exterior specialization. -/
theorem sinTheta_unbounded_of_intervalExteriorGap
    [HasApproximationNumberStrongCutoff.{u, v, 0} 𝕜]
    [HasKyFanApproximationGaugeTriangle.{u, v} 𝕜]
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    (D : UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := G))
    (hA : D.A.IsSelfAdjoint)
    (hA₀ : D.A₀.IsSelfAdjoint)
    (hΛ₁ : D.Λ₁.IsSelfAdjoint)
    (_hX : IsometricEmbedding D.X)
    (hF₁ : IsometricEmbedding D.F₁)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hgap : UnboundedIntervalExteriorGap D.A₀ D.Λ₁ β α δ)
    (hR : N.Mem D.residual) :
    N.Mem (D.X.adjoint ∘L D.F₁) ∧
      δ * N.gauge (D.X.adjoint ∘L D.F₁)
        ≤ N.gauge D.residual := by
  have hEq := unbounded_adjoint_residual_block_identity D hA hA₀ hΛ₁
  have hC := adjointResidualBlock_mem_and_gauge_le N D hF₁ hR
  have hRaw := unbounded_sylvester_mem_and_gauge_le_of_intervalExteriorGap
    N hA₀ hΛ₁ hβα hδ hgap hEq hC.1
  exact ⟨hRaw.1, hRaw.2.trans hC.2⟩

/-- Isometric headline specialization of the complete unbounded block theorem. -/
theorem sinTheta_unbounded
    [HasApproximationNumberStrongCutoff.{u, v, 0} 𝕜]
    [HasKyFanApproximationGaugeTriangle.{u, v} 𝕜]
    (N : UnitaryInvariantIdealFamily (𝕜 := 𝕜))
    (D : UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := G))
    (hA : D.A.IsSelfAdjoint)
    (hA₀ : D.A₀.IsSelfAdjoint)
    (hΛ₁ : D.Λ₁.IsSelfAdjoint)
    (_hX : IsometricEmbedding D.X)
    (hF₁ : IsometricEmbedding D.F₁)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : UnboundedSylvesterGap D.A₀ D.Λ₁ δ)
    (hR : N.toRectangularSymmetricIdealFamily.Mem D.residual) :
    N.toRectangularSymmetricIdealFamily.Mem (D.X.adjoint ∘L D.F₁) ∧
      δ * N.toRectangularSymmetricIdealFamily.gauge (D.X.adjoint ∘L D.F₁)
        ≤ N.toRectangularSymmetricIdealFamily.gauge D.residual := by
  let M := N.toRectangularSymmetricIdealFamily
  have hEq := unbounded_adjoint_residual_block_identity D hA hA₀ hΛ₁
  have hC := adjointResidualBlock_mem_and_gauge_le M D hF₁ hR
  have hRaw := davisKahan1970_sylvester N hA₀ hΛ₁ hδ hgap hEq hC.1
  exact ⟨hRaw.1, hRaw.2.trans hC.2⟩

end GenericCore

section ComplexGeneralized

universe v

variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Generalized finite-interval/exterior endpoint.  At least one diagonal block
has bounded spectrum, so this is not the fully two-unbounded theorem. -/
theorem generalizedSinTheta_unbounded_of_intervalExteriorGap
    (N : RectangularSymmetricIdealFamily (𝕜 := ℂ))
    (D : UnboundedSinThetaData (𝕜 := ℂ) (E := E) (F := F) (G := G))
    (hA : D.A.IsSelfAdjoint)
    (hA₀ : D.A₀.IsSelfAdjoint)
    (hΛ₁ : D.Λ₁.IsSelfAdjoint)
    (hF₁ : IsometricEmbedding D.F₁)
    {β α δ ε : ℝ}
    (hβα : β ≤ α) (hδ : 0 < δ) (hε : 0 < ε)
    (hframe : LowerFrameBound D.X ε)
    (hgap : UnboundedIntervalExteriorGap D.A₀ D.Λ₁ β α δ)
    (hR : N.Mem D.residual) :
    N.Mem (sinThetaBlock D.X D.F₁ hframe hε) ∧
      δ * ε * N.gauge (sinThetaBlock D.X D.F₁ hframe hε)
        ≤ N.gauge D.residual := by
  have hEq := unbounded_adjoint_residual_block_identity D hA hA₀ hΛ₁
  have hC := adjointResidualBlock_mem_and_gauge_le N D hF₁ hR
  have hRaw := unbounded_sylvester_mem_and_gauge_le_of_intervalExteriorGap
    N hA₀ hΛ₁ hβα hδ hgap hEq hC.1
  have hFrame := lowerFrame_sinThetaBlock_mem_and_gauge_le
    N D.X D.F₁ hframe hε hRaw.1
  refine ⟨hFrame.1, ?_⟩
  calc
    δ * ε * N.gauge (sinThetaBlock D.X D.F₁ hframe hε)
        = δ * (ε * N.gauge (sinThetaBlock D.X D.F₁ hframe hε)) := by ring
    _ ≤ δ * N.gauge (D.X.adjoint ∘L D.F₁) :=
      mul_le_mul_of_nonneg_left hFrame.2 hδ.le
    _ ≤ N.gauge (-(D.residual.adjoint ∘L D.F₁)) := hRaw.2
    _ ≤ N.gauge D.residual := hC.2

/-- Exact generalized finite-interval/exterior endpoint, with the full
directed sine identified by a complete orthogonal exact-space decomposition. -/
theorem generalizedSinTheta_unbounded_exact_of_intervalExteriorGap
    (N : RectangularSymmetricIdealFamily (𝕜 := ℂ))
    (D : UnboundedSinThetaData (𝕜 := ℂ) (E := E) (F := F) (G := G))
    (F₀ : H →L[ℂ] E)
    (hA : D.A.IsSelfAdjoint)
    (hA₀ : D.A₀.IsSelfAdjoint)
    (hΛ₁ : D.Λ₁.IsSelfAdjoint)
    (hdecomp : OrthogonalExactDecomposition F₀ D.F₁)
    {β α δ ε : ℝ}
    (hβα : β ≤ α) (hδ : 0 < δ) (hε : 0 < ε)
    (hframe : LowerFrameBound D.X ε)
    (hgap : UnboundedIntervalExteriorGap D.A₀ D.Λ₁ β α δ)
    (hR : N.Mem D.residual) :
    N.Mem (directedSinThetaOperator D.X F₀ hframe hε) ∧
      δ * ε * N.gauge (directedSinThetaOperator D.X F₀ hframe hε)
        ≤ N.gauge D.residual := by
  have hBlock := generalizedSinTheta_unbounded_of_intervalExteriorGap
    N D hA hA₀ hΛ₁ hdecomp.isometry₁ hβα hδ hε hframe hgap hR
  have hAngle := sinThetaBlock_mem_and_gauge_eq_directedSinThetaOperator
    N D.X F₀ D.F₁ hframe hε hdecomp hBlock.1
  refine ⟨hAngle.1, ?_⟩
  rw [hAngle.2]
  exact hBlock.2

/-- Complete generalized unbounded complementary-block theorem.  The gap may
be finite interval/exterior or either ordered half-line orientation. -/
theorem generalizedSinTheta_unbounded
    (N : UnitaryInvariantIdealFamily (𝕜 := ℂ))
    (D : UnboundedSinThetaData (𝕜 := ℂ) (E := E) (F := F) (G := G))
    (hA : D.A.IsSelfAdjoint)
    (hA₀ : D.A₀.IsSelfAdjoint)
    (hΛ₁ : D.Λ₁.IsSelfAdjoint)
    (hF₁ : IsometricEmbedding D.F₁)
    {δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε)
    (hframe : LowerFrameBound D.X ε)
    (hgap : UnboundedSylvesterGap D.A₀ D.Λ₁ δ)
    (hR : N.toRectangularSymmetricIdealFamily.Mem D.residual) :
    N.toRectangularSymmetricIdealFamily.Mem (sinThetaBlock D.X D.F₁ hframe hε) ∧
      δ * ε * N.toRectangularSymmetricIdealFamily.gauge (sinThetaBlock D.X D.F₁ hframe hε)
        ≤ N.toRectangularSymmetricIdealFamily.gauge D.residual := by
  let M := N.toRectangularSymmetricIdealFamily
  have hEq := unbounded_adjoint_residual_block_identity D hA hA₀ hΛ₁
  have hC := adjointResidualBlock_mem_and_gauge_le M D hF₁ hR
  have hRaw := davisKahan1970_sylvester N hA₀ hΛ₁ hδ hgap hEq hC.1
  have hFrame := lowerFrame_sinThetaBlock_mem_and_gauge_le
    M D.X D.F₁ hframe hε hRaw.1
  refine ⟨hFrame.1, ?_⟩
  calc
    δ * ε * M.gauge (sinThetaBlock D.X D.F₁ hframe hε)
        = δ * (ε * M.gauge (sinThetaBlock D.X D.F₁ hframe hε)) := by ring
    _ ≤ δ * M.gauge (D.X.adjoint ∘L D.F₁) :=
      mul_le_mul_of_nonneg_left hFrame.2 hδ.le
    _ ≤ M.gauge (-(D.residual.adjoint ∘L D.F₁)) := hRaw.2
    _ ≤ M.gauge D.residual := hC.2

/-- Exact complete generalized unbounded Davis--Kahan theorem, with the full
directed sine operator identified through a complete orthogonal exact-space
decomposition. -/
theorem generalizedSinTheta_unbounded_exact
    (N : UnitaryInvariantIdealFamily (𝕜 := ℂ))
    (D : UnboundedSinThetaData (𝕜 := ℂ) (E := E) (F := F) (G := G))
    (F₀ : H →L[ℂ] E)
    (hA : D.A.IsSelfAdjoint)
    (hA₀ : D.A₀.IsSelfAdjoint)
    (hΛ₁ : D.Λ₁.IsSelfAdjoint)
    (hdecomp : OrthogonalExactDecomposition F₀ D.F₁)
    {δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε)
    (hframe : LowerFrameBound D.X ε)
    (hgap : UnboundedSylvesterGap D.A₀ D.Λ₁ δ)
    (hR : N.toRectangularSymmetricIdealFamily.Mem D.residual) :
    N.toRectangularSymmetricIdealFamily.Mem (directedSinThetaOperator D.X F₀ hframe hε) ∧
      δ * ε * N.toRectangularSymmetricIdealFamily.gauge (directedSinThetaOperator D.X F₀ hframe hε)
        ≤ N.toRectangularSymmetricIdealFamily.gauge D.residual := by
  let M := N.toRectangularSymmetricIdealFamily
  have hBlock := generalizedSinTheta_unbounded
    N D hA hA₀ hΛ₁ hdecomp.isometry₁ hδ hε hframe hgap hR
  have hAngle := sinThetaBlock_mem_and_gauge_eq_directedSinThetaOperator
    M D.X F₀ D.F₁ hframe hε hdecomp hBlock.1
  refine ⟨hAngle.1, ?_⟩
  rw [hAngle.2]
  exact hBlock.2

end ComplexGeneralized

section GenericExact

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- Exact isometric finite-interval/exterior endpoint. -/
theorem sinTheta_unbounded_exact_of_intervalExteriorGap
    [HasApproximationNumberStrongCutoff.{u, v, 0} 𝕜]
    [HasKyFanApproximationGaugeTriangle.{u, v} 𝕜]
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    (D : UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := G))
    (F₀ : H →L[𝕜] E)
    (hA : D.A.IsSelfAdjoint)
    (hA₀ : D.A₀.IsSelfAdjoint)
    (hΛ₁ : D.Λ₁.IsSelfAdjoint)
    (hX : IsometricEmbedding D.X)
    (hdecomp : OrthogonalExactDecomposition F₀ D.F₁)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hgap : UnboundedIntervalExteriorGap D.A₀ D.Λ₁ β α δ)
    (hR : N.Mem D.residual) :
    N.Mem
      ((ContinuousLinearMap.id 𝕜 E - F₀ ∘L F₀.adjoint) ∘L D.X) ∧
      δ * N.gauge
        ((ContinuousLinearMap.id 𝕜 E - F₀ ∘L F₀.adjoint) ∘L D.X)
        ≤ N.gauge D.residual := by
  have hBlock := sinTheta_unbounded_of_intervalExteriorGap
    N D hA hA₀ hΛ₁ hX hdecomp.isometry₁ hβα hδ hgap hR
  have hAngle := isometricComplementaryBlock_mem_and_gauge_eq_directed
    N D.X F₀ D.F₁ hX hdecomp hBlock.1
  refine ⟨hAngle.1, ?_⟩
  rw [hAngle.2]
  exact hBlock.2

/-- Exact isometric headline specialization of the complete unbounded theorem. -/
theorem sinTheta_unbounded_exact
    [HasApproximationNumberStrongCutoff.{u, v, 0} 𝕜]
    [HasKyFanApproximationGaugeTriangle.{u, v} 𝕜]
    (N : UnitaryInvariantIdealFamily (𝕜 := 𝕜))
    (D : UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := G))
    (F₀ : H →L[𝕜] E)
    (hA : D.A.IsSelfAdjoint)
    (hA₀ : D.A₀.IsSelfAdjoint)
    (hΛ₁ : D.Λ₁.IsSelfAdjoint)
    (hX : IsometricEmbedding D.X)
    (hdecomp : OrthogonalExactDecomposition F₀ D.F₁)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : UnboundedSylvesterGap D.A₀ D.Λ₁ δ)
    (hR : N.toRectangularSymmetricIdealFamily.Mem D.residual) :
    N.toRectangularSymmetricIdealFamily.Mem
      ((ContinuousLinearMap.id 𝕜 E - F₀ ∘L F₀.adjoint) ∘L D.X) ∧
      δ * N.toRectangularSymmetricIdealFamily.gauge
        ((ContinuousLinearMap.id 𝕜 E - F₀ ∘L F₀.adjoint) ∘L D.X)
        ≤ N.toRectangularSymmetricIdealFamily.gauge D.residual := by
  have hBlock := sinTheta_unbounded
    N D hA hA₀ hΛ₁ hX hdecomp.isometry₁ hδ hgap hR
  have hAngle := isometricComplementaryBlock_mem_and_gauge_eq_directed
    N.toRectangularSymmetricIdealFamily D.X F₀ D.F₁ hX hdecomp hBlock.1
  refine ⟨hAngle.1, ?_⟩
  rw [hAngle.2]
  exact hBlock.2

end GenericExact

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib

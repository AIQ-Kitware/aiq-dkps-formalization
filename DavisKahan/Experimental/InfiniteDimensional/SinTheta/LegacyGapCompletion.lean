/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.Unbounded
import DavisKahan.Experimental.InfiniteDimensional.Sylvester.LegacyGapCompletion

/-!
# Completion of the manuscript-shaped complex gap surface

The historical problem records use `UnboundedSylvesterGap`.  This module keeps
those statements intact while routing their complex proofs through the direct
genuine-spectrum Sylvester engine.  It is deliberately above both the
Sylvester and sine-theta implementation layers so that the compatibility route
does not enter either foundational import cone.
-/

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open scoped InnerProductSpace

section Complex

universe v

variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Complex isometric complementary-block theorem routed through the direct
manuscript-shaped Sylvester engine. -/
theorem sinTheta_unbounded_complex
    (N : UnitaryInvariantIdealFamily (𝕜 := ℂ))
    (D : UnboundedSinThetaData (𝕜 := ℂ) (E := E) (F := F) (G := G))
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
  have hRaw := davisKahan1970_sylvester_complex
    N hA₀ hΛ₁ hδ hgap hEq hC.1
  exact ⟨hRaw.1, hRaw.2.trans hC.2⟩

/-- Exact complex isometric theorem with the directed sine operator used by
the manuscript surface. -/
theorem sinTheta_unbounded_exact_complex
    (N : UnitaryInvariantIdealFamily (𝕜 := ℂ))
    (D : UnboundedSinThetaData (𝕜 := ℂ) (E := E) (F := F) (G := G))
    (F₀ : H →L[ℂ] E)
    (hA : D.A.IsSelfAdjoint)
    (hA₀ : D.A₀.IsSelfAdjoint)
    (hΛ₁ : D.Λ₁.IsSelfAdjoint)
    (hX : IsometricEmbedding D.X)
    (hdecomp : OrthogonalExactDecomposition F₀ D.F₁)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : UnboundedSylvesterGap D.A₀ D.Λ₁ δ)
    (hR : N.toRectangularSymmetricIdealFamily.Mem D.residual) :
    N.toRectangularSymmetricIdealFamily.Mem
      ((ContinuousLinearMap.id ℂ E - F₀ ∘L F₀.adjoint) ∘L D.X) ∧
      δ * N.toRectangularSymmetricIdealFamily.gauge
        ((ContinuousLinearMap.id ℂ E - F₀ ∘L F₀.adjoint) ∘L D.X)
        ≤ N.toRectangularSymmetricIdealFamily.gauge D.residual := by
  have hBlock := sinTheta_unbounded_complex
    N D hA hA₀ hΛ₁ hX hdecomp.isometry₁ hδ hgap hR
  have hAngle := isometricComplementaryBlock_mem_and_gauge_eq_directed
    N.toRectangularSymmetricIdealFamily D.X F₀ D.F₁ hX hdecomp hBlock.1
  refine ⟨hAngle.1, ?_⟩
  rw [hAngle.2]
  exact hBlock.2

/-- Complex generalized complementary-block theorem for all three manuscript
gap configurations. -/
theorem generalizedSinTheta_unbounded_complex
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
    N.toRectangularSymmetricIdealFamily.Mem
        (sinThetaBlock D.X D.F₁ hframe hε) ∧
      δ * ε * N.toRectangularSymmetricIdealFamily.gauge
          (sinThetaBlock D.X D.F₁ hframe hε)
        ≤ N.toRectangularSymmetricIdealFamily.gauge D.residual := by
  let M := N.toRectangularSymmetricIdealFamily
  have hEq := unbounded_adjoint_residual_block_identity D hA hA₀ hΛ₁
  have hC := adjointResidualBlock_mem_and_gauge_le M D hF₁ hR
  have hRaw := davisKahan1970_sylvester_complex
    N hA₀ hΛ₁ hδ hgap hEq hC.1
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

/-- Exact complex generalized theorem for all three manuscript gap
configurations. -/
theorem generalizedSinTheta_unbounded_exact_complex
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
    N.toRectangularSymmetricIdealFamily.Mem
        (directedSinThetaOperator D.X F₀ hframe hε) ∧
      δ * ε * N.toRectangularSymmetricIdealFamily.gauge
          (directedSinThetaOperator D.X F₀ hframe hε)
        ≤ N.toRectangularSymmetricIdealFamily.gauge D.residual := by
  let M := N.toRectangularSymmetricIdealFamily
  have hBlock := generalizedSinTheta_unbounded_complex
    N D hA hA₀ hΛ₁ hdecomp.isometry₁ hδ hε hframe hgap hR
  have hAngle := sinThetaBlock_mem_and_gauge_eq_directedSinThetaOperator
    M D.X F₀ D.F₁ hframe hε hdecomp hBlock.1
  refine ⟨hAngle.1, ?_⟩
  rw [hAngle.2]
  exact hBlock.2

end Complex

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib

/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.SinTheta.Unbounded.Core
import DavisKahan.Sylvester.RealUnbounded

/-!
# Real unbounded sine-theta theorem

The complementary residual identity and exact-angle geometry are already
scalar-generic.  Combining them with the real unbounded Sylvester theorem gives
the full isometric sine-theta theorem over real Hilbert spaces for all three
gap configurations and every real Ky-Fan-dominant unitarily invariant
ideal family.
-/

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open scoped InnerProductSpace

noncomputable section

universe v

variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Real isometric complementary-block theorem for the complete unbounded gap
disjunction. -/
theorem sinTheta_unbounded_real
    (N : KyFanDominantIdealFamily (𝕜 := ℝ))
    (D : UnboundedSinThetaData (𝕜 := ℝ) (E := E) (F := F) (G := G))
    (hA : D.A.IsSelfAdjoint)
    (hA₀ : D.A₀.IsSelfAdjoint)
    (hΛ₁ : D.Λ₁.IsSelfAdjoint)
    (_hX : IsometricEmbedding D.X)
    (hF₁ : IsometricEmbedding D.F₁)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : UnboundedSylvesterGap D.A₀ D.Λ₁ δ)
    (hR : N.Mem D.residual) :
    N.Mem (D.X.adjoint ∘L D.F₁) ∧
      δ * N.gauge (D.X.adjoint ∘L D.F₁)
        ≤ N.gauge D.residual := by
  have hEq := unbounded_adjoint_residual_block_identity D hA hA₀ hΛ₁
  have hC := adjointResidualBlock_mem_and_gauge_le N.toRectangularSymmetricIdealFamily D hF₁ hR
  have hRaw := davisKahan1970_sylvester_real
    N hA₀ hΛ₁ hδ hgap hEq hC.1
  exact ⟨hRaw.1, hRaw.2.trans hC.2⟩

/-- Exact real isometric theorem in directed sine form. -/
theorem sinTheta_unbounded_exact_real
    (N : KyFanDominantIdealFamily (𝕜 := ℝ))
    (D : UnboundedSinThetaData (𝕜 := ℝ) (E := E) (F := F) (G := G))
    (F₀ : H →L[ℝ] E)
    (hA : D.A.IsSelfAdjoint)
    (hA₀ : D.A₀.IsSelfAdjoint)
    (hΛ₁ : D.Λ₁.IsSelfAdjoint)
    (hX : IsometricEmbedding D.X)
    (hdecomp : OrthogonalExactDecomposition F₀ D.F₁)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : UnboundedSylvesterGap D.A₀ D.Λ₁ δ)
    (hR : N.Mem D.residual) :
    N.Mem
      ((ContinuousLinearMap.id ℝ E - F₀ ∘L F₀.adjoint) ∘L D.X) ∧
      δ * N.gauge
        ((ContinuousLinearMap.id ℝ E - F₀ ∘L F₀.adjoint) ∘L D.X)
        ≤ N.gauge D.residual := by
  have hBlock := sinTheta_unbounded_real
    N D hA hA₀ hΛ₁ hX hdecomp.isometry₁ hδ hgap hR
  have hAngle := isometricComplementaryBlock_mem_and_gauge_eq_directed
    N.toRectangularSymmetricIdealFamily D.X F₀ D.F₁ hX hdecomp hBlock.1
  refine ⟨hAngle.1, ?_⟩
  simp only [KyFanDominantIdealFamily.gauge]
  rw [hAngle.2]
  exact hBlock.2

end

end ExactSinTheta
end Experimental
end DavisKahan
end TauCeti
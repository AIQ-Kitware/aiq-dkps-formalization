/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Sylvester.ShiftedInverse

/-!
# Operator-norm `sin Θ` bound from a two-sided shifted inverse
-/

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta


open scoped InnerProductSpace

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F G : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]

/-- **The unbounded Davis--Kahan `sin Θ` theorem, operator norm, honest
hypotheses.**  For the paper-shaped data `D` (self-adjoint ambient operator,
trial block `A₀`, complementary block `Λ₁`, isometric-into embeddings and the
residual identity), if the quadratic form of `A₀` lies in `[β, α]` while
`Λ₁ - (α+β)/2` has a bounded two-sided inverse of norm at most
`((α-β)/2 + δ)⁻¹`, then `δ ‖X⋆ ∘ F₁‖ ≤ ‖R⋆ ∘ F₁‖`. -/
theorem sinTheta_unbounded_opNorm
    (D : UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := G))
    (hA : D.A.IsSelfAdjoint) (hA₀ : D.A₀.IsSelfAdjoint)
    (hΛ₁ : D.Λ₁.IsSelfAdjoint)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hA₀low : SemiboundedBelow D.A₀ β) (hA₀high : SemiboundedAbove D.A₀ α)
    (hΛres : TwoSidedShiftedInverseBound D.Λ₁ ((α + β) / 2)
      ((α - β) / 2 + δ)) :
    δ * ‖D.X.adjoint ∘L D.F₁‖ ≤ ‖D.residual.adjoint ∘L D.F₁‖ := by
  have hEq := unbounded_adjoint_residual_block_identity D hA hA₀ hΛ₁
  have h := norm_closedSylvester_le_of_exteriorInterval hA₀.isSymmetric
    hβα hδ hA₀low hA₀high hΛres hEq
  simpa [norm_neg] using h

end ExactSinTheta
end Experimental
end DavisKahan
end TauCeti
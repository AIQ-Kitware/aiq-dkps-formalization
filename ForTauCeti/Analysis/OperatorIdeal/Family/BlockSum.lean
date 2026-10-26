/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-6
-/
module

public import TauCeti.Analysis.OperatorIdeal.Family

/-!
# Block-sum bounds for operator-ideal families

The gauge of each block cut out by contractive factors is bounded by the gauge
of the original operator. When two such blocks sum to the original operator,
the sum of their gauges bounds its gauge from above.

This unmerged consequence is retained from the former DKPS `Family.Basic`
module. The operator-ideal family, its laws and its carrier are owned by Tau Ceti.
-/

public section

universe u v w

namespace TauCeti.OperatorIdealFamily

variable {𝕜 : Type u} [RCLike 𝕜] {E : Type v} {F : Type w}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable (N : OperatorIdealFamily.{u, v, w} 𝕜)

/-- A DKPS block-sum estimate for contractive factors. -/
theorem gauge_blockSum_le {T : E →L[𝕜] F} {P₁ P₂ : E →L[𝕜] E} {Q₁ Q₂ : F →L[𝕜] F}
    (hP₁ : ‖P₁‖ ≤ 1) (hP₂ : ‖P₂‖ ≤ 1) (hQ₁ : ‖Q₁‖ ≤ 1) (hQ₂ : ‖Q₂‖ ≤ 1)
    (hsplit : Q₁ ∘L T ∘L P₁ + Q₂ ∘L T ∘L P₂ = T) :
    max (N.gauge (Q₁ ∘L T ∘L P₁)) (N.gauge (Q₂ ∘L T ∘L P₂)) ≤ N.gauge T ∧
      N.gauge T ≤ N.gauge (Q₁ ∘L T ∘L P₁) + N.gauge (Q₂ ∘L T ∘L P₂) := by
  have hcomp (Q : F →L[𝕜] F) (P : E →L[𝕜] E) (hQ : ‖Q‖ ≤ 1) (hP : ‖P‖ ≤ 1) :
      N.gauge (Q ∘L T ∘L P) ≤ N.gauge T :=
    (N.gauge_comp_left_le_self hQ (T ∘L P)).trans (N.gauge_comp_right_le_self T hP)
  refine ⟨max_le (hcomp Q₁ P₁ hQ₁ hP₁) (hcomp Q₂ P₂ hQ₂ hP₂), ?_⟩
  calc N.gauge T = N.gauge (Q₁ ∘L T ∘L P₁ + Q₂ ∘L T ∘L P₂) := by rw [hsplit]
    _ ≤ N.gauge (Q₁ ∘L T ∘L P₁) + N.gauge (Q₂ ∘L T ∘L P₂) := N.gauge_add_le _ _

end TauCeti.OperatorIdealFamily

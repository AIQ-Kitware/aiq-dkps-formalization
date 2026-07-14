/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import ForMathlib.Analysis.InnerProductSpace.DavisKahan.Experimental.ExactSinTheta.BoundedSpectralBridge
import ForMathlib.Analysis.InnerProductSpace.DavisKahan.Experimental.ExactSinTheta.FrameFactorization

/-!
# Exact bounded infinite-dimensional `sin Θ` endpoints

The complementary-block theorem is separated from the final angle
identification.  To call the block the full directed sine, the exact desired
space and its orthogonal complement must form a complete decomposition of the
ambient Hilbert space.
-/

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open scoped InnerProductSpace

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- Residual of the trial map and trial block. -/
def generalResidual
    (A : E →L[𝕜] E) (X : F →L[𝕜] E)
    (A₀ : F →L[𝕜] F) : F →L[𝕜] E :=
  A ∘L X - X ∘L A₀

/-- Adjoint residual block identity used by the generalized theorem. -/
theorem adjoint_residual_block_identity
    {A : E →L[𝕜] E} {A₀ : F →L[𝕜] F}
    {Λ₁ : G →L[𝕜] G} {X : F →L[𝕜] E}
    {F₁ : G →L[𝕜] E}
    (hA : A.IsSymmetric) (hA₀ : A₀.IsSymmetric)
    (hΛ₁ : Λ₁.IsSymmetric)
    (hIntertwine : A ∘L F₁ = F₁ ∘L Λ₁) :
    (generalResidual A X A₀).adjoint ∘L F₁ =
      (X.adjoint ∘L F₁) ∘L Λ₁ -
        A₀ ∘L (X.adjoint ∘L F₁) := by
  sorry

/-- The same residual identity in the orientation consumed by the
Sylvester estimate. -/
theorem complementary_sylvester_equation
    {A : E →L[𝕜] E} {A₀ : F →L[𝕜] F}
    {Λ₁ : G →L[𝕜] G} {X : F →L[𝕜] E}
    {F₁ : G →L[𝕜] E}
    (hA : A.IsSymmetric) (hA₀ : A₀.IsSymmetric)
    (hΛ₁ : Λ₁.IsSymmetric)
    (hIntertwine : A ∘L F₁ = F₁ ∘L Λ₁) :
    A₀ ∘L (X.adjoint ∘L F₁) -
      (X.adjoint ∘L F₁) ∘L Λ₁ =
        -((generalResidual A X A₀).adjoint ∘L F₁) := by
  sorry

/-- The raw complementary block obeys the sharp interval/exterior estimate. -/
theorem complementaryBlock_mem_and_gauge_le
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    {A : E →L[𝕜] E} {A₀ : F →L[𝕜] F}
    {Λ₁ : G →L[𝕜] G} {X : F →L[𝕜] E}
    {F₁ : G →L[𝕜] E}
    (hA : A.IsSymmetric) (hA₀ : A₀.IsSymmetric)
    (hΛ₁ : Λ₁.IsSymmetric)
    (hF₁ : IsometricEmbedding F₁)
    (hIntertwine : A ∘L F₁ = F₁ ∘L Λ₁)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hgap : IntervalExteriorGap A₀ Λ₁ β α δ)
    (hR : N.Mem (generalResidual A X A₀)) :
    N.Mem (X.adjoint ∘L F₁) ∧
      δ * N.gauge (X.adjoint ∘L F₁)
        ≤ N.gauge (generalResidual A X A₀) := by
  sorry

/-- Bounded generalized complementary-block theorem.  This is the analytic
core of Theorem 6.1, before identifying the block with the full directed sine
of a complete exact-space decomposition. -/
theorem generalizedSinTheta_bounded
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    {A : E →L[𝕜] E} {A₀ : F →L[𝕜] F}
    {Λ₁ : G →L[𝕜] G} {X : F →L[𝕜] E}
    {F₁ : G →L[𝕜] E}
    (hA : A.IsSymmetric) (hA₀ : A₀.IsSymmetric)
    (hΛ₁ : Λ₁.IsSymmetric)
    (hF₁ : IsometricEmbedding F₁)
    (hIntertwine : A ∘L F₁ = F₁ ∘L Λ₁)
    {β α δ ε : ℝ}
    (hβα : β ≤ α) (hδ : 0 < δ) (hε : 0 < ε)
    (hframe : LowerFrameBound X ε)
    (hgap : IntervalExteriorGap A₀ Λ₁ β α δ)
    (hR : N.Mem (generalResidual A X A₀)) :
    N.Mem (sinThetaBlock X F₁ hframe hε) ∧
      δ * ε * N.gauge (sinThetaBlock X F₁ hframe hε)
        ≤ N.gauge (generalResidual A X A₀) := by
  sorry

/-- Isometric complementary-block specialization of the bounded theorem. -/
theorem sinTheta_bounded
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    {A : E →L[𝕜] E} {A₀ : F →L[𝕜] F}
    {Λ₁ : G →L[𝕜] G} {X : F →L[𝕜] E}
    {F₁ : G →L[𝕜] E}
    (hA : A.IsSymmetric) (hA₀ : A₀.IsSymmetric)
    (hΛ₁ : Λ₁.IsSymmetric)
    (hX : IsometricEmbedding X) (hF₁ : IsometricEmbedding F₁)
    (hIntertwine : A ∘L F₁ = F₁ ∘L Λ₁)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hgap : IntervalExteriorGap A₀ Λ₁ β α δ)
    (hR : N.Mem (generalResidual A X A₀)) :
    N.Mem (X.adjoint ∘L F₁) ∧
      δ * N.gauge (X.adjoint ∘L F₁)
        ≤ N.gauge (generalResidual A X A₀) := by
  sorry

/-- The desired exact space and its unwanted complement form an orthogonal
coordinate decomposition of the entire ambient Hilbert space. -/
structure OrthogonalExactDecomposition
    (F₀ : H →L[𝕜] E) (F₁ : G →L[𝕜] E) : Prop where
  isometry₀ : IsometricEmbedding F₀
  isometry₁ : IsometricEmbedding F₁
  orthogonal : F₀.adjoint ∘L F₁ = 0
  projection_sum :
    F₀ ∘L F₀.adjoint + F₁ ∘L F₁.adjoint =
      ContinuousLinearMap.id 𝕜 E

/-- Directed sine operator from the orthonormalized trial coordinates into the
orthogonal complement of the desired exact space. -/
noncomputable def directedSinThetaOperator
    (X : F →L[𝕜] E) (F₀ : H →L[𝕜] E) {ε : ℝ}
    (hX : LowerFrameBound X ε) (hε : 0 < ε) : F →L[𝕜] E :=
  (ContinuousLinearMap.id 𝕜 E - F₀ ∘L F₀.adjoint) ∘L
    frameIsometry X hX hε

/-- Under a complete orthogonal exact decomposition, the complementary overlap
block and the directed sine operator have the same ideal membership and gauge. -/
theorem sinThetaBlock_mem_and_gauge_eq_directedSinThetaOperator
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    (X : F →L[𝕜] E) (F₀ : H →L[𝕜] E) (F₁ : G →L[𝕜] E)
    {ε : ℝ} (hX : LowerFrameBound X ε) (hε : 0 < ε)
    (hdecomp : OrthogonalExactDecomposition F₀ F₁)
    (hblock : N.Mem (sinThetaBlock X F₁ hX hε)) :
    N.Mem (directedSinThetaOperator X F₀ hX hε) ∧
      N.gauge (directedSinThetaOperator X F₀ hX hε) =
        N.gauge (sinThetaBlock X F₁ hX hε) := by
  sorry

/-- Exact bounded infinite-dimensional Davis--Kahan Theorem 6.1, expressed in
terms of the full directed sine operator rather than an arbitrary invariant
complementary block. -/
theorem generalizedSinTheta_bounded_exact
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    {A : E →L[𝕜] E} {A₀ : F →L[𝕜] F}
    {Λ₁ : G →L[𝕜] G} {X : F →L[𝕜] E}
    {F₀ : H →L[𝕜] E} {F₁ : G →L[𝕜] E}
    (hA : A.IsSymmetric) (hA₀ : A₀.IsSymmetric)
    (hΛ₁ : Λ₁.IsSymmetric)
    (hdecomp : OrthogonalExactDecomposition F₀ F₁)
    (hIntertwine : A ∘L F₁ = F₁ ∘L Λ₁)
    {β α δ ε : ℝ}
    (hβα : β ≤ α) (hδ : 0 < δ) (hε : 0 < ε)
    (hframe : LowerFrameBound X ε)
    (hgap : IntervalExteriorGap A₀ Λ₁ β α δ)
    (hR : N.Mem (generalResidual A X A₀)) :
    N.Mem (directedSinThetaOperator X F₀ hframe hε) ∧
      δ * ε * N.gauge (directedSinThetaOperator X F₀ hframe hε)
        ≤ N.gauge (generalResidual A X A₀) := by
  sorry

/-- Exact isometric headline specialization of the bounded theorem. -/
theorem sinTheta_bounded_exact
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    {A : E →L[𝕜] E} {A₀ : F →L[𝕜] F}
    {Λ₁ : G →L[𝕜] G} {X : F →L[𝕜] E}
    {F₀ : H →L[𝕜] E} {F₁ : G →L[𝕜] E}
    (hA : A.IsSymmetric) (hA₀ : A₀.IsSymmetric)
    (hΛ₁ : Λ₁.IsSymmetric)
    (hX : IsometricEmbedding X)
    (hdecomp : OrthogonalExactDecomposition F₀ F₁)
    (hIntertwine : A ∘L F₁ = F₁ ∘L Λ₁)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hgap : IntervalExteriorGap A₀ Λ₁ β α δ)
    (hR : N.Mem (generalResidual A X A₀)) :
    N.Mem ((ContinuousLinearMap.id 𝕜 E - F₀ ∘L F₀.adjoint) ∘L X) ∧
      δ * N.gauge
        ((ContinuousLinearMap.id 𝕜 E - F₀ ∘L F₀.adjoint) ∘L X)
        ≤ N.gauge (generalResidual A X A₀) := by
  sorry

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib

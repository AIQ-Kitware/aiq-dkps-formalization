/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import ForMathlib.Analysis.InnerProductSpace.DavisKahan.Experimental.ExactSinTheta.BoundedSinTheta
import ForMathlib.Analysis.InnerProductSpace.DavisKahan.Experimental.ExactSinTheta.UnboundedSylvester

/-!
# Exact unbounded Davis--Kahan `sin Θ` endpoint

This module records the domain data required to derive the complementary block
Sylvester equation and the complete generalized theorem.  The final headline
form is a specialization to an isometric trial map.
-/

namespace ForMathlib
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

abbrev ClosedOperatorAmbient :=
  ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := E)
abbrev ClosedOperatorTrial :=
  ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := F)
abbrev ClosedOperatorComplement :=
  ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := G)

/-- Paper-shaped data for the unbounded residual theorem. -/
structure UnboundedSinThetaData where
  A : ClosedOperatorAmbient (𝕜 := 𝕜) (E := E)
  A₀ : ClosedOperatorTrial (𝕜 := 𝕜) (F := F)
  Λ₁ : ClosedOperatorComplement (𝕜 := 𝕜) (G := G)
  X : F →L[𝕜] E
  F₁ : G →L[𝕜] E
  residual : F →L[𝕜] E
  X_maps_domain : ∀ x : A₀.domain, X (x : F) ∈ A.domain
  F₁_maps_domain : ∀ y : Λ₁.domain, F₁ (y : G) ∈ A.domain
  residual_eq : ∀ x : A₀.domain,
    A.toLinearMap ⟨X (x : F), X_maps_domain x⟩ -
      X (A₀.toLinearMap x) = residual (x : F)
  intertwines : ∀ y : Λ₁.domain,
    A.toLinearMap ⟨F₁ (y : G), F₁_maps_domain y⟩ =
      F₁ (Λ₁.toLinearMap y)

/-- The residual identity induces the domain-aware complementary Sylvester equation. -/
theorem unbounded_adjoint_residual_block_identity
    (D : UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := G))
    (hA : D.A.IsSelfAdjoint)
    (hA₀ : D.A₀.IsSelfAdjoint)
    (hΛ₁ : D.Λ₁.IsSelfAdjoint) :
    HasClosedSylvesterEquation D.A₀ D.Λ₁
      (D.X.adjoint ∘L D.F₁)
      (D.residual.adjoint ∘L D.F₁) := by
  sorry

/-- Complete generalized unbounded Davis--Kahan `sin Θ` theorem. -/
theorem generalizedSinTheta_unbounded
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    (D : UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := G))
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
  sorry

/-- Isometric headline specialization of the unbounded theorem. -/
theorem sinTheta_unbounded
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    (D : UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := G))
    (hA : D.A.IsSelfAdjoint)
    (hA₀ : D.A₀.IsSelfAdjoint)
    (hΛ₁ : D.Λ₁.IsSelfAdjoint)
    (hX : IsometricEmbedding D.X)
    (hF₁ : IsometricEmbedding D.F₁)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hgap : UnboundedIntervalExteriorGap D.A₀ D.Λ₁ β α δ)
    (hR : N.Mem D.residual) :
    N.Mem (D.X.adjoint ∘L D.F₁) ∧
      δ * N.gauge (D.X.adjoint ∘L D.F₁)
        ≤ N.gauge D.residual := by
  sorry

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib

/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import ForMathlib.Analysis.InnerProductSpace.DavisKahan.Experimental.ExactSinTheta.BoundedSinTheta
import ForMathlib.Analysis.InnerProductSpace.DavisKahan.Experimental.ExactSinTheta.UnboundedSylvester

/-!
# Unbounded Davis--Kahan `sin Θ` endpoints

The finite-interval endpoint and the genuinely two-unbounded ordered endpoint
are distinct.  The unified endpoint uses `UnboundedSylvesterGap`, whose ordered
constructors cover both half-line orientations.  Exact-angle statements also
require a complete orthogonal decomposition of the ambient exact space.
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

/-- The residual identity induces the domain-aware complementary Sylvester
equation.  The right-hand side has a minus sign:
`A₀ X*F₁ - X*F₁ Λ₁ = -R*F₁`. -/
theorem unbounded_adjoint_residual_block_identity
    (D : UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := G))
    (hA : D.A.IsSelfAdjoint)
    (hA₀ : D.A₀.IsSelfAdjoint)
    (hΛ₁ : D.Λ₁.IsSelfAdjoint) :
    HasClosedSylvesterEquation D.A₀ D.Λ₁
      (D.X.adjoint ∘L D.F₁)
      (-(D.residual.adjoint ∘L D.F₁)) := by
  sorry

/-- Generalized finite-interval/exterior endpoint.  At least one diagonal block
has bounded spectrum, so this is not the fully two-unbounded theorem. -/
theorem generalizedSinTheta_unbounded_of_intervalExteriorGap
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

/-- Isometric finite-interval/exterior specialization. -/
theorem sinTheta_unbounded_of_intervalExteriorGap
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

/-- Exact generalized finite-interval/exterior endpoint, with the full
directed sine identified by a complete orthogonal exact-space decomposition. -/
theorem generalizedSinTheta_unbounded_exact_of_intervalExteriorGap
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    (D : UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := G))
    (F₀ : H →L[𝕜] E)
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
  sorry

/-- Exact isometric finite-interval/exterior endpoint. -/
theorem sinTheta_unbounded_exact_of_intervalExteriorGap
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
  sorry

/-- Complete generalized unbounded complementary-block theorem.  The gap may
be finite interval/exterior or either ordered half-line orientation. -/
theorem generalizedSinTheta_unbounded
    (N : UnitaryInvariantIdealFamily (𝕜 := 𝕜))
    (D : UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := G))
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
  sorry

/-- Isometric headline specialization of the complete unbounded block theorem. -/
theorem sinTheta_unbounded
    (N : UnitaryInvariantIdealFamily (𝕜 := 𝕜))
    (D : UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := G))
    (hA : D.A.IsSelfAdjoint)
    (hA₀ : D.A₀.IsSelfAdjoint)
    (hΛ₁ : D.Λ₁.IsSelfAdjoint)
    (hX : IsometricEmbedding D.X)
    (hF₁ : IsometricEmbedding D.F₁)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : UnboundedSylvesterGap D.A₀ D.Λ₁ δ)
    (hR : N.toRectangularSymmetricIdealFamily.Mem D.residual) :
    N.toRectangularSymmetricIdealFamily.Mem (D.X.adjoint ∘L D.F₁) ∧
      δ * N.toRectangularSymmetricIdealFamily.gauge (D.X.adjoint ∘L D.F₁)
        ≤ N.toRectangularSymmetricIdealFamily.gauge D.residual := by
  sorry

/-- Exact complete generalized unbounded Davis--Kahan theorem, with the full
directed sine operator identified through a complete orthogonal exact-space
decomposition. -/
theorem generalizedSinTheta_unbounded_exact
    (N : UnitaryInvariantIdealFamily (𝕜 := 𝕜))
    (D : UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := G))
    (F₀ : H →L[𝕜] E)
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
  sorry

/-- Exact isometric headline specialization of the complete unbounded theorem. -/
theorem sinTheta_unbounded_exact
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
  sorry

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib

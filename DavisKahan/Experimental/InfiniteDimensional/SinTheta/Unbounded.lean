/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.Bounded
import DavisKahan.Experimental.InfiniteDimensional.Sylvester.Unbounded

/-!
# Unbounded Davis--Kahan `sin Θ` endpoints

The domain calculation is the essential new step.  The bounded residual
identity implies that `X⋆F₁` maps the domain of the complementary exact block
into the domain of the trial block.  Self-adjointness identifies the adjoint
domains, yielding the strong Sylvester equation

`A₀ X⋆F₁ - X⋆F₁ Λ₁ = -R⋆F₁`.

The remaining proof is the unbounded Sylvester theorem followed by the same
lower-frame normalization and exact-space identification as in the bounded
case.
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

/-- Domain membership of the adjoint overlap. -/
theorem adjointOverlap_mem_trialDomain
    (D : UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := G))
    (hA : D.A.IsSelfAdjoint) (hA₀ : D.A₀.IsSelfAdjoint)
    (y : D.Λ₁.domain) :
    (D.X.adjoint ∘L D.F₁) (y : G) ∈ D.A₀.domain := by
  let z : F :=
    (D.X.adjoint ∘L D.F₁) (D.Λ₁.toLinearMap y) -
      (D.residual.adjoint ∘L D.F₁) (y : G)
  have hfunctional : ∀ x : D.A₀.domain,
      ⟪D.A₀.toLinearMap x,
        (D.X.adjoint ∘L D.F₁) (y : G)⟫_𝕜 =
      ⟪(x : F), z⟫_𝕜 := by
    intro x
    rw [ContinuousLinearMap.comp_apply,
      ← D.X.adjoint_inner_left, ← D.F₁.adjoint_inner_right]
    have hres := D.residual_eq x
    have hint := D.intertwines y
    calc
      ⟪D.X (D.A₀.toLinearMap x), D.F₁ (y : G)⟫_𝕜
          = ⟪D.A.toLinearMap ⟨D.X (x : F), D.X_maps_domain x⟩ -
                D.residual (x : F), D.F₁ (y : G)⟫_𝕜 := by rw [← hres]
      _ = ⟪D.X (x : F),
              D.A.toLinearMap ⟨D.F₁ (y : G), D.F₁_maps_domain y⟩⟫_𝕜 -
            ⟪D.residual (x : F), D.F₁ (y : G)⟫_𝕜 := by
              rw [inner_sub_left, hA.inner_left]
      _ = ⟪D.X (x : F), D.F₁ (D.Λ₁.toLinearMap y)⟫_𝕜 -
            ⟪D.residual (x : F), D.F₁ (y : G)⟫_𝕜 := by rw [hint]
      _ = ⟪(x : F), z⟫_𝕜 := by
            simp [z, ContinuousLinearMap.adjoint_inner_right]
  have hadj : (D.X.adjoint ∘L D.F₁) (y : G) ∈ D.A₀.adjoint.domain :=
    D.A₀.mem_adjointDomain_of_exists z hfunctional
  simpa [hA₀] using hadj

/-- The residual identity induces the domain-aware complementary Sylvester equation. -/
theorem unbounded_adjoint_residual_block_identity
    (D : UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := G))
    (hA : D.A.IsSelfAdjoint)
    (hA₀ : D.A₀.IsSelfAdjoint)
    (hΛ₁ : D.Λ₁.IsSelfAdjoint) :
    HasClosedSylvesterEquation D.A₀ D.Λ₁
      (D.X.adjoint ∘L D.F₁)
      (-(D.residual.adjoint ∘L D.F₁)) := by
  intro y
  let hy := adjointOverlap_mem_trialDomain D hA hA₀ y
  refine ⟨hy, ?_⟩
  apply ext_inner_right 𝕜
  intro x
  have hfunctional := D.A₀.adjointVector_inner
    ((D.X.adjoint ∘L D.F₁) (y : G)) x
  have hres := D.residual_eq x
  have hint := D.intertwines y
  simp only [ContinuousLinearMap.comp_apply, neg_apply]
  calc
    ⟪D.A₀.toLinearMap ⟨(D.X.adjoint ∘L D.F₁) (y : G), hy⟩ -
        (D.X.adjoint ∘L D.F₁) (D.Λ₁.toLinearMap y), (x : F)⟫_𝕜
        = -⟪D.F₁ (y : G), D.residual (x : F)⟫_𝕜 := by
          rw [inner_sub_left, hA₀.inner_left]
          simp [ContinuousLinearMap.adjoint_inner_left,
            D.residual_eq, D.intertwines, hA.inner_left]
    _ = ⟪-(D.residual.adjoint ∘L D.F₁) (y : G), (x : F)⟫_𝕜 := by
          simp [ContinuousLinearMap.adjoint_inner_left]

/-- The unbounded complementary residual belongs to the ideal without gauge growth. -/
theorem unboundedComplementaryResidual_mem_and_gauge_le
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    (D : UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := G))
    (hF₁ : IsometricEmbedding D.F₁)
    (hR : N.Mem D.residual) :
    N.Mem (-(D.residual.adjoint ∘L D.F₁)) ∧
      N.gauge (-(D.residual.adjoint ∘L D.F₁)) ≤ N.gauge D.residual := by
  exact complementaryResidual_mem_and_gauge_le N hF₁ hR

/-- Generalized finite-interval/exterior endpoint. -/
theorem generalizedSinTheta_unbounded_of_intervalExteriorGap
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    (D : UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := G))
    (hA : D.A.IsSelfAdjoint) (hA₀ : D.A₀.IsSelfAdjoint)
    (hΛ₁ : D.Λ₁.IsSelfAdjoint) (hF₁ : IsometricEmbedding D.F₁)
    {β α δ ε : ℝ}
    (hβα : β ≤ α) (hδ : 0 < δ) (hε : 0 < ε)
    (hframe : LowerFrameBound D.X ε)
    (hgap : UnboundedIntervalExteriorGap D.A₀ D.Λ₁ β α δ)
    (hR : N.Mem D.residual) :
    N.Mem (sinThetaBlock D.X D.F₁ hframe hε) ∧
      δ * ε * N.gauge (sinThetaBlock D.X D.F₁ hframe hε) ≤
        N.gauge D.residual := by
  have hEq := unbounded_adjoint_residual_block_identity D hA hA₀ hΛ₁
  have hC := unboundedComplementaryResidual_mem_and_gauge_le N D hF₁ hR
  have hraw := unbounded_sylvester_mem_and_gauge_le_of_intervalExteriorGap
    N hA₀ hΛ₁ hβα hδ hgap hEq hC.1
  have hnormalize := lowerFrame_sinThetaBlock_mem_and_gauge_le
    N D.X D.F₁ hframe hε hraw.1
  refine ⟨hnormalize.1, ?_⟩
  calc
    δ * ε * N.gauge (sinThetaBlock D.X D.F₁ hframe hε)
        = δ * (ε * N.gauge (sinThetaBlock D.X D.F₁ hframe hε)) := by ring
    _ ≤ δ * N.gauge (D.X.adjoint ∘L D.F₁) :=
      mul_le_mul_of_nonneg_left hnormalize.2 hδ.le
    _ ≤ N.gauge (-(D.residual.adjoint ∘L D.F₁)) := hraw.2
    _ ≤ N.gauge D.residual := hC.2

/-- Isometric finite-interval/exterior specialization. -/
theorem sinTheta_unbounded_of_intervalExteriorGap
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    (D : UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := G))
    (hA : D.A.IsSelfAdjoint) (hA₀ : D.A₀.IsSelfAdjoint)
    (hΛ₁ : D.Λ₁.IsSelfAdjoint)
    (hX : IsometricEmbedding D.X) (hF₁ : IsometricEmbedding D.F₁)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hgap : UnboundedIntervalExteriorGap D.A₀ D.Λ₁ β α δ)
    (hR : N.Mem D.residual) :
    N.Mem (D.X.adjoint ∘L D.F₁) ∧
      δ * N.gauge (D.X.adjoint ∘L D.F₁) ≤ N.gauge D.residual := by
  have hEq := unbounded_adjoint_residual_block_identity D hA hA₀ hΛ₁
  have hC := unboundedComplementaryResidual_mem_and_gauge_le N D hF₁ hR
  have hraw := unbounded_sylvester_mem_and_gauge_le_of_intervalExteriorGap
    N hA₀ hΛ₁ hβα hδ hgap hEq hC.1
  exact ⟨hraw.1, hraw.2.trans hC.2⟩

/-- Exact generalized finite-interval/exterior endpoint. -/
theorem generalizedSinTheta_unbounded_exact_of_intervalExteriorGap
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    (D : UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := G))
    (F₀ : H →L[𝕜] E)
    (hA : D.A.IsSelfAdjoint) (hA₀ : D.A₀.IsSelfAdjoint)
    (hΛ₁ : D.Λ₁.IsSelfAdjoint)
    (hdecomp : OrthogonalExactDecomposition F₀ D.F₁)
    {β α δ ε : ℝ}
    (hβα : β ≤ α) (hδ : 0 < δ) (hε : 0 < ε)
    (hframe : LowerFrameBound D.X ε)
    (hgap : UnboundedIntervalExteriorGap D.A₀ D.Λ₁ β α δ)
    (hR : N.Mem D.residual) :
    N.Mem (directedSinThetaOperator D.X F₀ hframe hε) ∧
      δ * ε * N.gauge (directedSinThetaOperator D.X F₀ hframe hε) ≤
        N.gauge D.residual := by
  have hblock := generalizedSinTheta_unbounded_of_intervalExteriorGap
    N D hA hA₀ hΛ₁ hdecomp.isometry₁ hβα hδ hε hframe hgap hR
  have hid := sinThetaBlock_mem_and_gauge_eq_directedSinThetaOperator
    N D.X F₀ D.F₁ hframe hε hdecomp hblock.1
  exact ⟨hid.1, by simpa [hid.2] using hblock.2⟩

/-- Exact isometric finite-interval/exterior endpoint. -/
theorem sinTheta_unbounded_exact_of_intervalExteriorGap
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    (D : UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := G))
    (F₀ : H →L[𝕜] E)
    (hA : D.A.IsSelfAdjoint) (hA₀ : D.A₀.IsSelfAdjoint)
    (hΛ₁ : D.Λ₁.IsSelfAdjoint)
    (hX : IsometricEmbedding D.X)
    (hdecomp : OrthogonalExactDecomposition F₀ D.F₁)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hgap : UnboundedIntervalExteriorGap D.A₀ D.Λ₁ β α δ)
    (hR : N.Mem D.residual) :
    N.Mem ((ContinuousLinearMap.id 𝕜 E - F₀ ∘L F₀.adjoint) ∘L D.X) ∧
      δ * N.gauge
        ((ContinuousLinearMap.id 𝕜 E - F₀ ∘L F₀.adjoint) ∘L D.X) ≤
        N.gauge D.residual := by
  let hframe := lowerFrameBound_one_of_isometricEmbedding hX
  have h := generalizedSinTheta_unbounded_exact_of_intervalExteriorGap
    N D F₀ hA hA₀ hΛ₁ hdecomp hβα hδ zero_lt_one hframe hgap hR
  have hQ := frameIsometry_eq_of_isometricEmbedding hX
  simpa [directedSinThetaOperator, hQ] using h

/-- Complete generalized unbounded complementary-block theorem. -/
theorem generalizedSinTheta_unbounded
    (N : UnitaryInvariantIdealFamily (𝕜 := 𝕜))
    (D : UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := G))
    (hA : D.A.IsSelfAdjoint) (hA₀ : D.A₀.IsSelfAdjoint)
    (hΛ₁ : D.Λ₁.IsSelfAdjoint) (hF₁ : IsometricEmbedding D.F₁)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hframe : LowerFrameBound D.X ε)
    (hgap : UnboundedSylvesterGap D.A₀ D.Λ₁ δ)
    (hR : N.toRectangularSymmetricIdealFamily.Mem D.residual) :
    N.toRectangularSymmetricIdealFamily.Mem
      (sinThetaBlock D.X D.F₁ hframe hε) ∧
      δ * ε * N.toRectangularSymmetricIdealFamily.gauge
        (sinThetaBlock D.X D.F₁ hframe hε) ≤
        N.toRectangularSymmetricIdealFamily.gauge D.residual := by
  let M := N.toRectangularSymmetricIdealFamily
  have hEq := unbounded_adjoint_residual_block_identity D hA hA₀ hΛ₁
  have hC := unboundedComplementaryResidual_mem_and_gauge_le M D hF₁ hR
  have hraw := unbounded_sylvester_mem_and_gauge_le_of_gap
    N hA₀ hΛ₁ hδ hgap hEq hC.1
  have hnormalize := lowerFrame_sinThetaBlock_mem_and_gauge_le
    M D.X D.F₁ hframe hε hraw.1
  refine ⟨hnormalize.1, ?_⟩
  calc
    δ * ε * M.gauge (sinThetaBlock D.X D.F₁ hframe hε)
        = δ * (ε * M.gauge (sinThetaBlock D.X D.F₁ hframe hε)) := by ring
    _ ≤ δ * M.gauge (D.X.adjoint ∘L D.F₁) :=
      mul_le_mul_of_nonneg_left hnormalize.2 hδ.le
    _ ≤ M.gauge (-(D.residual.adjoint ∘L D.F₁)) := hraw.2
    _ ≤ M.gauge D.residual := hC.2

/-- Isometric headline specialization of the complete unbounded block theorem. -/
theorem sinTheta_unbounded
    (N : UnitaryInvariantIdealFamily (𝕜 := 𝕜))
    (D : UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := G))
    (hA : D.A.IsSelfAdjoint) (hA₀ : D.A₀.IsSelfAdjoint)
    (hΛ₁ : D.Λ₁.IsSelfAdjoint)
    (hX : IsometricEmbedding D.X) (hF₁ : IsometricEmbedding D.F₁)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : UnboundedSylvesterGap D.A₀ D.Λ₁ δ)
    (hR : N.toRectangularSymmetricIdealFamily.Mem D.residual) :
    N.toRectangularSymmetricIdealFamily.Mem (D.X.adjoint ∘L D.F₁) ∧
      δ * N.toRectangularSymmetricIdealFamily.gauge
        (D.X.adjoint ∘L D.F₁) ≤
        N.toRectangularSymmetricIdealFamily.gauge D.residual := by
  let M := N.toRectangularSymmetricIdealFamily
  have hEq := unbounded_adjoint_residual_block_identity D hA hA₀ hΛ₁
  have hC := unboundedComplementaryResidual_mem_and_gauge_le M D hF₁ hR
  have hraw := unbounded_sylvester_mem_and_gauge_le_of_gap
    N hA₀ hΛ₁ hδ hgap hEq hC.1
  exact ⟨hraw.1, hraw.2.trans hC.2⟩

/-- Exact complete generalized unbounded Davis--Kahan theorem. -/
theorem generalizedSinTheta_unbounded_exact
    (N : UnitaryInvariantIdealFamily (𝕜 := 𝕜))
    (D : UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := G))
    (F₀ : H →L[𝕜] E)
    (hA : D.A.IsSelfAdjoint) (hA₀ : D.A₀.IsSelfAdjoint)
    (hΛ₁ : D.Λ₁.IsSelfAdjoint)
    (hdecomp : OrthogonalExactDecomposition F₀ D.F₁)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hframe : LowerFrameBound D.X ε)
    (hgap : UnboundedSylvesterGap D.A₀ D.Λ₁ δ)
    (hR : N.toRectangularSymmetricIdealFamily.Mem D.residual) :
    N.toRectangularSymmetricIdealFamily.Mem
      (directedSinThetaOperator D.X F₀ hframe hε) ∧
      δ * ε * N.toRectangularSymmetricIdealFamily.gauge
        (directedSinThetaOperator D.X F₀ hframe hε) ≤
        N.toRectangularSymmetricIdealFamily.gauge D.residual := by
  have hblock := generalizedSinTheta_unbounded
    N D hA hA₀ hΛ₁ hdecomp.isometry₁ hδ hε hframe hgap hR
  have hid := sinThetaBlock_mem_and_gauge_eq_directedSinThetaOperator
    N.toRectangularSymmetricIdealFamily D.X F₀ D.F₁
      hframe hε hdecomp hblock.1
  exact ⟨hid.1, by simpa [hid.2] using hblock.2⟩

/-- Exact isometric headline specialization of the complete unbounded theorem. -/
theorem sinTheta_unbounded_exact
    (N : UnitaryInvariantIdealFamily (𝕜 := 𝕜))
    (D : UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := G))
    (F₀ : H →L[𝕜] E)
    (hA : D.A.IsSelfAdjoint) (hA₀ : D.A₀.IsSelfAdjoint)
    (hΛ₁ : D.Λ₁.IsSelfAdjoint)
    (hX : IsometricEmbedding D.X)
    (hdecomp : OrthogonalExactDecomposition F₀ D.F₁)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : UnboundedSylvesterGap D.A₀ D.Λ₁ δ)
    (hR : N.toRectangularSymmetricIdealFamily.Mem D.residual) :
    N.toRectangularSymmetricIdealFamily.Mem
      ((ContinuousLinearMap.id 𝕜 E - F₀ ∘L F₀.adjoint) ∘L D.X) ∧
      δ * N.toRectangularSymmetricIdealFamily.gauge
        ((ContinuousLinearMap.id 𝕜 E - F₀ ∘L F₀.adjoint) ∘L D.X) ≤
        N.toRectangularSymmetricIdealFamily.gauge D.residual := by
  let hframe := lowerFrameBound_one_of_isometricEmbedding hX
  have h := generalizedSinTheta_unbounded_exact
    N D F₀ hA hA₀ hΛ₁ hdecomp hδ zero_lt_one hframe hgap hR
  have hQ := frameIsometry_eq_of_isometricEmbedding hX
  simpa [directedSinThetaOperator, hQ] using h

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib

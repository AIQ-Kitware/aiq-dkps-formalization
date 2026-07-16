/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.Bounded
import DavisKahan.Experimental.InfiniteDimensional.Sylvester.Unbounded

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
    (_hΛ₁ : D.Λ₁.IsSelfAdjoint) :
    HasClosedSylvesterEquation D.A₀ D.Λ₁
      (D.X.adjoint ∘L D.F₁)
      (-(D.residual.adjoint ∘L D.F₁)) := by
  have hA_symm := hA.isSymmetric
  have hA₀P : D.A₀.toLinearPMap.adjoint = D.A₀.toLinearPMap :=
    (D.A₀.isSelfAdjoint_iff_toLinearPMap_adjoint_eq).mp hA₀
  refine ⟨?_, ?_⟩
  · intro y
    let z : F := D.X.adjoint (D.F₁ (y : G))
    let w : F :=
      D.X.adjoint (D.F₁ (D.Λ₁.toLinearMap y)) -
        D.residual.adjoint (D.F₁ (y : G))
    have hw : ∀ x : D.A₀.domain,
        ⟪w, (x : F)⟫_𝕜 = ⟪z, D.A₀.toLinearMap x⟫_𝕜 := by
      intro x
      let Fx : D.A.domain := ⟨D.X (x : F), D.X_maps_domain x⟩
      let Fy : D.A.domain := ⟨D.F₁ (y : G), D.F₁_maps_domain y⟩
      calc
        ⟪w, (x : F)⟫_𝕜 =
            ⟪D.F₁ (D.Λ₁.toLinearMap y), D.X (x : F)⟫_𝕜 -
              ⟪D.F₁ (y : G), D.residual (x : F)⟫_𝕜 := by
          rw [inner_sub_left,
            D.X.adjoint_inner_left (x : F) (D.F₁ (D.Λ₁.toLinearMap y)),
            D.residual.adjoint_inner_left (x : F) (D.F₁ (y : G))]
        _ = ⟪D.A.toLinearMap Fy, D.X (x : F)⟫_𝕜 -
              ⟪D.F₁ (y : G), D.residual (x : F)⟫_𝕜 := by
          rw [← D.intertwines y]
        _ = ⟪D.F₁ (y : G), D.A.toLinearMap Fx⟫_𝕜 -
              ⟪D.F₁ (y : G), D.residual (x : F)⟫_𝕜 := by
          rw [hA_symm Fy Fx]
        _ = ⟪D.F₁ (y : G), D.X (D.A₀.toLinearMap x)⟫_𝕜 := by
          rw [← D.residual_eq x, inner_sub_right]
          abel
        _ = ⟪z, D.A₀.toLinearMap x⟫_𝕜 := by
          rw [← D.X.adjoint_inner_left (D.A₀.toLinearMap x) (D.F₁ (y : G))]
    have hzAdj : z ∈ D.A₀.toLinearPMap.adjoint.domain :=
      LinearPMap.mem_adjoint_domain_of_exists z ⟨w, hw⟩
    have hdom : D.A₀.toLinearPMap.adjoint.domain = D.A₀.domain :=
      congrArg LinearPMap.domain hA₀P
    exact hdom ▸ hzAdj
  · intro y
    let z : F := D.X.adjoint (D.F₁ (y : G))
    let w : F :=
      D.X.adjoint (D.F₁ (D.Λ₁.toLinearMap y)) -
        D.residual.adjoint (D.F₁ (y : G))
    have hw : ∀ x : D.A₀.domain,
        ⟪w, (x : F)⟫_𝕜 = ⟪z, D.A₀.toLinearMap x⟫_𝕜 := by
      intro x
      let Fx : D.A.domain := ⟨D.X (x : F), D.X_maps_domain x⟩
      let Fy : D.A.domain := ⟨D.F₁ (y : G), D.F₁_maps_domain y⟩
      calc
        ⟪w, (x : F)⟫_𝕜 =
            ⟪D.F₁ (D.Λ₁.toLinearMap y), D.X (x : F)⟫_𝕜 -
              ⟪D.F₁ (y : G), D.residual (x : F)⟫_𝕜 := by
          rw [inner_sub_left,
            D.X.adjoint_inner_left (x : F) (D.F₁ (D.Λ₁.toLinearMap y)),
            D.residual.adjoint_inner_left (x : F) (D.F₁ (y : G))]
        _ = ⟪D.A.toLinearMap Fy, D.X (x : F)⟫_𝕜 -
              ⟪D.F₁ (y : G), D.residual (x : F)⟫_𝕜 := by
          rw [← D.intertwines y]
        _ = ⟪D.F₁ (y : G), D.A.toLinearMap Fx⟫_𝕜 -
              ⟪D.F₁ (y : G), D.residual (x : F)⟫_𝕜 := by
          rw [hA_symm Fy Fx]
        _ = ⟪D.F₁ (y : G), D.X (D.A₀.toLinearMap x)⟫_𝕜 := by
          rw [← D.residual_eq x, inner_sub_right]
          abel
        _ = ⟪z, D.A₀.toLinearMap x⟫_𝕜 := by
          rw [← D.X.adjoint_inner_left (D.A₀.toLinearMap x) (D.F₁ (y : G))]
    have hzAdj : z ∈ D.A₀.toLinearPMap.adjoint.domain :=
      LinearPMap.mem_adjoint_domain_of_exists z ⟨w, hw⟩
    have hdom : D.A₀.toLinearPMap.adjoint.domain = D.A₀.domain :=
      congrArg LinearPMap.domain hA₀P
    have hzDom : z ∈ D.A₀.domain := hdom ▸ hzAdj
    have hA₀z : D.A₀.toLinearMap ⟨z, hzDom⟩ = w := by
      have hinner :
          (fun x : F => ⟪D.A₀.toLinearMap ⟨z, hzDom⟩, x⟫_𝕜) =
            fun x : F => ⟪w, x⟫_𝕜 := by
        apply Continuous.ext_on D.A₀.dense_domain
        · exact continuous_const.inner continuous_id
        · exact continuous_const.inner continuous_id
        · intro x hx
          let xDom : D.A₀.domain := ⟨x, hx⟩
          calc
            ⟪D.A₀.toLinearMap ⟨z, hzDom⟩, x⟫_𝕜 =
                ⟪z, D.A₀.toLinearMap xDom⟫_𝕜 := hA₀.isSymmetric ⟨z, hzDom⟩ xDom
            _ = ⟪w, x⟫_𝕜 := (hw xDom).symm
      have hzero :
          ⟪D.A₀.toLinearMap ⟨z, hzDom⟩ - w,
            D.A₀.toLinearMap ⟨z, hzDom⟩ - w⟫_𝕜 = 0 := by
        rw [inner_sub_left,
          congrFun hinner (D.A₀.toLinearMap ⟨z, hzDom⟩ - w), sub_self]
      exact sub_eq_zero.mp (inner_self_eq_zero.mp hzero)
    change D.A₀.toLinearMap ⟨z, hzDom⟩ -
        D.X.adjoint (D.F₁ (D.Λ₁.toLinearMap y)) =
      -D.residual.adjoint (D.F₁ (y : G))
    rw [hA₀z]
    unfold w
    abel

/-- The projected residual block remains in the same rectangular ideal and its
 gauge is no larger than the original residual gauge. -/
theorem adjointResidualBlock_mem_and_gauge_le
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    (D : UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := G))
    (hF₁ : IsometricEmbedding D.F₁)
    (hR : N.Mem D.residual) :
    N.Mem (-(D.residual.adjoint ∘L D.F₁)) ∧
      N.gauge (-(D.residual.adjoint ∘L D.F₁)) ≤
        N.gauge D.residual := by
  have hAdj : N.Mem D.residual.adjoint := N.adjoint_mem hR
  have hComp : N.Mem (D.residual.adjoint ∘L D.F₁) :=
    N.comp_right_mem D.F₁ hAdj
  refine ⟨N.neg_mem hComp, ?_⟩
  calc
    N.gauge (-(D.residual.adjoint ∘L D.F₁))
        = N.gauge (D.residual.adjoint ∘L D.F₁) := N.gauge_neg hComp
    _ ≤ N.gauge D.residual.adjoint :=
      N.gauge_comp_right_le D.F₁ hAdj (opNorm_le_one_of_isometry hF₁)
    _ = N.gauge D.residual := N.gauge_adjoint hR

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

/-- Isometric finite-interval/exterior specialization. -/
theorem sinTheta_unbounded_of_intervalExteriorGap
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
  have hBlock := generalizedSinTheta_unbounded_of_intervalExteriorGap
    N D hA hA₀ hΛ₁ hdecomp.isometry₁ hβα hδ hε hframe hgap hR
  have hAngle := sinThetaBlock_mem_and_gauge_eq_directedSinThetaOperator
    N D.X F₀ D.F₁ hframe hε hdecomp hBlock.1
  refine ⟨hAngle.1, ?_⟩
  rw [hAngle.2]
  exact hBlock.2

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
  have hframe := lowerFrameBound_one_of_isometry hX
  have hGeneral := generalizedSinTheta_unbounded_exact_of_intervalExteriorGap
    N D F₀ hA hA₀ hΛ₁ hdecomp hβα hδ zero_lt_one hframe hgap hR
  rw [directedSinThetaOperator_eq_of_isometry D.X F₀ hX] at hGeneral
  simpa using hGeneral

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

/-- Isometric headline specialization of the complete unbounded block theorem. -/
theorem sinTheta_unbounded
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
  let M := N.toRectangularSymmetricIdealFamily
  have hBlock := generalizedSinTheta_unbounded
    N D hA hA₀ hΛ₁ hdecomp.isometry₁ hδ hε hframe hgap hR
  have hAngle := sinThetaBlock_mem_and_gauge_eq_directedSinThetaOperator
    M D.X F₀ D.F₁ hframe hε hdecomp hBlock.1
  refine ⟨hAngle.1, ?_⟩
  rw [hAngle.2]
  exact hBlock.2

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
  have hframe := lowerFrameBound_one_of_isometry hX
  have hGeneral := generalizedSinTheta_unbounded_exact
    N D F₀ hA hA₀ hΛ₁ hdecomp hδ zero_lt_one hframe hgap hR
  rw [directedSinThetaOperator_eq_of_isometry D.X F₀ hX] at hGeneral
  simpa using hGeneral

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib

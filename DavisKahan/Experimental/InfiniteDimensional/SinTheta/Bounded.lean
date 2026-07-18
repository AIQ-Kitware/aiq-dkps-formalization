/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.SpectralBridge
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.FrameFactorization

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

section Generic

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

omit [CompleteSpace G] in
/-- Adjoint residual block identity used by the generalized theorem. -/
theorem adjoint_residual_block_identity
    {A : E →L[𝕜] E} {A₀ : F →L[𝕜] F}
    {Λ₁ : G →L[𝕜] G} {X : F →L[𝕜] E}
    {F₁ : G →L[𝕜] E}
    (hA : A.IsSymmetric) (hA₀ : A₀.IsSymmetric)
    (_hΛ₁ : Λ₁.IsSymmetric)
    (hIntertwine : A ∘L F₁ = F₁ ∘L Λ₁) :
    (generalResidual A X A₀).adjoint ∘L F₁ =
      (X.adjoint ∘L F₁) ∘L Λ₁ -
        A₀ ∘L (X.adjoint ∘L F₁) := by
  ext y
  refine ext_inner_right 𝕜 fun x => ?_
  have hInt : A (F₁ y) = F₁ (Λ₁ y) := by
    have h := congrArg (fun T : G →L[𝕜] E => T y) hIntertwine
    simpa only [ContinuousLinearMap.comp_apply] using h
  calc
    ⟪((generalResidual A X A₀).adjoint ∘L F₁) y, x⟫_𝕜
        = ⟪F₁ y, generalResidual A X A₀ x⟫_𝕜 := by
            rw [ContinuousLinearMap.comp_apply,
              (generalResidual A X A₀).adjoint_inner_left x (F₁ y)]
    _ = ⟪F₁ y, A (X x)⟫_𝕜 - ⟪F₁ y, X (A₀ x)⟫_𝕜 := by
          simp only [generalResidual, ContinuousLinearMap.comp_apply, sub_apply,
            inner_sub_right]
    _ = ⟪A (F₁ y), X x⟫_𝕜 - ⟪F₁ y, X (A₀ x)⟫_𝕜 := by
          exact congrArg
            (fun z : 𝕜 => z - ⟪F₁ y, X (A₀ x)⟫_𝕜)
            (hA (F₁ y) (X x)).symm
    _ = ⟪F₁ (Λ₁ y), X x⟫_𝕜 - ⟪F₁ y, X (A₀ x)⟫_𝕜 := by
          rw [hInt]
    _ = ⟪X.adjoint (F₁ (Λ₁ y)), x⟫_𝕜 -
          ⟪X.adjoint (F₁ y), A₀ x⟫_𝕜 := by
          rw [← X.adjoint_inner_left x (F₁ (Λ₁ y)),
            ← X.adjoint_inner_left (A₀ x) (F₁ y)]
    _ = ⟪X.adjoint (F₁ (Λ₁ y)), x⟫_𝕜 -
          ⟪A₀ (X.adjoint (F₁ y)), x⟫_𝕜 := by
          exact congrArg
            (fun z : 𝕜 => ⟪X.adjoint (F₁ (Λ₁ y)), x⟫_𝕜 - z)
            (hA₀ (X.adjoint (F₁ y)) x).symm
    _ = ⟪(((X.adjoint ∘L F₁) ∘L Λ₁ -
          A₀ ∘L (X.adjoint ∘L F₁)) y), x⟫_𝕜 := by
          simp only [ContinuousLinearMap.comp_apply, sub_apply, inner_sub_left]

omit [CompleteSpace G] in
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
  rw [adjoint_residual_block_identity hA hA₀ hΛ₁ hIntertwine]
  abel

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
  have hEq := complementary_sylvester_equation
    (X := X) (F₁ := F₁) hA hA₀ hΛ₁ hIntertwine
  have hAdj : N.Mem (generalResidual A X A₀).adjoint := N.adjoint_mem hR
  have hComp : N.Mem ((generalResidual A X A₀).adjoint ∘L F₁) :=
    N.comp_right_mem F₁ hAdj
  have hC : N.Mem (-((generalResidual A X A₀).adjoint ∘L F₁)) :=
    N.neg_mem hComp
  have hRaw := sylvester_mem_and_gauge_le_of_intervalExteriorGap
    N hA₀ hΛ₁ hβα hδ hgap hEq hC
  refine ⟨hRaw.1, hRaw.2.trans ?_⟩
  calc
    N.gauge (-((generalResidual A X A₀).adjoint ∘L F₁))
        = N.gauge ((generalResidual A X A₀).adjoint ∘L F₁) :=
          N.gauge_neg hComp
    _ ≤ N.gauge (generalResidual A X A₀).adjoint :=
      N.gauge_comp_right_le F₁ hAdj (opNorm_le_one_of_isometry hF₁)
    _ = N.gauge (generalResidual A X A₀) := N.gauge_adjoint hR

/-- Isometric complementary-block specialization of the bounded theorem. -/
theorem sinTheta_bounded
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    {A : E →L[𝕜] E} {A₀ : F →L[𝕜] F}
    {Λ₁ : G →L[𝕜] G} {X : F →L[𝕜] E}
    {F₁ : G →L[𝕜] E}
    (hA : A.IsSymmetric) (hA₀ : A₀.IsSymmetric)
    (hΛ₁ : Λ₁.IsSymmetric)
    (_hX : IsometricEmbedding X) (hF₁ : IsometricEmbedding F₁)
    (hIntertwine : A ∘L F₁ = F₁ ∘L Λ₁)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hgap : IntervalExteriorGap A₀ Λ₁ β α δ)
    (hR : N.Mem (generalResidual A X A₀)) :
    N.Mem (X.adjoint ∘L F₁) ∧
      δ * N.gauge (X.adjoint ∘L F₁)
        ≤ N.gauge (generalResidual A X A₀) := by
  exact complementaryBlock_mem_and_gauge_le
    N hA hA₀ hΛ₁ hF₁ hIntertwine hβα hδ hgap hR

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

end Generic

section Complex

universe v

variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Bounded generalized complementary-block theorem.  This is the analytic
core of Theorem 6.1, before identifying the block with the full directed sine
of a complete exact-space decomposition. -/
theorem generalizedSinTheta_bounded
    (N : RectangularSymmetricIdealFamily (𝕜 := ℂ))
    {A : E →L[ℂ] E} {A₀ : F →L[ℂ] F}
    {Λ₁ : G →L[ℂ] G} {X : F →L[ℂ] E}
    {F₁ : G →L[ℂ] E}
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
  have hRaw := complementaryBlock_mem_and_gauge_le
    N hA hA₀ hΛ₁ hF₁ hIntertwine hβα hδ hgap hR
  have hFrame := lowerFrame_sinThetaBlock_mem_and_gauge_le
    N X F₁ hframe hε hRaw.1
  refine ⟨hFrame.1, ?_⟩
  calc
    δ * ε * N.gauge (sinThetaBlock X F₁ hframe hε)
        = δ * (ε * N.gauge (sinThetaBlock X F₁ hframe hε)) := by ring
    _ ≤ δ * N.gauge (X.adjoint ∘L F₁) :=
      mul_le_mul_of_nonneg_left hFrame.2 hδ.le
    _ ≤ N.gauge (generalResidual A X A₀) := hRaw.2

/-- Directed sine operator from the orthonormalized trial coordinates into the
orthogonal complement of the desired exact space. -/
noncomputable def directedSinThetaOperator
    (X : F →L[ℂ] E) (F₀ : H →L[ℂ] E) {ε : ℝ}
    (hX : LowerFrameBound X ε) (hε : 0 < ε) : F →L[ℂ] E :=
  (ContinuousLinearMap.id ℂ E - F₀ ∘L F₀.adjoint) ∘L
    frameIsometry X hX hε

/-- The directed sine operator of an isometric trial map is the direct
orthogonal-complement block of that map. -/
theorem directedSinThetaOperator_eq_of_isometry
    (X : F →L[ℂ] E) (F₀ : H →L[ℂ] E)
    (hX : IsometricEmbedding X) :
    directedSinThetaOperator X F₀
        (lowerFrameBound_one_of_isometry hX) zero_lt_one =
      (ContinuousLinearMap.id ℂ E - F₀ ∘L F₀.adjoint) ∘L X := by
  unfold directedSinThetaOperator
  exact congrArg
    (fun U : F →L[ℂ] E =>
      (ContinuousLinearMap.id ℂ E - F₀ ∘L F₀.adjoint) ∘L U)
    (frameIsometry_eq_of_isometry X hX)

/-- Under a complete orthogonal exact decomposition, the complementary overlap
block and the directed sine operator have the same ideal membership and gauge. -/
theorem sinThetaBlock_mem_and_gauge_eq_directedSinThetaOperator
    (N : RectangularSymmetricIdealFamily (𝕜 := ℂ))
    (X : F →L[ℂ] E) (F₀ : H →L[ℂ] E) (F₁ : G →L[ℂ] E)
    {ε : ℝ} (hX : LowerFrameBound X ε) (hε : 0 < ε)
    (hdecomp : OrthogonalExactDecomposition F₀ F₁)
    (hblock : N.Mem (sinThetaBlock X F₁ hX hε)) :
    N.Mem (directedSinThetaOperator X F₀ hX hε) ∧
      N.gauge (directedSinThetaOperator X F₀ hX hε) =
        N.gauge (sinThetaBlock X F₁ hX hε) := by
  have hComplement :
      ContinuousLinearMap.id ℂ E - F₀ ∘L F₀.adjoint =
        F₁ ∘L F₁.adjoint := by
    rw [← hdecomp.projection_sum]
    abel
  have hDirected :
      directedSinThetaOperator X F₀ hX hε =
        F₁ ∘L (sinThetaBlock X F₁ hX hε).adjoint := by
    unfold directedSinThetaOperator sinThetaBlock
    rw [hComplement, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint]
    exact ContinuousLinearMap.comp_assoc _ _ _
  have hblockAdj : N.Mem (sinThetaBlock X F₁ hX hε).adjoint :=
    N.adjoint_mem hblock
  have hDirectedMem :
      N.Mem (directedSinThetaOperator X F₀ hX hε) := by
    rw [hDirected]
    exact N.comp_left_mem F₁ hblockAdj
  have hF₁Norm : ‖F₁‖ ≤ 1 :=
    opNorm_le_one_of_isometry hdecomp.isometry₁
  have hForward :
      N.gauge (directedSinThetaOperator X F₀ hX hε) ≤
        N.gauge (sinThetaBlock X F₁ hX hε) := by
    rw [hDirected]
    calc
      N.gauge (F₁ ∘L (sinThetaBlock X F₁ hX hε).adjoint)
          ≤ N.gauge (sinThetaBlock X F₁ hX hε).adjoint :=
        N.gauge_comp_left_le F₁ hblockAdj hF₁Norm
      _ = N.gauge (sinThetaBlock X F₁ hX hε) :=
        N.gauge_adjoint hblock
  have hF₁LeftInverse :
      F₁.adjoint ∘L F₁ = ContinuousLinearMap.id ℂ G :=
    adjoint_comp_self_eq_id_of_isometry hdecomp.isometry₁
  have hRecover :
      (sinThetaBlock X F₁ hX hε).adjoint =
        F₁.adjoint ∘L directedSinThetaOperator X F₀ hX hε := by
    calc
      (sinThetaBlock X F₁ hX hε).adjoint =
          ContinuousLinearMap.id ℂ G ∘L
            (sinThetaBlock X F₁ hX hε).adjoint := by simp
      _ = (F₁.adjoint ∘L F₁) ∘L
            (sinThetaBlock X F₁ hX hε).adjoint := by
          rw [hF₁LeftInverse]
      _ = F₁.adjoint ∘L
            (F₁ ∘L (sinThetaBlock X F₁ hX hε).adjoint) :=
          ContinuousLinearMap.comp_assoc _ _ _
      _ = F₁.adjoint ∘L directedSinThetaOperator X F₀ hX hε := by
          rw [hDirected]
  have hF₁AdjNorm : ‖F₁.adjoint‖ ≤ 1 := by
    simpa using hF₁Norm
  have hReverse :
      N.gauge (sinThetaBlock X F₁ hX hε) ≤
        N.gauge (directedSinThetaOperator X F₀ hX hε) := by
    rw [← N.gauge_adjoint hblock, hRecover]
    exact N.gauge_comp_left_le F₁.adjoint hDirectedMem hF₁AdjNorm
  exact ⟨hDirectedMem, le_antisymm hForward hReverse⟩

/-- Exact bounded infinite-dimensional Davis--Kahan Theorem 6.1, expressed in
terms of the full directed sine operator rather than an arbitrary invariant
complementary block. -/
theorem generalizedSinTheta_bounded_exact
    (N : RectangularSymmetricIdealFamily (𝕜 := ℂ))
    {A : E →L[ℂ] E} {A₀ : F →L[ℂ] F}
    {Λ₁ : G →L[ℂ] G} {X : F →L[ℂ] E}
    {F₀ : H →L[ℂ] E} {F₁ : G →L[ℂ] E}
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
  have hBlock := generalizedSinTheta_bounded
    N hA hA₀ hΛ₁ hdecomp.isometry₁ hIntertwine
      hβα hδ hε hframe hgap hR
  have hAngle := sinThetaBlock_mem_and_gauge_eq_directedSinThetaOperator
    N X F₀ F₁ hframe hε hdecomp hBlock.1
  refine ⟨hAngle.1, ?_⟩
  rw [hAngle.2]
  exact hBlock.2

end Complex

section GenericExact

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- In the isometric case, the raw complementary overlap block and the
orthogonal-complement projection of the trial map have the same ideal gauge. -/
theorem isometricComplementaryBlock_mem_and_gauge_eq_directed
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    (X : F →L[𝕜] E) (F₀ : H →L[𝕜] E) (F₁ : G →L[𝕜] E)
    (_hX : IsometricEmbedding X)
    (hdecomp : OrthogonalExactDecomposition F₀ F₁)
    (hblock : N.Mem (X.adjoint ∘L F₁)) :
    N.Mem ((ContinuousLinearMap.id 𝕜 E - F₀ ∘L F₀.adjoint) ∘L X) ∧
      N.gauge ((ContinuousLinearMap.id 𝕜 E - F₀ ∘L F₀.adjoint) ∘L X) =
        N.gauge (X.adjoint ∘L F₁) := by
  have hComplement :
      ContinuousLinearMap.id 𝕜 E - F₀ ∘L F₀.adjoint =
        F₁ ∘L F₁.adjoint := by
    rw [← hdecomp.projection_sum]
    abel
  let D : F →L[𝕜] E :=
    (ContinuousLinearMap.id 𝕜 E - F₀ ∘L F₀.adjoint) ∘L X
  have hDirected : D = F₁ ∘L (X.adjoint ∘L F₁).adjoint := by
    dsimp [D]
    rw [hComplement, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint]
    exact ContinuousLinearMap.comp_assoc _ _ _
  have hblockAdj : N.Mem (X.adjoint ∘L F₁).adjoint :=
    N.adjoint_mem hblock
  have hDirectedMem : N.Mem D := by
    rw [hDirected]
    exact N.comp_left_mem F₁ hblockAdj
  have hF₁Norm : ‖F₁‖ ≤ 1 :=
    opNorm_le_one_of_isometry hdecomp.isometry₁
  have hForward : N.gauge D ≤ N.gauge (X.adjoint ∘L F₁) := by
    rw [hDirected]
    calc
      N.gauge (F₁ ∘L (X.adjoint ∘L F₁).adjoint)
          ≤ N.gauge (X.adjoint ∘L F₁).adjoint :=
        N.gauge_comp_left_le F₁ hblockAdj hF₁Norm
      _ = N.gauge (X.adjoint ∘L F₁) := N.gauge_adjoint hblock
  have hF₁LeftInverse :
      F₁.adjoint ∘L F₁ = ContinuousLinearMap.id 𝕜 G :=
    adjoint_comp_self_eq_id_of_isometry hdecomp.isometry₁
  have hRecover :
      (X.adjoint ∘L F₁).adjoint = F₁.adjoint ∘L D := by
    calc
      (X.adjoint ∘L F₁).adjoint =
          ContinuousLinearMap.id 𝕜 G ∘L (X.adjoint ∘L F₁).adjoint := by simp
      _ = (F₁.adjoint ∘L F₁) ∘L (X.adjoint ∘L F₁).adjoint := by
          rw [hF₁LeftInverse]
      _ = F₁.adjoint ∘L (F₁ ∘L (X.adjoint ∘L F₁).adjoint) :=
          ContinuousLinearMap.comp_assoc _ _ _
      _ = F₁.adjoint ∘L D := by rw [hDirected]
  have hF₁AdjNorm : ‖F₁.adjoint‖ ≤ 1 := by simpa using hF₁Norm
  have hReverse : N.gauge (X.adjoint ∘L F₁) ≤ N.gauge D := by
    rw [← N.gauge_adjoint hblock, hRecover]
    exact N.gauge_comp_left_le F₁.adjoint hDirectedMem hF₁AdjNorm
  exact ⟨hDirectedMem, le_antisymm hForward hReverse⟩

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
  have hBlock := sinTheta_bounded
    N hA hA₀ hΛ₁ hX hdecomp.isometry₁ hIntertwine
      hβα hδ hgap hR
  have hAngle := isometricComplementaryBlock_mem_and_gauge_eq_directed
    N X F₀ F₁ hX hdecomp hBlock.1
  refine ⟨hAngle.1, ?_⟩
  rw [hAngle.2]
  exact hBlock.2
end GenericExact

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib

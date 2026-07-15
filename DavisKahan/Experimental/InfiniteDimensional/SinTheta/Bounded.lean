/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.SpectralBridge
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.FrameFactorization

/-!
# Exact bounded infinite-dimensional `sin Θ` endpoints

The proof first solves the complementary Sylvester equation for the raw overlap
`X⋆F₁`.  A lower-frame polar factorization then converts that overlap into the
normalized sine block.  Under a complete orthogonal decomposition of the exact
space, this block is identified with the full directed sine operator.
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
  rw [generalResidual, ContinuousLinearMap.adjoint_sub,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp]
  rw [hA.clm_adjoint_eq, hA₀.clm_adjoint_eq]
  rw [ContinuousLinearMap.sub_comp]
  calc
    (X.adjoint ∘L A) ∘L F₁ - A₀ ∘L X.adjoint ∘L F₁
        = X.adjoint ∘L (A ∘L F₁) -
            A₀ ∘L (X.adjoint ∘L F₁) := by
              simp [ContinuousLinearMap.comp_assoc]
    _ = X.adjoint ∘L (F₁ ∘L Λ₁) -
            A₀ ∘L (X.adjoint ∘L F₁) := by rw [hIntertwine]
    _ = (X.adjoint ∘L F₁) ∘L Λ₁ -
            A₀ ∘L (X.adjoint ∘L F₁) := by
              simp [ContinuousLinearMap.comp_assoc]

/-- The same residual identity in the orientation consumed by the Sylvester estimate. -/
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

/-- The residual right-hand side in the complementary equation belongs to the
same rectangular ideal, with no increase in gauge. -/
theorem complementaryResidual_mem_and_gauge_le
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    {A : E →L[𝕜] E} {A₀ : F →L[𝕜] F}
    {X : F →L[𝕜] E} {F₁ : G →L[𝕜] E}
    (hF₁ : IsometricEmbedding F₁)
    (hR : N.Mem (generalResidual A X A₀)) :
    N.Mem (-((generalResidual A X A₀).adjoint ∘L F₁)) ∧
      N.gauge (-((generalResidual A X A₀).adjoint ∘L F₁)) ≤
        N.gauge (generalResidual A X A₀) := by
  have hRadj : N.Mem (generalResidual A X A₀).adjoint :=
    N.adjoint_mem hR
  have hcomp : N.Mem ((generalResidual A X A₀).adjoint ∘L F₁) := by
    simpa [ContinuousLinearMap.id_comp] using
      N.comp_mem (ContinuousLinearMap.id 𝕜 F)
        (generalResidual A X A₀).adjoint F₁ hRadj
  have hneg := N.smul_mem (-1 : 𝕜) hcomp
  refine ⟨by simpa using hneg, ?_⟩
  calc
    N.gauge (-((generalResidual A X A₀).adjoint ∘L F₁))
        = N.gauge ((generalResidual A X A₀).adjoint ∘L F₁) :=
          N.gauge_neg hcomp
    _ ≤ ‖ContinuousLinearMap.id 𝕜 F‖ *
          N.gauge (generalResidual A X A₀).adjoint * ‖F₁‖ := by
          simpa [ContinuousLinearMap.id_comp] using
            N.gauge_comp_le (ContinuousLinearMap.id 𝕜 F) F₁ hRadj
    _ = N.gauge (generalResidual A X A₀) := by
          rw [norm_id, one_mul, N.gauge_adjoint hR,
            norm_eq_one_of_isometricEmbedding hF₁, mul_one]

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
  let C : G →L[𝕜] F :=
    -((generalResidual A X A₀).adjoint ∘L F₁)
  have hC := complementaryResidual_mem_and_gauge_le N hF₁ hR
  have hEq :
      A₀ ∘L (X.adjoint ∘L F₁) -
        (X.adjoint ∘L F₁) ∘L Λ₁ = C := by
    exact complementary_sylvester_equation hA hA₀ hΛ₁ hIntertwine
  have hSyl := sylvester_mem_and_gauge_le_of_intervalExteriorGap
    N hA₀ hΛ₁ hβα hδ hgap hEq hC.1
  exact ⟨hSyl.1, hSyl.2.trans hC.2⟩

/-- Bounded generalized complementary-block theorem. -/
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
  have hraw := complementaryBlock_mem_and_gauge_le
    N hA hA₀ hΛ₁ hF₁ hIntertwine hβα hδ hgap hR
  have hnormalize := lowerFrame_sinThetaBlock_mem_and_gauge_le
    N X F₁ hframe hε hraw.1
  refine ⟨hnormalize.1, ?_⟩
  calc
    δ * ε * N.gauge (sinThetaBlock X F₁ hframe hε)
        = δ * (ε * N.gauge (sinThetaBlock X F₁ hframe hε)) := by ring
    _ ≤ δ * N.gauge (X.adjoint ∘L F₁) :=
      mul_le_mul_of_nonneg_left hnormalize.2 hδ.le
    _ ≤ N.gauge (generalResidual A X A₀) := hraw.2

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
        ≤ N.gauge (generalResidual A X A₀) :=
  complementaryBlock_mem_and_gauge_le
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

/-- Directed sine operator from normalized trial coordinates into the
orthogonal complement of the desired exact space. -/
noncomputable def directedSinThetaOperator
    (X : F →L[𝕜] E) (F₀ : H →L[𝕜] E) {ε : ℝ}
    (hX : LowerFrameBound X ε) (hε : 0 < ε) : F →L[𝕜] E :=
  (ContinuousLinearMap.id 𝕜 E - F₀ ∘L F₀.adjoint) ∘L
    frameIsometry X hX hε

/-- The exact complementary projection equals `F₁F₁⋆`. -/
theorem complementaryProjection_eq_exactComplement
    {F₀ : H →L[𝕜] E} {F₁ : G →L[𝕜] E}
    (hdecomp : OrthogonalExactDecomposition F₀ F₁) :
    ContinuousLinearMap.id 𝕜 E - F₀ ∘L F₀.adjoint =
      F₁ ∘L F₁.adjoint := by
  linarith [hdecomp.projection_sum]

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
  let Q := frameIsometry X hX hε
  let B := sinThetaBlock X F₁ hX hε
  have hF₁starF₁ : F₁.adjoint ∘L F₁ = ContinuousLinearMap.id 𝕜 G :=
    ContinuousLinearMap.norm_map_iff_adjoint_comp_self F₁ |>.1
      hdecomp.isometry₁
  have hBstar : B.adjoint = F₁.adjoint ∘L Q := by
    simp [B, Q, sinThetaBlock, ContinuousLinearMap.adjoint_comp]
  have hdir : directedSinThetaOperator X F₀ hX hε = F₁ ∘L B.adjoint := by
    rw [directedSinThetaOperator,
      complementaryProjection_eq_exactComplement hdecomp]
    simp [B, Q, hBstar, ContinuousLinearMap.comp_assoc]
  have hBadj : N.Mem B.adjoint := N.adjoint_mem hblock
  have hdirMem : N.Mem (directedSinThetaOperator X F₀ hX hε) := by
    rw [hdir]
    simpa [ContinuousLinearMap.comp_id] using
      N.comp_mem F₁ B.adjoint (ContinuousLinearMap.id 𝕜 F) hBadj
  have hrecover : B.adjoint = F₁.adjoint ∘L
      directedSinThetaOperator X F₀ hX hε := by
    rw [hdir, ← ContinuousLinearMap.comp_assoc, hF₁starF₁]
    simp
  have hforward :
      N.gauge (directedSinThetaOperator X F₀ hX hε) ≤ N.gauge B := by
    rw [hdir]
    calc
      N.gauge (F₁ ∘L B.adjoint)
          ≤ ‖F₁‖ * N.gauge B.adjoint :=
            N.gauge_comp_left_le F₁ hBadj
      _ = N.gauge B := by
        rw [norm_eq_one_of_isometricEmbedding hdecomp.isometry₁,
          one_mul, N.gauge_adjoint hblock]
  have hreverse : N.gauge B ≤
      N.gauge (directedSinThetaOperator X F₀ hX hε) := by
    rw [← N.gauge_adjoint hblock, hrecover]
    calc
      N.gauge (F₁.adjoint ∘L directedSinThetaOperator X F₀ hX hε)
          ≤ ‖F₁.adjoint‖ *
              N.gauge (directedSinThetaOperator X F₀ hX hε) :=
            N.gauge_comp_left_le F₁.adjoint hdirMem
      _ = N.gauge (directedSinThetaOperator X F₀ hX hε) := by
        rw [ContinuousLinearMap.norm_adjoint,
          norm_eq_one_of_isometricEmbedding hdecomp.isometry₁, one_mul]
  exact ⟨hdirMem, le_antisymm hforward hreverse⟩

/-- Exact bounded infinite-dimensional Davis--Kahan Theorem 6.1. -/
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
  have hblock := generalizedSinTheta_bounded N hA hA₀ hΛ₁
    hdecomp.isometry₁ hIntertwine hβα hδ hε hframe hgap hR
  have hidentify := sinThetaBlock_mem_and_gauge_eq_directedSinThetaOperator
    N X F₀ F₁ hframe hε hdecomp hblock.1
  exact ⟨hidentify.1, by simpa [hidentify.2] using hblock.2⟩

/-- An isometry has lower frame bound one. -/
theorem lowerFrameBound_one_of_isometricEmbedding
    {X : F →L[𝕜] E} (hX : IsometricEmbedding X) :
    LowerFrameBound X 1 := by
  intro x
  simpa [hX x]

/-- For an isometry the frame polar factor is the original map. -/
theorem frameIsometry_eq_of_isometricEmbedding
    {X : F →L[𝕜] E} (hX : IsometricEmbedding X) :
    frameIsometry X (lowerFrameBound_one_of_isometricEmbedding hX)
      zero_lt_one = X := by
  have hgram : gram X = ContinuousLinearMap.id 𝕜 F :=
    ContinuousLinearMap.norm_map_iff_adjoint_comp_self X |>.1 hX
  unfold frameIsometry gramInvSqrt gramInverseData gram
  simp [hgram]

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
  let hframe : LowerFrameBound X 1 :=
    lowerFrameBound_one_of_isometricEmbedding hX
  have hgeneral := generalizedSinTheta_bounded_exact
    N hA hA₀ hΛ₁ hdecomp hIntertwine hβα hδ zero_lt_one
      hframe hgap hR
  have hQ : frameIsometry X hframe zero_lt_one = X :=
    frameIsometry_eq_of_isometricEmbedding hX
  simpa [directedSinThetaOperator, hQ] using hgeneral

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib

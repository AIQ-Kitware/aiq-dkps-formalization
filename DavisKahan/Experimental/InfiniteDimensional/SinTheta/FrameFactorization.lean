/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.Sylvester.Bounded

/-!
# Infinite-dimensional lower-frame factorization

A bounded-below trial map has the polar factorization `X = Q |X|`, where `Q`
is an isometry and `|X| = sqrt (X*X)` is bounded below by the frame constant.
The inverse square root transports residual estimates from `X*F₁` to the
normalized sine block `Q*F₁`.
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

/-- A quantitative lower frame bound. -/
def LowerFrameBound (X : F →L[𝕜] E) (ε : ℝ) : Prop :=
  ∀ x, ε * ‖x‖ ≤ ‖X x‖

/-- A positive lower frame bound implies injectivity. -/
theorem LowerFrameBound.injective
    {X : F →L[𝕜] E} {ε : ℝ}
    (hX : LowerFrameBound X ε) (hε : 0 < ε) :
    Function.Injective X := by
  intro x y hxy
  have h := hX (x-y)
  rw [map_sub, hxy, sub_self, norm_zero] at h
  have : ‖x-y‖ = 0 := by nlinarith [norm_nonneg (x-y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

/-- A positive lower frame bound implies closed range. -/
theorem LowerFrameBound.closedRange
    {X : F →L[𝕜] E} {ε : ℝ}
    (hX : LowerFrameBound X ε) (hε : 0 < ε) :
    IsClosed (Set.range X) := by
  exact LinearMap.isClosed_range_of_bound_below X.toLinearMap ε hε hX

/-- Gram operator of a trial map. -/
noncomputable def gram (X : F →L[𝕜] E) : F →L[𝕜] F :=
  X.adjoint ∘L X

/-- Coercivity of the Gram operator. -/
theorem gram_coercive
    {X : F →L[𝕜] E} {ε : ℝ}
    (hX : LowerFrameBound X ε) (hε : 0 ≤ ε) :
    ∀ x, ε ^ 2 * ‖x‖ ^ 2
      ≤ RCLike.re ⟪gram X x, x⟫_𝕜 := by
  intro x
  rw [gram, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left,
    RCLike.re_inner_self]
  have h := hX x
  nlinarith [norm_nonneg x, norm_nonneg (X x)]

/-- Bounded inverse of the positive Gram operator. -/
noncomputable def gramInverseData
    (X : F →L[𝕜] E) {ε : ℝ}
    (hX : LowerFrameBound X ε) (hε : 0 < ε) :
    BoundedInverseData (gram X) :=
  positiveBoundedInverseData_of_coercive
    (gram X) (by
      exact ContinuousLinearMap.isSelfAdjoint_adjoint_comp_self X)
    (ε^2) (sq_pos_of_pos hε) (gram_coercive hX hε.le)

/-- Positive square root of the Gram operator. -/
noncomputable def gramSqrt (X : F →L[𝕜] E) : F →L[𝕜] F :=
  RCLikeContinuousFunctionalCalculus.sqrt (gram X)

/-- Inverse square root of the Gram operator. -/
noncomputable def gramInvSqrt
    (X : F →L[𝕜] E) {ε : ℝ}
    (hX : LowerFrameBound X ε) (hε : 0 < ε) :
    F →L[𝕜] F :=
  let Gunit := (gramInverseData X hX hε).toUnit
  RCLikeContinuousFunctionalCalculus.sqrt
    ((Gunit⁻¹ : (F →L[𝕜] F)ˣ) : F →L[𝕜] F)

/-- The two square-root factors are mutual inverses. -/
theorem gramInvSqrt_comp_gramSqrt
    (X : F →L[𝕜] E) {ε : ℝ}
    (hX : LowerFrameBound X ε) (hε : 0 < ε) :
    gramInvSqrt X hX hε ∘L gramSqrt X =
      ContinuousLinearMap.id 𝕜 F := by
  exact RCLikeContinuousFunctionalCalculus.sqrt_inv_mul_sqrt
    (gramInverseData X hX hε).toUnit

/-- Isometric polar factor of a bounded-below trial map. -/
noncomputable def frameIsometry
    (X : F →L[𝕜] E) {ε : ℝ}
    (hX : LowerFrameBound X ε) (hε : 0 < ε) :
    F →L[𝕜] E :=
  X ∘L gramInvSqrt X hX hε

/-- The polar factor preserves norms. -/
theorem frameIsometry_isometry
    (X : F →L[𝕜] E) {ε : ℝ}
    (hX : LowerFrameBound X ε) (hε : 0 < ε) :
    IsometricEmbedding (frameIsometry X hX hε) := by
  intro x
  have hgramInv :
      gramInvSqrt X hX hε ∘L gram X ∘L gramInvSqrt X hX hε =
        ContinuousLinearMap.id 𝕜 F :=
    inverseSquareRoot_conjugates_to_one (gramInverseData X hX hε)
  have hsquare : ‖frameIsometry X hX hε x‖^2 = ‖x‖^2 := by
    rw [frameIsometry, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right]
    simpa [gram, ContinuousLinearMap.comp_assoc] using
      congrArg (fun T : F →L[𝕜] F => RCLike.re ⟪T x, x⟫_𝕜) hgramInv
  exact sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mp hsquare

/-- Polar factorization of the trial map. -/
theorem frameFactorization
    (X : F →L[𝕜] E) {ε : ℝ}
    (hX : LowerFrameBound X ε) (hε : 0 < ε) :
    X = frameIsometry X hX hε ∘L gramSqrt X := by
  unfold frameIsometry
  rw [ContinuousLinearMap.comp_assoc,
    gramInvSqrt_comp_gramSqrt X hX hε]
  simp

/-- Quantitative inverse-square-root estimate. -/
theorem norm_gramInvSqrt_le
    (X : F →L[𝕜] E) {ε : ℝ}
    (hX : LowerFrameBound X ε) (hε : 0 < ε) :
    ‖gramInvSqrt X hX hε‖ ≤ ε⁻¹ := by
  apply RCLikeContinuousFunctionalCalculus.norm_sqrt_le
  intro λ hλ
  have hλlower : ε^2 ≤ λ :=
    spectrum_gram_lower_bound (gram_coercive hX hε.le) hλ
  have hλpos : 0 < λ := lt_of_lt_of_le (sq_pos_of_pos hε) hλlower
  rw [Real.sqrt_inv hλ.le]
  exact Real.sqrt_le_iff.2 ⟨inv_nonneg.mpr hε.le,
    by rw [sq_inv]; exact inv_le_inv₀ (sq_pos_of_pos hε) hλlower⟩

/-- The range of the polar factor agrees with the range of the trial map. -/
theorem range_frameIsometry_eq_range
    (X : F →L[𝕜] E) {ε : ℝ}
    (hX : LowerFrameBound X ε) (hε : 0 < ε) :
    LinearMap.range (frameIsometry X hX hε).toLinearMap =
      LinearMap.range X.toLinearMap := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    exact ⟨gramInvSqrt X hX hε x, rfl⟩
  · rintro y ⟨x, rfl⟩
    refine ⟨gramSqrt X x, ?_⟩
    simpa [ContinuousLinearMap.comp_apply] using
      congrArg (fun T : F →L[𝕜] E => T x)
        (frameFactorization X hX hε)

/-- Directed sine block in normalized trial coordinates. -/
noncomputable def sinThetaBlock
    (X : F →L[𝕜] E) (F₁ : G →L[𝕜] E) {ε : ℝ}
    (hX : LowerFrameBound X ε) (hε : 0 < ε) :
    G →L[𝕜] F :=
  (frameIsometry X hX hε).adjoint ∘L F₁

/-- The normalized sine block is obtained from the raw overlap block by the
inverse Gram square root. -/
theorem sinThetaBlock_eq_gramInvSqrt_comp_raw
    (X : F →L[𝕜] E) (F₁ : G →L[𝕜] E) {ε : ℝ}
    (hX : LowerFrameBound X ε) (hε : 0 < ε) :
    sinThetaBlock X F₁ hX hε =
      gramInvSqrt X hX hε ∘L (X.adjoint ∘L F₁) := by
  unfold sinThetaBlock frameIsometry
  rw [ContinuousLinearMap.adjoint_comp]
  have hself : (gramInvSqrt X hX hε).adjoint =
      gramInvSqrt X hX hε :=
    (inverseSquareRoot_isSelfAdjoint (gramInverseData X hX hε)).adjoint_eq
  rw [hself, ContinuousLinearMap.comp_assoc]

/-- Lower-frame transport from the raw complementary block to the sine block. -/
theorem lowerFrame_sinThetaBlock_mem_and_gauge_le
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    (X : F →L[𝕜] E) (F₁ : G →L[𝕜] E) {ε : ℝ}
    (hX : LowerFrameBound X ε) (hε : 0 < ε)
    (hRaw : N.Mem (X.adjoint ∘L F₁)) :
    N.Mem (sinThetaBlock X F₁ hX hε) ∧
      ε * N.gauge (sinThetaBlock X F₁ hX hε)
        ≤ N.gauge (X.adjoint ∘L F₁) := by
  rw [sinThetaBlock_eq_gramInvSqrt_comp_raw X F₁ hX hε]
  have hmem := N.comp_mem (gramInvSqrt X hX hε)
    (ContinuousLinearMap.id 𝕜 G) hRaw
  refine ⟨by simpa using hmem, ?_⟩
  have hgauge := N.gauge_comp_le (gramInvSqrt X hX hε)
    (ContinuousLinearMap.id 𝕜 G) hRaw
  have hinv := norm_gramInvSqrt_le X hX hε
  simp only [ContinuousLinearMap.comp_id, norm_id, mul_one] at hgauge
  have hεinv : ε * ε⁻¹ = 1 := by field_simp [ne_of_gt hε]
  nlinarith [N.gauge_nonneg hRaw]

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib

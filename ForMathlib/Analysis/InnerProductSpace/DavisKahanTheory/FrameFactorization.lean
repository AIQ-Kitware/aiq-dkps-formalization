/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForMathlib.Analysis.InnerProductSpace.DavisKahanTheory.Residual
import ForMathlib.Analysis.InnerProductSpace.PositiveSqrt

/-!
# Isometric range factorization of an injective trial map

For an injective rectangular map `X : F →ₗ[𝕜] E`, this module constructs the
canonical finite-dimensional polar factorization

`X = Q T`,

where `Q : F →ₗᵢ[𝕜] E` is an isometric embedding with the same range as `X`
and `T : F ≃ₗ[𝕜] F` is the positive square root of the Gram operator
`X⋆ X`, packaged as a linear equivalence.

This is the shared coordinate layer needed by the generalized sine theorem and
later graph-operator tangent developments.  In particular, it separates the
geometric range representative `Q` from the invertible coordinate distortion
`T` without conjugating a coordinate operator through `T`.
-/

namespace ForMathlib
namespace DavisKahanTheory

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- A quantitative lower frame bound for a not-necessarily-isometric trial
map.  Davis--Kahan's parameter `e` is this lower singular-value bound. -/
def LowerFrameBound (X : F →ₗ[𝕜] E) (ε : ℝ) : Prop :=
  ∀ y, ε * ‖y‖ ≤ ‖X y‖

/-- A positive lower frame bound implies injectivity. -/
theorem LowerFrameBound.injective {X : F →ₗ[𝕜] E} {ε : ℝ}
    (hframe : LowerFrameBound X ε) (hε : 0 < ε) :
    Function.Injective X := by
  intro x y hxy
  have hmul : ε * ‖x - y‖ ≤ 0 := by
    simpa [map_sub, hxy] using hframe (x - y)
  have hnorm : ‖x - y‖ ≤ 0 := by
    nlinarith [norm_nonneg (x - y)]
  apply sub_eq_zero.mp
  exact norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _))

/-- The positive square root of the Gram operator `X⋆ X`. -/
noncomputable def trialGramSqrt (X : F →ₗ[𝕜] E) : F →ₗ[𝕜] F :=
  X.isPositive_adjoint_comp_self.sqrt

/-- The Gram square root has the same pointwise norm as the original
rectangular map. -/
theorem norm_trialGramSqrt_apply (X : F →ₗ[𝕜] E) (x : F) :
    ‖trialGramSqrt X x‖ = ‖X x‖ := by
  have hsq : ‖trialGramSqrt X x‖ ^ 2 = ‖X x‖ ^ 2 :=
    (X.isPositive_adjoint_comp_self.sq_norm_sqrt_apply x).trans <| by
      rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left,
        ← norm_sq_eq_re_inner (𝕜 := 𝕜)]
  rw [← Real.sqrt_sq (norm_nonneg (trialGramSqrt X x)),
    ← Real.sqrt_sq (norm_nonneg (X x)), hsq]

/-- The Gram square root has exactly the kernel of the original rectangular
map. -/
theorem ker_trialGramSqrt (X : F →ₗ[𝕜] E) :
    LinearMap.ker (trialGramSqrt X) = LinearMap.ker X := by
  calc
    LinearMap.ker (trialGramSqrt X) =
        LinearMap.ker (X.adjoint ∘ₗ X) :=
      X.isPositive_adjoint_comp_self.ker_sqrt
    _ = LinearMap.ker X := LinearMap.ker_adjoint_comp_self X

/-- Injectivity of `X` transfers to its positive Gram square root. -/
theorem trialGramSqrt_injective {X : F →ₗ[𝕜] E}
    (hX : Function.Injective X) : Function.Injective (trialGramSqrt X) := by
  rw [← LinearMap.ker_eq_bot, ker_trialGramSqrt X, LinearMap.ker_eq_bot]
  exact hX

/-- For an injective trial map, the positive Gram square root is an invertible
coordinate map. -/
noncomputable def trialGramSqrtEquiv (X : F →ₗ[𝕜] E)
    (hX : Function.Injective X) : F ≃ₗ[𝕜] F :=
  let hinj := trialGramSqrt_injective hX
  LinearEquiv.ofBijective (trialGramSqrt X)
    ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

@[simp] theorem trialGramSqrtEquiv_toLinearMap (X : F →ₗ[𝕜] E)
    (hX : Function.Injective X) :
    (trialGramSqrtEquiv X hX).toLinearMap = trialGramSqrt X :=
  rfl

/-- The invertible coordinate factor has the same pointwise norm as the
original trial map. -/
theorem norm_trialGramSqrtEquiv_apply (X : F →ₗ[𝕜] E)
    (hX : Function.Injective X) (x : F) :
    ‖trialGramSqrtEquiv X hX x‖ = ‖X x‖ := by
  change ‖trialGramSqrt X x‖ = ‖X x‖
  exact norm_trialGramSqrt_apply X x

/-- Isometric polar factor of an injective rectangular trial map. -/
noncomputable def orthonormalizedEmbedding (X : F →ₗ[𝕜] E)
    (hX : Function.Injective X) : F →ₗᵢ[𝕜] E where
  toLinearMap := X ∘ₗ (trialGramSqrtEquiv X hX).symm.toLinearMap
  norm_map' y := by
    change ‖X ((trialGramSqrtEquiv X hX).symm y)‖ = ‖y‖
    rw [← norm_trialGramSqrt_apply X]
    change ‖(trialGramSqrtEquiv X hX)
      ((trialGramSqrtEquiv X hX).symm y)‖ = ‖y‖
    rw [(trialGramSqrtEquiv X hX).apply_symm_apply]

/-- The canonical polar factors recompose to the original rectangular map. -/
theorem orthonormalizedEmbedding_comp_trialGramSqrtEquiv
    (X : F →ₗ[𝕜] E) (hX : Function.Injective X) :
    (orthonormalizedEmbedding X hX).toLinearMap ∘ₗ
        (trialGramSqrtEquiv X hX).toLinearMap = X := by
  ext x
  change X ((trialGramSqrtEquiv X hX).symm
    (trialGramSqrtEquiv X hX x)) = X x
  rw [(trialGramSqrtEquiv X hX).symm_apply_apply]

/-- The isometric polar factor and the original trial map have the same range. -/
theorem range_orthonormalizedEmbedding (X : F →ₗ[𝕜] E)
    (hX : Function.Injective X) :
    LinearMap.range (orthonormalizedEmbedding X hX).toLinearMap =
      LinearMap.range X := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    refine ⟨(trialGramSqrtEquiv X hX).symm x, ?_⟩
    rfl
  · rintro y ⟨x, rfl⟩
    refine ⟨trialGramSqrtEquiv X hX x, ?_⟩
    exact LinearMap.congr_fun
      (orthonormalizedEmbedding_comp_trialGramSqrtEquiv X hX) x

/-- Reusable proof-carrying isometric range factorization of a trial map. -/
structure TrialMapFrameFactorization (X : F →ₗ[𝕜] E) where
  /-- Isometric embedding representing the range of `X`. -/
  isometry : F →ₗᵢ[𝕜] E
  /-- Invertible coordinate distortion on the trial space. -/
  coordinate : F ≃ₗ[𝕜] F
  /-- Reconstruction of the original trial map. -/
  factor : isometry.toLinearMap ∘ₗ coordinate.toLinearMap = X
  /-- The isometric representative has exactly the original range. -/
  range_eq : LinearMap.range isometry.toLinearMap = LinearMap.range X

/-- The canonical Gram/polar factorization of an injective trial map. -/
noncomputable def trialMapFrameFactorization (X : F →ₗ[𝕜] E)
    (hX : Function.Injective X) : TrialMapFrameFactorization X where
  isometry := orthonormalizedEmbedding X hX
  coordinate := trialGramSqrtEquiv X hX
  factor := orthonormalizedEmbedding_comp_trialGramSqrtEquiv X hX
  range_eq := range_orthonormalizedEmbedding X hX

/-- Canonical frame factorization obtained directly from a positive lower
frame bound. -/
noncomputable def trialMapFrameFactorizationOfLowerFrameBound
    (X : F →ₗ[𝕜] E) {ε : ℝ} (hframe : LowerFrameBound X ε)
    (hε : 0 < ε) : TrialMapFrameFactorization X :=
  trialMapFrameFactorization X (hframe.injective hε)

@[simp] theorem trialMapFrameFactorization_isometry
    (X : F →ₗ[𝕜] E) (hX : Function.Injective X) :
    (trialMapFrameFactorization X hX).isometry =
      orthonormalizedEmbedding X hX :=
  rfl

@[simp] theorem trialMapFrameFactorization_coordinate
    (X : F →ₗ[𝕜] E) (hX : Function.Injective X) :
    (trialMapFrameFactorization X hX).coordinate =
      trialGramSqrtEquiv X hX :=
  rfl

end DavisKahanTheory
end ForMathlib

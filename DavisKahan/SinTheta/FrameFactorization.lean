/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import TauCeti.Analysis.InnerProductSpace.Projection.SinTheta
public import TauCeti.Analysis.InnerProductSpace.Polar.Bounded
public import ForTauCeti.Analysis.InnerProductSpace.Projection.Gap
public import ForTauCeti.Analysis.InnerProductSpace.Projection.Blocks
public import DavisKahan.BoundedOperator.Problem
public import DavisKahan.Sylvester.Bounded
public import DavisKahan.OperatorIdeal.CanonicalRealView
public import TauCeti.Analysis.InnerProductSpace.Coercive
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

public section

open TauCeti.DavisKahan.Sylvester

/-!
# Infinite-dimensional lower-frame factorization

The generalized theorem permits a non-isometric trial map with a positive lower
frame bound.  This module exposes the closed-range, Gram inverse, polar factor,
and ideal-norm transport seams separately.

The modulus and polar factor are TauCeti's native bounded-operator constructions.
A positive lower frame bound makes the Gram operator and its modulus invertible.
The paper-facing package collects the two-sided inverse, range, and norm facts
used by the generalized sine estimates. Both scalar branches use the same
construction. The former separate power-calculus proofs are archived at DKPS
commit `8c1a82e68`.

-/

namespace TauCeti

open TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace

section Generic

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F G : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]

/-- A quantitative lower frame bound. -/
@[expose]
def LowerFrameBound (X : F →L[𝕜] E) (ε : ℝ) : Prop :=
  ∀ x, ε * ‖x‖ ≤ ‖X x‖

omit [CompleteSpace E] [CompleteSpace F] in
/-- A lower frame bound remains valid after decreasing its constant. -/
theorem LowerFrameBound.mono
    {X : F →L[𝕜] E} {ε ε' : ℝ}
    (hX : LowerFrameBound X ε) (hε'ε : ε' ≤ ε) :
    LowerFrameBound X ε' := by
  intro x
  exact (mul_le_mul_of_nonneg_right hε'ε (norm_nonneg x)).trans (hX x)

omit [CompleteSpace E] [CompleteSpace F] in
/-- A positive lower frame bound implies injectivity. -/
theorem LowerFrameBound.injective
    {X : F →L[𝕜] E} {ε : ℝ}
    (hX : LowerFrameBound X ε) (hε : 0 < ε) :
    Function.Injective X := by
  intro x y hxy
  have hbound := hX (x - y)
  have hzero : X (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  rw [hzero, norm_zero] at hbound
  have hnorm : ‖x - y‖ = 0 := by
    nlinarith [norm_nonneg (x - y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

omit [CompleteSpace E] [CompleteSpace F] in
/-- An isometric trial map has lower frame bound one. -/
theorem lowerFrameBound_one_of_isometry
    {X : F →L[𝕜] E} (hX : IsometricEmbedding X) :
    LowerFrameBound X 1 := by
  intro x
  simpa using le_of_eq (hX x).symm

omit [CompleteSpace E] [CompleteSpace F] in
/-- An isometric embedding is a contraction in operator norm. -/
theorem opNorm_le_one_of_isometry
    {X : F →L[𝕜] E} (hX : IsometricEmbedding X) :
    ‖X‖ ≤ 1 := by
  refine X.opNorm_le_bound zero_le_one ?_
  intro x
  simpa using le_of_eq (hX x)

/-- The Gram operator of an isometric embedding is the identity. -/
theorem adjoint_comp_self_eq_id_of_isometry
    {X : F →L[𝕜] E} (hX : IsometricEmbedding X) :
    X.adjoint ∘L X = ContinuousLinearMap.id 𝕜 F :=
  X.isometry_iff_adjoint_comp_self.mp (AddMonoidHomClass.isometry_of_norm X hX)

omit [CompleteSpace E] in
/-- A positive lower frame bound implies closed range. -/
theorem LowerFrameBound.closedRange
    {X : F →L[𝕜] E} {ε : ℝ}
    (hX : LowerFrameBound X ε) (hε : 0 < ε) :
    IsClosed (Set.range X) := by
  obtain ⟨K, hanti⟩ : ∃ K : NNReal, AntilipschitzWith K X :=
    (antilipschitzWith_iff_exists_mul_le_norm (f := X)).2 ⟨ε, hε, hX⟩
  exact hanti.isClosed_range X.uniformContinuous

/-- Coercivity of the Gram operator. -/
theorem gram_coercive
    {X : F →L[𝕜] E} {ε : ℝ}
    (hX : LowerFrameBound X ε) (hε : 0 ≤ ε) :
    ∀ x, ε ^ 2 * ‖x‖ ^ 2
      ≤ RCLike.re ⟪(X.adjoint ∘L X) x, x⟫_𝕜 := by
  intro x
  rw [ContinuousLinearMap.comp_apply, X.adjoint_inner_left,
    ← norm_sq_eq_re_inner (𝕜 := 𝕜)]
  have hle : ε * ‖x‖ ≤ ‖X x‖ := hX x
  have hleft : 0 ≤ ε * ‖x‖ := mul_nonneg hε (norm_nonneg x)
  have hdiff : 0 ≤ ‖X x‖ - ε * ‖x‖ := sub_nonneg.mpr hle
  have hsum : 0 ≤ ‖X x‖ + ε * ‖x‖ :=
    add_nonneg (norm_nonneg (X x)) hleft
  have hprod := mul_nonneg hdiff hsum
  nlinarith

/-- Proof-carrying lower-frame polar data.  The single existence theorem below
is the functional-calculus seam; all public factorization and transport results
are projections or consequences of this package. -/
structure LowerFramePolarData
    (X : F →L[𝕜] E) (ε : ℝ)
    (hX : LowerFrameBound X ε) (hε : 0 < ε) where
  sqrt : F →L[𝕜] F
  invSqrt : F →L[𝕜] F
  gram_isUnit : IsUnit (X.adjoint ∘L X)
  invSqrt_sqrt : invSqrt ∘L sqrt = ContinuousLinearMap.id 𝕜 F
  sqrt_invSqrt : sqrt ∘L invSqrt = ContinuousLinearMap.id 𝕜 F
  sqrt_sq : sqrt ∘L sqrt = X.adjoint ∘L X
  normalized_isometry : IsometricEmbedding (X ∘L invSqrt)
  factorization : X = (X ∘L invSqrt) ∘L sqrt
  invSqrt_norm_le : ‖invSqrt‖ ≤ ε⁻¹
  range_normalized :
    LinearMap.range (X ∘L invSqrt).toLinearMap = LinearMap.range X.toLinearMap
  invSqrt_eq_id_of_isometry :
    ∀ _hIso : IsometricEmbedding X, invSqrt = ContinuousLinearMap.id 𝕜 F

/-- The polar package is explicit when the trial map is already isometric. -/
def lowerFramePolarDataOfIsometry
    (X : F →L[𝕜] E) (hIso : IsometricEmbedding X) :
    LowerFramePolarData X 1 (lowerFrameBound_one_of_isometry hIso) zero_lt_one := by
  let I : F →L[𝕜] F := ContinuousLinearMap.id 𝕜 F
  have hgram : X.adjoint ∘L X = I := adjoint_comp_self_eq_id_of_isometry hIso
  refine {
    sqrt := I
    invSqrt := I
    gram_isUnit := hgram.symm ▸ (isUnit_one : IsUnit (1 : F →L[𝕜] F))
    invSqrt_sqrt := ?_
    sqrt_invSqrt := ?_
    sqrt_sq := ?_
    normalized_isometry := ?_
    factorization := ?_
    invSqrt_norm_le := ?_
    range_normalized := ?_
    invSqrt_eq_id_of_isometry := ?_
  }
  · simp [I]
  · simp [I]
  · simpa [I] using hgram.symm
  · simpa [I] using hIso
  · simp [I]
  · simpa [I] using (ContinuousLinearMap.norm_id_le (𝕜 := 𝕜) (E := F))
  · simp [I]
  · intro _
    rfl

/-- The polar data of a bounded-below trial map, assembled from the native modulus
and polar factor over real or complex Hilbert spaces. -/
noncomputable def lowerFramePolarData
    (X : F →L[𝕜] E) {ε : ℝ}
    (hX : LowerFrameBound X ε) (hε : 0 < ε) :
    LowerFramePolarData X ε hX hε := by
  let gram := X.adjoint ∘L X
  have hgram : IsUnit gram :=
    gram.isUnit_of_coercive (sq_pos_of_pos hε) (gram_coercive hX hε.le)
  have hmod_sq : X.modulus * X.modulus = gram := X.modulus_comp_modulus
  have hmod : IsUnit X.modulus :=
    ((Commute.refl X.modulus).isUnit_mul_iff.mp (hmod_sq.symm ▸ hgram)).1
  have hpolar := X.polarFactor_eq_comp_inverse hmod
  have hisometry : IsometricEmbedding (X ∘L Ring.inverse X.modulus) := by
    rw [← hpolar]
    exact X.norm_polarFactor_apply_of_injective (hX.injective hε)
  refine {
    sqrt := X.modulus
    invSqrt := Ring.inverse X.modulus
    gram_isUnit := hgram
    invSqrt_sqrt := Ring.inverse_mul_cancel _ hmod
    sqrt_invSqrt := Ring.mul_inverse_cancel _ hmod
    sqrt_sq := X.modulus_comp_modulus
    normalized_isometry := hisometry
    factorization := ?_
    invSqrt_norm_le := ?_
    range_normalized := ?_
    invSqrt_eq_id_of_isometry := ?_
  }
  · rw [← hpolar]
    exact X.polarFactor_comp_modulus.symm
  · refine (Ring.inverse X.modulus).opNorm_le_bound (inv_nonneg.mpr hε.le) fun y => ?_
    rw [le_inv_mul_iff₀ hε]
    exact (hX (Ring.inverse X.modulus y)).trans_eq (hisometry y)
  · rw [← hpolar, X.range_polarFactor]
    exact (hX.closedRange hε).submodule_topologicalClosure_eq
  · intro hIso
    have hid : (1 : F →L[𝕜] F) = X.modulus := ContinuousLinearMap.eq_modulus_iff.2
      ⟨ContinuousLinearMap.isPositive_one, by
        change ContinuousLinearMap.id 𝕜 F ∘L ContinuousLinearMap.id 𝕜 F = _
        rw [ContinuousLinearMap.comp_id]
        exact (adjoint_comp_self_eq_id_of_isometry hIso).symm⟩
    change Ring.inverse X.modulus = (1 : F →L[𝕜] F)
    rw [← hid, Ring.inverse_one]

end Generic

section Complex

universe v

variable {E F G : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- Existence of the bounded-below polar package over a complex Hilbert space. -/
theorem lowerFramePolarData_nonempty
    (X : F →L[ℂ] E) {ε : ℝ}
    (hX : LowerFrameBound X ε) (hε : 0 < ε) :
    Nonempty (LowerFramePolarData X ε hX hε) :=
  ⟨lowerFramePolarData X hX hε⟩

/-- Inverse square root of the Gram operator. -/
noncomputable def gramInvSqrt
    (X : F →L[ℂ] E) {ε : ℝ}
    (hX : LowerFrameBound X ε) (hε : 0 < ε) :
    F →L[ℂ] F :=
  (lowerFramePolarData X hX hε).invSqrt

/-- Square root of the Gram operator. -/
noncomputable def gramSqrt
    (X : F →L[ℂ] E) {ε : ℝ}
    (hX : LowerFrameBound X ε) (hε : 0 < ε) : F →L[ℂ] F :=
  (lowerFramePolarData X hX hε).sqrt

/-- Isometric polar factor of a bounded-below trial map. -/
noncomputable def frameIsometry
    (X : F →L[ℂ] E) {ε : ℝ}
    (hX : LowerFrameBound X ε) (hε : 0 < ε) :
    F →L[ℂ] E :=
  X ∘L gramInvSqrt X hX hε

/-- For an isometric trial map, the lower-frame polar factor is the trial
map itself.  This is the bridge used to derive the isometric theorem from the
generalized lower-frame theorem rather than maintaining two independent
canonical proofs. -/
theorem frameIsometry_eq_of_isometry
    (X : F →L[ℂ] E) (hX : IsometricEmbedding X) :
    frameIsometry X (lowerFrameBound_one_of_isometry hX) zero_lt_one = X := by
  have hinv :
      gramInvSqrt X (lowerFrameBound_one_of_isometry hX) zero_lt_one =
        ContinuousLinearMap.id ℂ F :=
    (lowerFramePolarData X
      (lowerFrameBound_one_of_isometry hX) zero_lt_one).invSqrt_eq_id_of_isometry hX
  unfold frameIsometry
  rw [hinv]
  simp

/-- The polar factor preserves norms. -/
theorem frameIsometry_isometry
    (X : F →L[ℂ] E) {ε : ℝ}
    (hX : LowerFrameBound X ε) (hε : 0 < ε) :
    IsometricEmbedding (frameIsometry X hX hε) := by
  simpa [frameIsometry, gramInvSqrt] using
    (lowerFramePolarData X hX hε).normalized_isometry

/-- Polar factorization of the trial map. -/
theorem frameFactorization
    (X : F →L[ℂ] E) {ε : ℝ}
    (hX : LowerFrameBound X ε) (hε : 0 < ε) :
    X = frameIsometry X hX hε ∘L gramSqrt X hX hε := by
  simpa [frameIsometry, gramInvSqrt, gramSqrt] using
    (lowerFramePolarData X hX hε).factorization

/-- Quantitative inverse-square-root estimate. -/
theorem norm_gramInvSqrt_le
    (X : F →L[ℂ] E) {ε : ℝ}
    (hX : LowerFrameBound X ε) (hε : 0 < ε) :
    ‖gramInvSqrt X hX hε‖ ≤ ε⁻¹ := by
  simpa [gramInvSqrt] using
    (lowerFramePolarData X hX hε).invSqrt_norm_le

/-- The range of the polar factor agrees with the range of the trial map. -/
theorem range_frameIsometry_eq_range
    (X : F →L[ℂ] E) {ε : ℝ}
    (hX : LowerFrameBound X ε) (hε : 0 < ε) :
    LinearMap.range (frameIsometry X hX hε).toLinearMap =
      LinearMap.range X.toLinearMap := by
  simpa [frameIsometry, gramInvSqrt] using
    (lowerFramePolarData X hX hε).range_normalized

/-- Directed sine block used in the paper-facing generalized theorem. -/
@[expose]
noncomputable def sinThetaBlock
    (X : F →L[ℂ] E) (F₁ : G →L[ℂ] E) {ε : ℝ}
    (hX : LowerFrameBound X ε) (hε : 0 < ε) :
    G →L[ℂ] F :=
  (frameIsometry X hX hε).adjoint ∘L F₁

/-- Lower-frame transport from the raw complementary block to the sine block. -/
theorem lowerFrame_sinThetaBlock_mem_and_gauge_le
    (N : TauCeti.SymmetricOperatorIdealFamily.{0, v} ℂ)
    (X : F →L[ℂ] E) (F₁ : G →L[ℂ] E) {ε : ℝ}
    (hX : LowerFrameBound X ε) (hε : 0 < ε)
    (hRaw : N.Mem (X.adjoint ∘L F₁)) :
    N.Mem (sinThetaBlock X F₁ hX hε) ∧
      ε * N.gaugeReal (sinThetaBlock X F₁ hX hε)
        ≤ N.gaugeReal (X.adjoint ∘L F₁) := by
  have hBlock :
      sinThetaBlock X F₁ hX hε =
        (gramInvSqrt X hX hε).adjoint ∘L (X.adjoint ∘L F₁) := by
    unfold sinThetaBlock frameIsometry
    rw [ContinuousLinearMap.adjoint_comp]
    exact ContinuousLinearMap.comp_assoc _ _ _
  have hMem :
      N.Mem ((gramInvSqrt X hX hε).adjoint ∘L (X.adjoint ∘L F₁)) :=
    N.comp_left_mem (gramInvSqrt X hX hε).adjoint hRaw
  have hnorm : ‖(gramInvSqrt X hX hε).adjoint‖ ≤ ε⁻¹ := by
    simpa using norm_gramInvSqrt_le X hX hε
  have hgauge :
      N.gaugeReal (sinThetaBlock X F₁ hX hε) ≤
        ε⁻¹ * N.gaugeReal (X.adjoint ∘L F₁) := by
    rw [hBlock]
    exact (N.gaugeReal_comp_left_le_mul
      (gramInvSqrt X hX hε).adjoint hRaw).trans
        (mul_le_mul_of_nonneg_right hnorm (N.gaugeReal_nonneg hRaw))
  refine ⟨hBlock ▸ hMem, ?_⟩
  calc
    ε * N.gaugeReal (sinThetaBlock X F₁ hX hε)
        ≤ ε * (ε⁻¹ * N.gaugeReal (X.adjoint ∘L F₁)) :=
      mul_le_mul_of_nonneg_left hgauge hε.le
    _ = N.gaugeReal (X.adjoint ∘L F₁) := by
      rw [← mul_assoc, mul_inv_cancel₀ hε.ne', one_mul]

end Complex

end ExactSinTheta
end DavisKahan
end TauCeti

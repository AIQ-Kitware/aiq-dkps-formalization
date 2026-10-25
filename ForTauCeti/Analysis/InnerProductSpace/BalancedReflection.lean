/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.PairedInvolutionDecomposition
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.InnerProductSpace.Reflection

/-!
# Balanced reflections have only fixed and right-angle transport blocks

If an orthogonal projection `A` has compression `A*P*A=A/2`, its
range is orthogonal to its image under the source reflection `2*P-I`.
The reflection `I-2*A` acts by `(-I,I)` on those paired spaces and by
the identity on their orthogonal complement. Source reflection swaps
the paired coordinates and preserves the remaining space.

These are classical real/complex projection identities. The compression
and orthogonality facts are dimension-free; completing paired coordinates
uses the existing finite-dimensional decomposition.
-/

public section

noncomputable section

namespace TauCeti

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- Half compression makes the source reflection vanish between the
negative reflection projection on both sides. -/
theorem balanced_projection_source_reflection_mul_eq_zero
    (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]
    (A : E →L[𝕜] E) (hA : IsStarProjection A)
    (hbalance : (2 : 𝕜) • (A * K.starProjection * A) = A) :
    A * (K.reflection : E →L[𝕜] E) * A = 0 := by
  have hJ : (K.reflection : E →L[𝕜] E) = (2 : 𝕜) • K.starProjection - 1 := by
    simpa only [ofNat_smul_eq_nsmul] using Submodule.coe_reflection K
  calc
    _ = (2 : 𝕜) • (A * K.starProjection * A) - A := by
      rw [hJ]
      simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc,
        mul_one, hA.isIdempotentElem.eq]
    _ = 0 := by rw [hbalance, sub_self]

private theorem projection_apply_eq_self_of_mem_range
    (A : E →L[𝕜] E) (hA : IsStarProjection A) (x : A.range) : A x = x := by
  have hidem : IsIdempotentElem A.toLinearMap := by
    change (A * A).toLinearMap = A.toLinearMap
    exact congrArg ContinuousLinearMap.toLinearMap hA.isIdempotentElem.eq
  exact (LinearMap.IsIdempotentElem.mem_range_iff hidem).mp x.property

/-- The negative reflection space and its image under source reflection
are orthogonal. No dimension assumption is needed. -/
theorem balanced_projection_orthogonal_source_reflection
    (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]
    (A : E →L[𝕜] E) (hA : IsStarProjection A)
    (hbalance : (2 : 𝕜) • (A * K.starProjection * A) = A) :
    ∀ x y : A.range, ⟪(x : E), K.reflection y⟫_𝕜 = 0 := by
  have hAJ := balanced_projection_source_reflection_mul_eq_zero K A hA hbalance
  intro x y
  have hAx := projection_apply_eq_self_of_mem_range A hA x
  have hAy := projection_apply_eq_self_of_mem_range A hA y
  have hAJy : A (K.reflection y) = 0 := by
    have h := DFunLike.congr_fun hAJ (y : E)
    change A (K.reflection (A y)) = 0 at h
    rwa [hAy] at h
  calc
    _ = ⟪A x, K.reflection y⟫_𝕜 := by rw [hAx]
    _ = ⟪(x : E), A (K.reflection y)⟫_𝕜 := hA.isSelfAdjoint.isSymmetric _ _
    _ = 0 := by rw [hAJy, inner_zero_right]

/-- A balanced reflection has actual paired coordinates with action
`(-I,I)` and a fixed orthogonal remainder. The source reflection swaps
the pair and acts by an involution on that remainder. Empty and repeated
negative spaces are allowed, over both real and complex scalars. -/
theorem balanced_reflection_paired_decomposition [FiniteDimensional 𝕜 E]
    (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]
    (A : E →L[𝕜] E) (hA : IsStarProjection A)
    (hbalance : (2 : 𝕜) • (A * K.starProjection * A) = A)
    (R : E ≃ₗᵢ[𝕜] E) (hR : (R : E →L[𝕜] E) = 1 - (2 : 𝕜) • A) :
    ∃ horth : ∀ x y : A.range, ⟪(x : E), K.reflection y⟫_𝕜 = 0,
      let S := (pairedInvolutionEmbedding A.range K.reflection horth).toLinearMap.range
      let e := pairedInvolutionDecomposition A.range K.reflection horth
      ∃ J₀ : Sᗮ ≃ₗᵢ[𝕜] Sᗮ,
        Function.Involutive J₀ ∧ (∀ z, (J₀ z : E) = K.reflection z) ∧
        (∀ x, R (e x) = e (WithLp.toLp 2
          (WithLp.toLp 2 (-x.fst.fst, x.fst.snd), x.snd))) ∧
        (∀ x, K.reflection (e x) = e (WithLp.toLp 2
          (WithLp.toLp 2 (x.fst.snd, x.fst.fst), J₀ x.snd))) := by
  let horth := balanced_projection_orthogonal_source_reflection K A hA hbalance
  let S := (pairedInvolutionEmbedding A.range K.reflection horth).toLinearMap.range
  let e := pairedInvolutionDecomposition A.range K.reflection horth
  obtain ⟨J₀, hJ₀act, hJ₀inv, hJcoords⟩ :=
    pairedInvolutionDecomposition_involution A.range K.reflection horth K.reflection_involutive
  have hAJ := balanced_projection_source_reflection_mul_eq_zero K A hA hbalance
  have hRneg (x : A.range) : R x = -(x : E) := by
    change (R : E →L[𝕜] E) x = _
    rw [hR]
    change (x : E) - (2 : 𝕜) • A x = _
    rw [projection_apply_eq_self_of_mem_range A hA x, two_smul]
    abel
  have hRpos (y : A.range) : R (K.reflection y) = K.reflection y := by
    have hAzero : A (K.reflection y) = 0 := by
      have h := DFunLike.congr_fun hAJ (y : E)
      change A (K.reflection (A y)) = 0 at h
      rwa [projection_apply_eq_self_of_mem_range A hA y] at h
    change (R : E →L[𝕜] E) (K.reflection y) = _
    rw [hR]
    change K.reflection y - (2 : 𝕜) • A (K.reflection y) = _
    rw [hAzero, smul_zero, sub_zero]
  have hRfixed (z : Sᗮ) : R z = (z : E) := by
    have hsub : A.range ≤ S := by
      dsimp only [S]
      rw [pairedInvolutionEmbedding_range]
      exact le_sup_left
    have hzA : (z : E) ∈ A.rangeᗮ := by
      have hz := z.property
      rw [Submodule.mem_orthogonal] at hz ⊢
      intro y hy
      exact hz y (hsub hy)
    obtain ⟨hclosed, hAproj⟩ := isStarProjection_iff_eq_starProjection_range.mp hA
    let _ := hclosed
    have hAzero : A z = 0 := by
      rw [hAproj]
      exact A.range.starProjection_apply_eq_zero_iff.mpr hzA
    change (R : E →L[𝕜] E) z = _
    rw [hR]
    change (z : E) - (2 : 𝕜) • A z = _
    rw [hAzero, smul_zero, sub_zero]
  refine ⟨horth, J₀, hJ₀inv, hJ₀act, ?_, hJcoords⟩
  intro x
  rw [pairedInvolutionDecomposition_apply, map_add, map_add, hRneg, hRpos, hRfixed,
    pairedInvolutionDecomposition_apply]
  rfl

end TauCeti

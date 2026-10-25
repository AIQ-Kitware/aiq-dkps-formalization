/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.InvariantSubspace
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Normalization away from an operator kernel

Projection onto the orthogonal complement of a bounded operator's kernel
preserves its action. A commuting orthogonal projection can be normalized
to this complement, where its weighted action determines it uniquely.
These are real/complex Hilbert-space facts, without a dimension bound.
-/

public section

noncomputable section

open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- Projecting away from the kernel does not change a bounded operator. -/
theorem mul_starProjection_orthogonal_ker (W : E →L[𝕜] E) :
    W * W.kerᗮ.starProjection = W := by
  let : CompleteSpace W.ker := W.isClosed_ker.completeSpace_coe
  ext x
  have h := congrArg W (W.ker.starProjection_add_starProjection_orthogonal x)
  change W (W.ker.starProjection x + W.kerᗮ.starProjection x) = W x at h
  rw [map_add, show W (W.ker.starProjection x) = 0 from
    W.ker.starProjection_apply_mem x, zero_add] at h
  exact h

/-- A self-adjoint map commuting with `W` commutes with the projection
away from the kernel of `W`. -/
theorem commute_starProjection_orthogonal_ker_of_isSelfAdjoint
    (W P : E →L[𝕜] E) (hP : IsSelfAdjoint P) (hPW : Commute P W) :
    Commute W.kerᗮ.starProjection P := by
  let : CompleteSpace W.ker := W.isClosed_ker.completeSpace_coe
  have hker : W.ker ∈ Module.End.invtSubmodule P.toLinearMap := by
    intro x hx
    change W (P x) = 0
    have h := congrArg (fun A : E →L[𝕜] E => A x) hPW.eq
    change P (W x) = W (P x) at h
    rw [show W x = 0 from hx, map_zero] at h
    exact h.symm
  ext x
  exact hP.isSymmetric.starProjection_apply_comm
    (hP.isSymmetric.orthogonalComplement_mem_invtSubmodule hker) x

/-- A unitary commuting with `W` commutes with the projection away from
the kernel of `W`. Neither normality nor finite dimension is required. -/
theorem commute_starProjection_orthogonal_ker_of_unitary
    (W : E →L[𝕜] E) (V : E ≃ₗᵢ[𝕜] E) (hVW : Commute (V : E →L[𝕜] E) W) :
    Commute W.kerᗮ.starProjection (V : E →L[𝕜] E) := by
  let : CompleteSpace W.ker := W.isClosed_ker.completeSpace_coe
  have hmap : W.ker.map V.toLinearMap = W.ker := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change W (V x) = 0
      have h := congrArg (fun A : E →L[𝕜] E => A x) hVW.eq
      change V (W x) = W (V x) at h
      rw [show W x = 0 from hx, map_zero] at h
      exact h.symm
    · intro hy
      refine ⟨V.symm y, ?_, V.apply_symm_apply y⟩
      change W (V.symm y) = 0
      apply V.injective
      have h := congrArg (fun A : E →L[𝕜] E => A (V.symm y)) hVW.eq
      change V (W (V.symm y)) = W (V (V.symm y)) at h
      rw [V.apply_symm_apply, show W y = 0 from hy] at h
      simpa only [map_zero] using h
  have horthmap : W.kerᗮ.map V.toLinearMap = W.kerᗮ := by
    rw [W.ker.map_orthogonal_equiv V, hmap]
  ext x
  have h := Submodule.starProjection_map_apply V W.kerᗮ (V x)
  change (W.kerᗮ.map V.toLinearMap).starProjection (V x) =
    V (W.kerᗮ.starProjection (V.symm (V x))) at h
  change W.kerᗮ.starProjection (V x) = V (W.kerᗮ.starProjection x)
  simpa only [horthmap, V.symm_apply_apply] using h

/-- A commuting orthogonal projection has a normalized representative
supported away from the multiplier's kernel, with the same weighted
action. No finite-dimensional or normality hypothesis is required. -/
theorem normalized_starProjection
    (W P : E →L[𝕜] E) (hP : IsStarProjection P) (hPW : Commute P W) :
    let Q := W.kerᗮ.starProjection * P
    IsStarProjection Q ∧ (∀ x, Q x ∈ W.kerᗮ) ∧ W * Q = W * P := by
  have hAP := commute_starProjection_orthogonal_ker_of_isSelfAdjoint W P hP.isSelfAdjoint hPW
  refine ⟨IsStarProjection.mul isStarProjection_starProjection hP hAP,
    fun x => W.kerᗮ.starProjection_apply_mem (P x), ?_⟩
  rw [← mul_assoc, mul_starProjection_orthogonal_ker]

omit [CompleteSpace E] in
/-- Multiplication by `W` is injective on maps whose ranges lie in the
orthogonal complement of its kernel. -/
theorem eq_of_mul_eq_of_range_orthogonal_ker
    (W P Q : E →L[𝕜] E) (hPQ : W * P = W * Q)
    (hP : ∀ x, P x ∈ W.kerᗮ) (hQ : ∀ x, Q x ∈ W.kerᗮ) : P = Q := by
  ext x
  apply sub_eq_zero.mp
  have hker : P x - Q x ∈ W.ker := by
    change W (P x - Q x) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr (congrArg (fun A : E →L[𝕜] E => A x) hPQ)
  have horth := W.kerᗮ.sub_mem (hP x) (hQ x)
  exact inner_self_eq_zero.mp ((Submodule.mem_orthogonal _ _).mp horth _ hker)

/-- A self-adjoint map supported away from `W`'s kernel annihilates that
kernel. The map need not be an orthogonal projection. -/
theorem apply_eq_zero_of_range_orthogonal_ker
    (W P : E →L[𝕜] E) (hP : IsSelfAdjoint P)
    (hsupp : ∀ x, P x ∈ W.kerᗮ) (x : E) (hx : W x = 0) : P x = 0 := by
  apply (inner_self_eq_zero (𝕜 := 𝕜)).mp
  exact (hP.isSymmetric x (P x)).trans (hsupp (P x) x hx)

omit [CompleteSpace E] in
/-- A finite-dimensional effective input space gives uniform operator-norm
recovery from the weighted action. The ambient space may be infinite
dimensional; no bound is asserted for an infinite effective input space. -/
theorem exists_pos_norm_le_mul_norm_mul_on_orthogonal_ker
    (W : E →L[𝕜] E) [FiniteDimensional 𝕜 W.kerᗮ] :
    ∃ k : ℝ, 0 < k ∧ ∀ B : E →L[𝕜] E,
      (∀ x, B x ∈ W.kerᗮ) → ‖B‖ ≤ k * ‖W * B‖ := by
  let N := W.kerᗮ
  let f : N →ₗ[𝕜] E := W.toLinearMap.comp N.subtype
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply sub_eq_zero.mp
    have hker : (x : E) - (y : E) ∈ W.ker := by
      change W ((x : E) - (y : E)) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr hxy
    exact inner_self_eq_zero.mp
      ((Submodule.mem_orthogonal _ _).mp (N.sub_mem x.property y.property) _ hker)
  obtain ⟨k, hk, hanti⟩ := f.injective_iff_antilipschitz.mp hinj
  refine ⟨k, hk, fun B hB => ?_⟩
  apply B.opNorm_le_bound (mul_nonneg k.coe_nonneg (norm_nonneg _))
  intro x
  have h := ZeroHomClass.bound_of_antilipschitz f hanti (⟨B x, hB x⟩ : N)
  change ‖B x‖ ≤ (k : ℝ) * ‖W (B x)‖ at h
  calc
    ‖B x‖ ≤ (k : ℝ) * ‖W (B x)‖ := h
    _ ≤ (k : ℝ) * (‖W * B‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left ((W * B).le_opNorm x) k.coe_nonneg
    _ = ((k : ℝ) * ‖W * B‖) * ‖x‖ := (mul_assoc _ _ _).symm

end ContinuousLinearMap

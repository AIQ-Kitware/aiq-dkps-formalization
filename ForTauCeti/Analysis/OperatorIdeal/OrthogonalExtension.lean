/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import TauCeti.Analysis.OperatorIdeal.Family
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Orthogonal zero extension preserves singular values and ideal gauges

Extend an operator between orthogonally complemented subspaces by zero.
Compression recovers the original operator, and both operations use
contractions. Thus all approximation numbers and every accepted ideal
gauge are unchanged. Neither subspace has to be finite-dimensional.

These are classical ideal-property consequences, used for the
infinite-dimensional transport reduction; no priority claim is made.
-/

public section

namespace ContinuousLinearMap

variable {𝕜 E F G H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- An operator is the orthogonal zero extension of `T` precisely when
it agrees on the source subspace and vanishes on its orthogonal complement. -/
theorem eq_orthogonal_extension_iff
    (M : Submodule 𝕜 E) (N : Submodule 𝕜 F)
    [M.HasOrthogonalProjection] [N.HasOrthogonalProjection]
    (A : E →L[𝕜] F) (T : M →L[𝕜] N) :
    A = N.subtypeL ∘L T ∘L M.orthogonalProjectionOnto ↔
      (∀ x : M, A x = (T x : F)) ∧ (∀ x ∈ Mᗮ, A x = 0) := by
  constructor
  · rintro rfl
    constructor
    · intro x
      change (T (M.orthogonalProjectionOnto x) : F) = (T x : F)
      rw [M.orthogonalProjectionOnto_mem_subspace_eq_self]
    · intro x hx
      change (T (M.orthogonalProjectionOnto x) : F) = 0
      rw [M.orthogonalProjectionOnto_apply_of_mem_orthogonal hx, map_zero]
      rfl
  · rintro ⟨hM, hperp⟩
    ext x
    calc
      A x = A (M.starProjection x + Mᗮ.starProjection x) := by
        rw [M.starProjection_add_starProjection_orthogonal]
      _ = A (M.starProjection x) := by
        rw [map_add, hperp _ (Mᗮ.starProjection_apply_mem x), add_zero]
      _ = (T (M.orthogonalProjectionOnto x) : F) := hM _
      _ = _ := rfl

private theorem singularValue_contraction_sandwich_le
    (A : G →L[𝕜] H) (T : F →L[𝕜] G) (B : E →L[𝕜] F)
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (n : ℕ) :
    (A ∘L T ∘L B).singularValue n ≤ T.singularValue n := by
  calc
    _ ≤ ‖A‖₊ * T.singularValue n * ‖B‖₊ := singularValue_comp_comp_le A T B n
    _ ≤ 1 * T.singularValue n * 1 := by
      gcongr <;> exact_mod_cast (by assumption : ‖_‖ ≤ (1 : ℝ))
    _ = _ := by simp

/-- Orthogonal zero extension preserves every approximation number. -/
theorem singularValue_orthogonal_extension
    (M : Submodule 𝕜 E) (N : Submodule 𝕜 F)
    [M.HasOrthogonalProjection] [N.HasOrthogonalProjection]
    (T : M →L[𝕜] N) (n : ℕ) :
    (N.subtypeL ∘L T ∘L M.orthogonalProjectionOnto).singularValue n = T.singularValue n := by
  apply le_antisymm
    (singularValue_contraction_sandwich_le _ _ _ N.norm_subtypeL_le
      M.orthogonalProjectionOnto_norm_le n)
  have h := singularValue_contraction_sandwich_le N.orthogonalProjectionOnto
    (N.subtypeL ∘L T ∘L M.orthogonalProjectionOnto) M.subtypeL
    N.orthogonalProjectionOnto_norm_le M.norm_subtypeL_le n
  have heq : N.orthogonalProjectionOnto ∘L
      (N.subtypeL ∘L T ∘L M.orthogonalProjectionOnto) ∘L M.subtypeL = T := by
    ext x
    exact congrArg Subtype.val (by simp)
  rwa [heq] at h

/-- Orthogonal zero extension preserves the operator norm, even when
either subspace is infinite-dimensional or zero-dimensional. -/
theorem norm_orthogonal_extension
    (M : Submodule 𝕜 E) (N : Submodule 𝕜 F)
    [M.HasOrthogonalProjection] [N.HasOrthogonalProjection]
    (T : M →L[𝕜] N) :
    ‖N.subtypeL ∘L T ∘L M.orthogonalProjectionOnto‖ = ‖T‖ := by
  have h := singularValue_orthogonal_extension M N T 0
  rw [singularValue_zero, singularValue_zero] at h
  exact congrArg (fun x : NNReal => (x : ℝ)) h

end ContinuousLinearMap

namespace TauCeti.OperatorIdealFamily

universe u v

variable {𝕜 : Type u} [RCLike 𝕜] (Φ : OperatorIdealFamily.{u, v, v} 𝕜)
  {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Orthogonal zero extension preserves every operator-ideal gauge,
including infinite values. -/
theorem gauge_orthogonal_extension
    (M : Submodule 𝕜 E) (N : Submodule 𝕜 F)
    [M.HasOrthogonalProjection] [N.HasOrthogonalProjection]
    [CompleteSpace M] [CompleteSpace N]
    (T : M →L[𝕜] N) :
    Φ.gauge (N.subtypeL ∘L T ∘L M.orthogonalProjectionOnto) = Φ.gauge T := by
  apply le_antisymm
  · exact (Φ.gauge_comp_left_le_self N.norm_subtypeL_le _).trans
      (Φ.gauge_comp_right_le_self T M.orthogonalProjectionOnto_norm_le)
  · have h := (Φ.gauge_comp_left_le_self N.orthogonalProjectionOnto_norm_le
        ((N.subtypeL ∘L T ∘L M.orthogonalProjectionOnto) ∘L M.subtypeL)).trans
        (Φ.gauge_comp_right_le_self _ M.norm_subtypeL_le)
    have heq : N.orthogonalProjectionOnto ∘L
        ((N.subtypeL ∘L T ∘L M.orthogonalProjectionOnto) ∘L M.subtypeL) = T := by
      ext x
      exact congrArg Subtype.val (by simp)
    rwa [heq] at h

end TauCeti.OperatorIdealFamily

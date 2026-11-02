/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5

Staged for Tau Ceti: additions to the principal-angle API.
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.AngleGeometry
public import ForTauCeti.Analysis.InnerProductSpace.SinTheta.Perturbation
public import TauCeti.Analysis.InnerProductSpace.Projection.FrobeniusSine

/-! # The single-angle case: sine norms of a line against a subspace

When the source subspace is a line `𝕜 ∙ v`, the sine cross-projection
`sinThetaMap (𝕜 ∙ v) W = P_{Wᗮ} P_{𝕜∙v}` is the rank-one map
`x ↦ ⟪v, x⟫ • P_{Wᗮ} v`.  A rank-one operator has a single nonzero singular
value, so *every* normalized unitarily invariant norm of it is the same number
— here `‖P_{Wᗮ} v‖`, the sine of the one principal angle.

That collapse is what makes the single-vector Davis--Kahan statements
unambiguous: the paper writes `sin Θ(v̂, v)` without saying which norm, and for
`d = 1` it does not matter.  The two lemmas below prove it for the two norms the
statements actually use: the operator norm follows from the rank-one action,
and Frobenius sine from TauCeti's spanning-family projection formula.

## Main results

* `TauCeti.sinThetaMap_span_singleton_apply`: the rank-one formula.
* `TauCeti.norm_starProjection_orthogonal_sq`: `‖P_{Wᗮ} v‖² = 1 - ‖P_W v‖²`.
* `TauCeti.opNorm_sinThetaMap_span_singleton` and
  `TauCeti.sinThetaFrobenius_span_singleton`: both norms equal `‖P_{Wᗮ} v‖`.
-/

public section

open Module (finrank)
open scoped InnerProductSpace BigOperators

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {W : Submodule 𝕜 E} [W.HasOrthogonalProjection]

omit [FiniteDimensional 𝕜 E] in
/-- **The single-angle sine map is rank one.**  On the line `𝕜 ∙ v` with `v` a
unit vector, `sinThetaMap` sends `x` to `⟪v, x⟫ • P_{Wᗮ} v`. -/
theorem sinThetaMap_span_singleton_apply {v : E} (hv : ‖v‖ = 1) (x : E) :
    ((𝕜 ∙ v).sinThetaMap W) x = ⟪v, x⟫_𝕜 • Wᗮ.starProjection.toLinearMap v := by
  have hproj : ((𝕜 ∙ v)).starProjection.toLinearMap x = ⟪v, x⟫_𝕜 • v := by
    change (𝕜 ∙ v).starProjection x = _
    rw [Submodule.starProjection_singleton, hv]
    simp
  rw [Submodule.sinThetaMap_def]
  change Wᗮ.starProjection.toLinearMap (((𝕜 ∙ v)).starProjection.toLinearMap x) = _
  rw [hproj, map_smul]

omit [FiniteDimensional 𝕜 E] in
/-- Pythagoras for a projector: the complementary component of a unit vector has
squared norm `1 - ‖P_W v‖²`. -/
theorem norm_starProjection_orthogonal_sq {v : E} (hv : ‖v‖ = 1) :
    ‖Wᗮ.starProjection.toLinearMap v‖ ^ 2 = 1 - ‖W.starProjection.toLinearMap v‖ ^ 2 := by
  have hpy := W.norm_sq_eq_add_norm_sq_starProjection v
  rw [hv, one_pow] at hpy
  change ‖Wᗮ.starProjection v‖ ^ 2 = 1 - ‖W.starProjection v‖ ^ 2
  linarith

omit [FiniteDimensional 𝕜 E] in
/-- **The operator norm of the single-angle sine map** is the length of the
complementary component. -/
theorem opNorm_sinThetaMap_span_singleton {v : E} (hv : ‖v‖ = 1) :
    ‖((𝕜 ∙ v).sinThetaMap W)‖ = ‖Wᗮ.starProjection.toLinearMap v‖ := by
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_) ?_
  · rw [sinThetaMap_span_singleton_apply hv,
      norm_smul, mul_comm]
    have hcs : ‖⟪v, x⟫_𝕜‖ ≤ ‖x‖ := by
      have hle := norm_inner_le_norm (𝕜 := 𝕜) v x
      rwa [hv, one_mul] at hle
    exact mul_le_mul_of_nonneg_left hcs (norm_nonneg _)
  · -- The bound is attained at `v` itself.
    have h := ((𝕜 ∙ v).sinThetaMap W).le_opNorm v
    rw [sinThetaMap_span_singleton_apply hv,
      norm_smul, hv, mul_one] at h
    have hvv : ‖⟪v, v⟫_𝕜‖ = 1 := by
      rw [inner_self_eq_norm_sq_to_K, hv]
      simp
    rwa [hvv, one_mul] at h

/-- **The Frobenius norm of the single-angle sine map** is the same number: a
rank-one operator has one singular value, so the two norms agree. -/
theorem sinThetaFrobenius_span_singleton {v : E} (hv : ‖v‖ = 1) :
    Submodule.sinThetaFrobenius (𝕜 ∙ v) W = ‖Wᗮ.starProjection.toLinearMap v‖ := by
  have hfamily : Orthonormal 𝕜 (fun _ : Fin 1 => v) :=
    orthonormal_subsingleton_iff.mpr fun _ => hv
  have hspan : Submodule.span 𝕜 (Set.range (fun _ : Fin 1 => v)) = 𝕜 ∙ v := by
    simp
  have h := (𝕜 ∙ v).sq_sinThetaFrobenius_eq_sum_projection_of_orthonormal W hfamily hspan
  simp only [Fin.sum_univ_one] at h
  exact (sq_eq_sq₀ (Submodule.sinThetaFrobenius_nonneg _ _) (norm_nonneg _)).mp h

end TauCeti

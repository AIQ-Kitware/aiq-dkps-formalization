/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5

Staged for Tau Ceti: a new file alongside the orthogonal-projection API.
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! # Gluing isometries across an orthogonal decomposition

Given `A ≤ H` with an orthogonal projection, `A' ≤ H'` likewise, and isometric
equivalences `f : A ≃ₗᵢ A'` and `g : Aᗮ ≃ₗᵢ A'ᗮ`, there is a global
`H ≃ₗᵢ H'` restricting to `f` on `A` and to `g` on `Aᗮ`.  It is built pointwise,
`x ↦ f (P_A x) + g (P_{Aᗮ} x)`, and is isometric by Pythagoras because the two
images land in orthogonal subspaces.

This is the step that turns a *list* of matched summands into a single unitary,
which is what a classification theorem has to produce.  In particular it is
brick (2) of the converse of the Halmos two-projection classification: on the
four elementary Halmos summands a glued map automatically intertwines both
projections, so the whole assembly reduces to iterating this lemma.

## Main results

* `TauCeti.orthogonalGlue`: the glued isometric equivalence.
* `TauCeti.orthogonalGlue_apply_of_mem` / `_of_mem_orthogonal`: it restricts to
  `f` and to `g`.
* `TauCeti.map_orthogonalGlue`: it carries `A` onto `A'` (and `Aᗮ` onto `A'ᗮ`).
-/

public section

open scoped InnerProductSpace

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace 𝕜 H']
variable {A : Submodule 𝕜 H} [A.HasOrthogonalProjection]
  [Aᗮ.HasOrthogonalProjection]
variable {A' : Submodule 𝕜 H'} [A'.HasOrthogonalProjection]
  [A'ᗮ.HasOrthogonalProjection]

/-- The underlying linear map of the glue: send `x` to `f` of its `A`-component
plus `g` of its `Aᗮ`-component. -/
noncomputable def orthogonalGlueMap (f : A ≃ₗᵢ[𝕜] A') (g : Aᗮ ≃ₗᵢ[𝕜] A'ᗮ) :
    H →ₗ[𝕜] H' :=
  (A'.subtype ∘ₗ (f.toLinearEquiv : A →ₗ[𝕜] A') ∘ₗ
      (A.orthogonalProjectionOnto : H →ₗ[𝕜] A)) +
    (A'ᗮ.subtype ∘ₗ (g.toLinearEquiv : Aᗮ →ₗ[𝕜] A'ᗮ) ∘ₗ
      (Aᗮ.orthogonalProjectionOnto : H →ₗ[𝕜] Aᗮ))

omit [A'.HasOrthogonalProjection] [A'ᗮ.HasOrthogonalProjection] in
theorem orthogonalGlueMap_apply (f : A ≃ₗᵢ[𝕜] A') (g : Aᗮ ≃ₗᵢ[𝕜] A'ᗮ) (x : H) :
    orthogonalGlueMap f g x =
      (f (A.orthogonalProjectionOnto x) : H') +
        (g (Aᗮ.orthogonalProjectionOnto x) : H') := by
  simp [orthogonalGlueMap]

omit [A'.HasOrthogonalProjection] [A'ᗮ.HasOrthogonalProjection] in
/-- The glue is norm-preserving: the two components land in orthogonal
subspaces, so Pythagoras applies on both sides. -/
theorem norm_orthogonalGlueMap (f : A ≃ₗᵢ[𝕜] A') (g : Aᗮ ≃ₗᵢ[𝕜] A'ᗮ) (x : H) :
    ‖orthogonalGlueMap f g x‖ = ‖x‖ := by
  have hperp' : ⟪(f (A.orthogonalProjectionOnto x) : H'),
      (g (Aᗮ.orthogonalProjectionOnto x) : H')⟫_𝕜 = 0 :=
    Submodule.inner_right_of_mem_orthogonal
      (f (A.orthogonalProjectionOnto x)).2 (g (Aᗮ.orthogonalProjectionOnto x)).2
  have hperp : ⟪(A.starProjection x), (Aᗮ.starProjection x)⟫_𝕜 = 0 :=
    Submodule.inner_right_of_mem_orthogonal (A.starProjection_apply_mem x)
      (Aᗮ.starProjection_apply_mem x)
  have hsplit : A.starProjection x + Aᗮ.starProjection x = x := by simp
  have hsq : ‖orthogonalGlueMap f g x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [orthogonalGlueMap_apply, @norm_add_sq 𝕜, hperp']
    conv_rhs => rw [← hsplit]
    rw [@norm_add_sq 𝕜, hperp]
    -- The isometries preserve each component's norm.
    have h1 : ‖(f (A.orthogonalProjectionOnto x) : H')‖ = ‖A.starProjection x‖ := by
      rw [Submodule.norm_coe, f.norm_map, Submodule.coe_norm,
        Submodule.coe_orthogonalProjectionOnto_apply]
    have h2 : ‖(g (Aᗮ.orthogonalProjectionOnto x) : H')‖ = ‖Aᗮ.starProjection x‖ := by
      rw [Submodule.norm_coe, g.norm_map, Submodule.coe_norm,
        Submodule.coe_orthogonalProjectionOnto_apply]
    rw [h1, h2]
  have h1 : (0 : ℝ) ≤ ‖orthogonalGlueMap f g x‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ ‖x‖ := norm_nonneg _
  nlinarith

/-- The glue as a linear isometry. -/
noncomputable def orthogonalGlueIsometry (f : A ≃ₗᵢ[𝕜] A') (g : Aᗮ ≃ₗᵢ[𝕜] A'ᗮ) :
    H →ₗᵢ[𝕜] H' where
  toLinearMap := orthogonalGlueMap f g
  norm_map' := norm_orthogonalGlueMap f g

omit [A'.HasOrthogonalProjection] [A'ᗮ.HasOrthogonalProjection] in
theorem orthogonalGlueIsometry_apply (f : A ≃ₗᵢ[𝕜] A') (g : Aᗮ ≃ₗᵢ[𝕜] A'ᗮ)
    (x : H) :
    orthogonalGlueIsometry f g x =
      (f (A.orthogonalProjectionOnto x) : H') +
        (g (Aᗮ.orthogonalProjectionOnto x) : H') := by
  simp [orthogonalGlueIsometry, orthogonalGlueMap]

omit [A'.HasOrthogonalProjection] [A'ᗮ.HasOrthogonalProjection] in
/-- On `A` the glue is `f`. -/
theorem orthogonalGlueIsometry_apply_of_mem (f : A ≃ₗᵢ[𝕜] A')
    (g : Aᗮ ≃ₗᵢ[𝕜] A'ᗮ) {x : H} (hx : x ∈ A) :
    orthogonalGlueIsometry f g x = (f ⟨x, hx⟩ : H') := by
  have hA : A.orthogonalProjectionOnto x = ⟨x, hx⟩ := by
    apply Subtype.ext
    simpa using Submodule.starProjection_eq_self_iff.mpr hx
  have hAperp : Aᗮ.orthogonalProjectionOnto x = 0 := by
    apply Subtype.ext
    have : Aᗮ.starProjection x = 0 := by
      rw [Submodule.starProjection_apply_eq_zero_iff]
      simpa using hx
    simpa using this
  rw [orthogonalGlueIsometry_apply, hA, hAperp]
  simp

omit [A'.HasOrthogonalProjection] [A'ᗮ.HasOrthogonalProjection] in
/-- On `Aᗮ` the glue is `g`. -/
theorem orthogonalGlueIsometry_apply_of_mem_orthogonal (f : A ≃ₗᵢ[𝕜] A')
    (g : Aᗮ ≃ₗᵢ[𝕜] A'ᗮ) {x : H} (hx : x ∈ Aᗮ) :
    orthogonalGlueIsometry f g x = (g ⟨x, hx⟩ : H') := by
  have hAperp : Aᗮ.orthogonalProjectionOnto x = ⟨x, hx⟩ := by
    apply Subtype.ext
    simpa using Submodule.starProjection_eq_self_iff.mpr hx
  have hA : A.orthogonalProjectionOnto x = 0 := by
    apply Subtype.ext
    have : A.starProjection x = 0 := by
      rw [Submodule.starProjection_apply_eq_zero_iff]
      exact hx
    simpa using this
  rw [orthogonalGlueIsometry_apply, hA, hAperp]
  simp

/-- The glue is surjective: split the target across `A'` and `A'ᗮ` and pull each
piece back. -/
theorem orthogonalGlueIsometry_surjective (f : A ≃ₗᵢ[𝕜] A')
    (g : Aᗮ ≃ₗᵢ[𝕜] A'ᗮ) : Function.Surjective (orthogonalGlueIsometry f g) := by
  intro y
  refine ⟨(f.symm (A'.orthogonalProjectionOnto y) : H) +
    (g.symm (A'ᗮ.orthogonalProjectionOnto y) : H), ?_⟩
  rw [map_add,
    orthogonalGlueIsometry_apply_of_mem f g (f.symm (A'.orthogonalProjectionOnto y)).2,
    orthogonalGlueIsometry_apply_of_mem_orthogonal f g
      (g.symm (A'ᗮ.orthogonalProjectionOnto y)).2]
  simp

/-- **The glued isometric equivalence.** -/
noncomputable def orthogonalGlue (f : A ≃ₗᵢ[𝕜] A') (g : Aᗮ ≃ₗᵢ[𝕜] A'ᗮ) :
    H ≃ₗᵢ[𝕜] H' :=
  LinearIsometryEquiv.ofSurjective (orthogonalGlueIsometry f g)
    (orthogonalGlueIsometry_surjective f g)

@[simp] theorem orthogonalGlue_apply (f : A ≃ₗᵢ[𝕜] A') (g : Aᗮ ≃ₗᵢ[𝕜] A'ᗮ)
    (x : H) : orthogonalGlue f g x = orthogonalGlueIsometry f g x := by
  simp [orthogonalGlue]

theorem orthogonalGlue_apply_of_mem (f : A ≃ₗᵢ[𝕜] A') (g : Aᗮ ≃ₗᵢ[𝕜] A'ᗮ)
    {x : H} (hx : x ∈ A) : orthogonalGlue f g x = (f ⟨x, hx⟩ : H') :=
  orthogonalGlueIsometry_apply_of_mem f g hx

theorem orthogonalGlue_apply_of_mem_orthogonal (f : A ≃ₗᵢ[𝕜] A')
    (g : Aᗮ ≃ₗᵢ[𝕜] A'ᗮ) {x : H} (hx : x ∈ Aᗮ) :
    orthogonalGlue f g x = (g ⟨x, hx⟩ : H') :=
  orthogonalGlueIsometry_apply_of_mem_orthogonal f g hx

/-- **The glue carries `A` onto `A'`.**  This is what a classification proof
needs: the assembled unitary matches the prescribed subspaces. -/
theorem map_orthogonalGlue (f : A ≃ₗᵢ[𝕜] A') (g : Aᗮ ≃ₗᵢ[𝕜] A'ᗮ) :
    A.map (orthogonalGlue f g).toLinearMap = A' := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    rw [show (orthogonalGlue f g).toLinearMap x = orthogonalGlue f g x from rfl,
      orthogonalGlue_apply_of_mem f g hx]
    exact (f ⟨x, hx⟩).2
  · intro y hy
    refine ⟨(f.symm ⟨y, hy⟩ : H), (f.symm ⟨y, hy⟩).2, ?_⟩
    rw [show (orthogonalGlue f g).toLinearMap (f.symm ⟨y, hy⟩ : H) =
      orthogonalGlue f g (f.symm ⟨y, hy⟩ : H) from rfl,
      orthogonalGlue_apply_of_mem f g (f.symm ⟨y, hy⟩).2]
    simp

/-- The glue carries `Aᗮ` onto `A'ᗮ`. -/
theorem map_orthogonalGlue_orthogonal (f : A ≃ₗᵢ[𝕜] A') (g : Aᗮ ≃ₗᵢ[𝕜] A'ᗮ) :
    Aᗮ.map (orthogonalGlue f g).toLinearMap = A'ᗮ := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    rw [show (orthogonalGlue f g).toLinearMap x = orthogonalGlue f g x from rfl,
      orthogonalGlue_apply_of_mem_orthogonal f g hx]
    exact (g ⟨x, hx⟩).2
  · intro y hy
    refine ⟨(g.symm ⟨y, hy⟩ : H), (g.symm ⟨y, hy⟩).2, ?_⟩
    rw [show (orthogonalGlue f g).toLinearMap (g.symm ⟨y, hy⟩ : H) =
      orthogonalGlue f g (g.symm ⟨y, hy⟩ : H) from rfl,
      orthogonalGlue_apply_of_mem_orthogonal f g (g.symm ⟨y, hy⟩).2]
    simp

end TauCeti

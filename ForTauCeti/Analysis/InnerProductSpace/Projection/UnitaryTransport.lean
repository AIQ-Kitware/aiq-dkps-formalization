/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# Subspace transport as reflection intertwining

An ambient isometric equivalence carries one subspace onto another exactly
when it intertwines their reflections.
-/

public section

namespace Submodule

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F]

/-- An isometric equivalence transports subspaces exactly when it
intertwines their orthogonal reflections. -/
theorem map_eq_iff_intertwines_reflection
    (U : Submodule 𝕜 E) (V : Submodule 𝕜 F)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (W : E ≃ₗᵢ[𝕜] F) :
    U.map W.toLinearMap = V ↔ ∀ x, W (U.reflection x) = V.reflection (W x) := by
  constructor
  · intro h x
    have href := reflection_map_apply W U (W x)
    change (U.map W.toLinearMap).reflection (W x) = _ at href
    simpa only [h, W.symm_apply_apply] using href.symm
  · intro h
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      apply (reflection_eq_self_iff _).mp
      change V.reflection (W x) = W x
      rw [← h, reflection_mem_subspace_eq_self hx]
    · intro hy
      refine ⟨W.symm y, ?_, W.apply_symm_apply y⟩
      apply (reflection_eq_self_iff _).mp
      apply W.injective
      rw [h, W.apply_symm_apply, reflection_mem_subspace_eq_self hy]

/-- The relative unitary of two transports of the same subspaces commutes
with the source reflection. No dimension or completeness assumption is needed. -/
theorem relative_transport_commutes_reflection
    (U : Submodule 𝕜 E) (V : Submodule 𝕜 F)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (R T : E ≃ₗᵢ[𝕜] F) (hR : U.map R.toLinearMap = V) (hT : U.map T.toLinearMap = V)
    (x : E) :
    (R.trans T.symm) (U.reflection x) = U.reflection ((R.trans T.symm) x) := by
  have hRref := (U.map_eq_iff_intertwines_reflection V R).mp hR
  have hTref := (U.map_eq_iff_intertwines_reflection V T).mp hT
  apply T.injective
  change T (T.symm (R (U.reflection x))) = T (U.reflection (T.symm (R x)))
  rw [T.apply_symm_apply, hTref, T.apply_symm_apply, hRref]

/-- Affine phase parameters of relative unitaries cannot change faster
than the ambient unitaries. This estimate is valid over either field,
without finite dimension or completeness. -/
theorem relative_phase_projection_separation
    (N : Submodule 𝕜 E) (R T₁ T₂ : E ≃ₗᵢ[𝕜] E)
    (Q₁ Q₂ : N →L[𝕜] N) (alpha kappa : 𝕜)
    (h₁ : ∀ x : N, (R.trans T₁.symm) x = alpha • (x : E) + kappa • (Q₁ x : E))
    (h₂ : ∀ x : N, (R.trans T₂.symm) x = alpha • (x : E) + kappa • (Q₂ x : E)) :
    ‖kappa‖ * ‖Q₁ - Q₂‖ ≤ ‖(T₁ : E →L[𝕜] E) - (T₂ : E →L[𝕜] E)‖ := by
  have hbound : ‖kappa • (Q₁ - Q₂)‖ ≤ ‖(T₁ : E →L[𝕜] E) - (T₂ : E →L[𝕜] E)‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    let Z₁ := R.trans T₁.symm
    let Z₂ := R.trans T₂.symm
    have hvec : ((kappa • (Q₁ - Q₂)) x : E) = Z₁ x - Z₂ x := by
      change kappa • ((Q₁ x : E) - (Q₂ x : E)) = _
      rw [show Z₁ x = _ from h₁ x, show Z₂ x = _ from h₂ x]
      simp only [smul_sub]
      rw [add_sub_add_left_eq_sub]
    calc
      ‖(kappa • (Q₁ - Q₂)) x‖ = ‖Z₁ x - Z₂ x‖ := by rw [← hvec]; rfl
      _ = ‖T₁ (Z₁ x - Z₂ x)‖ := (T₁.norm_map _).symm
      _ = ‖((T₂ : E →L[𝕜] E) - (T₁ : E →L[𝕜] E)) (Z₂ x)‖ := by
        congr 1
        change T₁ (T₁.symm (R x) - T₂.symm (R x)) =
          T₂ (T₂.symm (R x)) - T₁ (T₂.symm (R x))
        rw [map_sub, T₁.apply_symm_apply, T₂.apply_symm_apply]
      _ ≤ ‖(T₂ : E →L[𝕜] E) - (T₁ : E →L[𝕜] E)‖ * ‖Z₂ x‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖(T₁ : E →L[𝕜] E) - (T₂ : E →L[𝕜] E)‖ * ‖x‖ := by
        rw [Z₂.norm_map, norm_sub_rev]
        rfl
  simpa only [norm_smul] using hbound

end Submodule

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

end Submodule

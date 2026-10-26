/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.ReducingUnitaryRestriction

/-!
# Unitaries agreeing on a reducing complementary sector

Agreement with a reducing reference unitary on the complementary sector
forces the retained sector to reduce the competitor as well. The
reference tail's actual inverse, rather than invariance alone, supplies
surjectivity. All sectors may be infinite-dimensional.
-/

public section

noncomputable section

namespace LinearIsometryEquiv

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Agreement on the orthogonal complement of a reducing sector forces
the other unitary to reduce that same sector, without a rank assumption. -/
theorem isReducing_of_eq_on_orthogonal
    (U R : E ≃ₗᵢ[𝕜] E) (M : Submodule 𝕜 E) [M.HasOrthogonalProjection]
    (hR : M.IsReducing R.toLinearMap)
    (hU : ∀ x ∈ Mᗮ, U x = R x) : M.IsReducing U.toLinearMap := by
  obtain ⟨T, hT, _⟩ := R.exists_restriction_of_reducing Mᗮ
    ((Submodule.isReducing_orthogonal_iff M R.toLinearMap).mpr hR)
  apply (M.isReducing_iff U.toLinearMap).mpr
  constructor
  · intro x hx
    change U x ∈ M
    have hperp : U x ∈ Mᗮᗮ := by
      intro y hy
      let z := T.symm ⟨y, hy⟩
      have hUz : U (z : E) = y := by
        rw [hU z z.property, ← hT]
        exact congrArg Subtype.val (T.apply_symm_apply ⟨y, hy⟩)
      rw [← hUz, U.inner_map_map]
      exact M.inner_left_of_mem_orthogonal hx z.property
    simpa only [M.orthogonal_orthogonal] using hperp
  · intro x hx
    change U x ∈ Mᗮ
    rw [hU x hx]
    exact hR.orthogonal_mem_invtSubmodule hx

end LinearIsometryEquiv

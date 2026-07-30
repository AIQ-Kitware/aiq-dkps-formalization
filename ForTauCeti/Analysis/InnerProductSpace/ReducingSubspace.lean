/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import Mathlib

/-!
# Reducing subspaces for bounded operators

General `RCLike` infrastructure for invariant and reducing subspaces of bounded
operators on inner-product spaces.  This module is independent of the
Davis--Kahan theory.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForMathlib` at Davis--Kahan commit
  `df036cd`; it has had no prior home.
* Extraction class: **authored in place**, for Tau Ceti — `ForMathlib` was
  retired on 2026-07-29 and `ForTauCeti` is the single staging library, whose
  destination is Tau Ceti and not Mathlib (`ForTauCeti/README.md`).
* Original authors / copyright: Jon Crall, GPT 5.6 High; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Spectra influence: **none** — the `ForTauCeti` import firewall admits only
  Mathlib, `TauCeti` and `ForTauCeti` (enforced by `scripts/check_dependency_layers.py`).
-/


open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace ContinuousLinearMap

/-- A subspace reduces a bounded operator when it and its orthogonal complement
are invariant. -/
def Reduces (A : E →L[𝕜] E) (U : Submodule 𝕜 E) : Prop :=
  (∀ x ∈ U, A x ∈ U) ∧ (∀ x ∈ Uᗮ, A x ∈ Uᗮ)

/-- An invariant subspace of a symmetric operator is reducing. -/
theorem IsSymmetric.reduces_of_invariant {A : E →L[𝕜] E}
    (hA : A.IsSymmetric) {U : Submodule 𝕜 E}
    (hU : ∀ x ∈ U, A x ∈ U) : A.Reduces U := by
  refine ⟨hU, ?_⟩
  intro x hx
  rw [Submodule.mem_orthogonal]
  intro u hu
  -- states the goal as the inner-product identity the structure lemma expects.
  change ⟪u, (A : E →ₗ[𝕜] E) x⟫_𝕜 = 0
  rw [← hA u x]
  exact Submodule.inner_right_of_mem_orthogonal (hU u hu) hx

/-- The orthogonal projection onto a reducing subspace commutes with the
operator. -/
theorem starProjection_comp_comm_of_reduces
    (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (hU : A.Reduces U) :
    U.starProjection ∘L A = A ∘L U.starProjection := by
  ext x
  -- states the goal with the definition unfolded, in the shape the next step needs;
  -- there is no `_apply` lemma to rewrite with here.
  change U.starProjection (A x) = A (U.starProjection x)
  have hpx : U.starProjection x ∈ U := U.starProjection_apply_mem x
  have hrest : x - U.starProjection x ∈ Uᗮ :=
    U.sub_starProjection_mem_orthogonal x
  have hApx : A (U.starProjection x) ∈ U := hU.1 _ hpx
  have hArest : A (x - U.starProjection x) ∈ Uᗮ := hU.2 _ hrest
  have hsplit : A x = A (U.starProjection x) + A (x - U.starProjection x) := by
    rw [← map_add]
    congr 1
    abel
  rw [hsplit, map_add,
    Submodule.starProjection_eq_self_iff.mpr hApx,
    (Submodule.starProjection_apply_eq_zero_iff U).mpr hArest,
    add_zero]

/-- Pointwise form of `starProjection_comp_comm_of_reduces`. -/
theorem starProjection_apply_comm_of_reduces
    (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (hU : A.Reduces U) (x : E) :
    U.starProjection (A x) = A (U.starProjection x) := by
  have h := congrArg (fun T : E →L[𝕜] E => T x)
    (starProjection_comp_comm_of_reduces A U hU)
  simpa only [ContinuousLinearMap.comp_apply] using h

/-- Restricting a symmetric operator to an invariant subspace preserves
symmetry. -/
theorem IsSymmetric.restrict_of_invariant {A : E →L[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} (hU : ∀ x ∈ U, A x ∈ U) :
    (A.restrict hU).IsSymmetric := by
  intro x y
  -- states the goal as the inner-product identity the structure lemma expects.
  change ⟪A (x : E), (y : E)⟫_𝕜 = ⟪(x : E), A (y : E)⟫_𝕜
  exact hA x y

end ContinuousLinearMap

namespace Submodule

/-- A subspace admitting an orthogonal projection is complete when the ambient
space is complete. -/
theorem isComplete_coe_of_hasOrthogonalProjection [CompleteSpace E]
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    IsComplete (U : Set E) := by
  have hclosed : IsClosed ((Uᗮ)ᗮ : Set E) := Uᗮ.isClosed_orthogonal
  simpa using hclosed.isComplete

end Submodule


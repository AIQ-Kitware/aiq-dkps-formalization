/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.FiniteUnitaryRestriction

/-!
# Finite reducing supports for unitary transport

A finite-rank unitary perturbation and an orthogonal projection admit
a common finite reducing support, containing any prescribed finite
subspace. The unitary acts as identity off that support. This is the
geometric finite-section step for unrestricted transport optimization.

## Provenance

Classical finite-rank linear algebra: saturate a finite subspace by one
idempotent, and use unitary invariance. No priority claim is made here.
-/

public section

noncomputable section

namespace LinearIsometryEquiv

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A unitary fixes the orthogonal complement of any subspace containing
the range of its displacement. No closedness or dimension is required. -/
theorem apply_eq_self_of_mem_orthogonal_displacement
    (U : E ≃ₗᵢ[𝕜] E) (M : Submodule 𝕜 E)
    (hM : (1 - U.toLinearMap).range ≤ M) {x : E} (hx : x ∈ Mᗮ) : U x = x := by
  apply ext_inner_left 𝕜
  intro y
  have h := M.inner_right_of_mem_orthogonal
    (hM (LinearMap.mem_range_self (1 - U.toLinearMap) (U.symm y))) hx
  change inner 𝕜 (U.symm y - U (U.symm y)) x = 0 at h
  rw [U.apply_symm_apply, inner_sub_left, sub_eq_zero] at h
  calc
    inner 𝕜 y (U x) = inner 𝕜 (U (U.symm y)) (U x) := by rw [U.apply_symm_apply]
    _ = inner 𝕜 (U.symm y) x := U.inner_map_map _ _
    _ = inner 𝕜 y x := h

/-- Every subspace containing the displacement range of a unitary
reduces that unitary. Its orthogonal complement is fixed pointwise. -/
theorem isReducing_of_displacement_range_le
    (U : E ≃ₗᵢ[𝕜] E) (M : Submodule 𝕜 E)
    (hM : (1 - U.toLinearMap).range ≤ M) : M.IsReducing U.toLinearMap := by
  apply (M.isReducing_iff U.toLinearMap).mpr
  constructor
  · intro x hx
    change U x ∈ M
    have hdiff := hM (LinearMap.mem_range_self (1 - U.toLinearMap) x)
    change x - U x ∈ M at hdiff
    simpa only [sub_sub_cancel] using M.sub_mem hx hdiff
  · intro x hx
    change U x ∈ Mᗮ
    rwa [U.apply_eq_self_of_mem_orthogonal_displacement M hM hx]

end LinearIsometryEquiv

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Enlarge any finite core to a common finite reducing support for a
finite-rank unitary perturbation and a source orthogonal projection.
In particular all nontrivial action of the unitary is inside the support. -/
theorem exists_finite_transport_support
    (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]
    (F : Submodule 𝕜 E) [FiniteDimensional 𝕜 F]
    (U : E ≃ₗᵢ[𝕜] E) (n : ℕ) (hU : (1 - U.toLinearMap).rank ≤ n) :
    ∃ M : Submodule 𝕜 E, FiniteDimensional 𝕜 M ∧ F ≤ M ∧
      M.IsReducing K.starProjection.toLinearMap ∧ M.IsReducing U.toLinearMap ∧
      (1 - U.toLinearMap).range ≤ M ∧ (∀ x ∈ Mᗮ, U x = x) := by
  let D := (1 - U.toLinearMap).range
  have hD : Module.rank 𝕜 D < Cardinal.aleph0 :=
    hU.trans_lt Cardinal.natCast_lt_aleph0
  let : FiniteDimensional 𝕜 D := Module.rank_lt_aleph0_iff.mp hD
  let G := F ⊔ D
  let M := G ⊔ G.map K.starProjection.toLinearMap
  have hGM : G ≤ M := le_sup_left
  have hmapM : G.map K.starProjection.toLinearMap ≤ M := le_sup_right
  have hDM : D ≤ M := le_sup_right.trans hGM
  have hP : ∀ x ∈ M, K.starProjection x ∈ M := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨c, hc, rfl⟩ := Submodule.mem_map.mp hb
    rw [map_add]
    apply M.add_mem
    · exact hmapM (Submodule.mem_map.mpr ⟨a, ha, rfl⟩)
    · change K.starProjection (K.starProjection c) ∈ M
      rw [K.starProjection_eq_self_iff.mpr (K.starProjection_apply_mem c)]
      exact hmapM (Submodule.mem_map.mpr ⟨c, hc, rfl⟩)
  refine ⟨M, inferInstance, le_sup_left.trans hGM, ?_,
    U.isReducing_of_displacement_range_le M hDM, hDM, ?_⟩
  · exact (K.starProjection_isSymmetric.isReducing_iff_mem_invtSubmodule M).mpr hP
  · intro x hx
    exact U.apply_eq_self_of_mem_orthogonal_displacement M hDM hx

end TauCeti

/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.InvariantSubspace
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import TauCeti.Analysis.Normed.Lp.ProdLp

/-!
# Restricting an isometric equivalence to a finite invariant subspace

Finite-dimensional invariance gives a surjective restriction and reduction.
The ambient space need not be complete or finite-dimensional. The actual
inverse restriction is recorded as well as the forward action.
-/

public section

noncomputable section

namespace LinearIsometryEquiv

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A finite invariant subspace of an isometric equivalence is reducing,
and carries the actual restricted equivalence and its inverse. -/
theorem exists_restriction_of_finite_invariant
    (U : E ≃ₗᵢ[𝕜] E) (N : Submodule 𝕜 E) [FiniteDimensional 𝕜 N]
    (hinv : ∀ x ∈ N, U x ∈ N) :
    ∃ V : N ≃ₗᵢ[𝕜] N,
      (∀ x : N, (V x : E) = U x) ∧
      (∀ x : N, (V.symm x : E) = U.symm x) ∧ N.IsReducing U.toLinearMap := by
  let v : N →ₗᵢ[𝕜] N :=
    { U.toLinearMap.restrict hinv with norm_map' := fun x => U.norm_map x }
  let V := v.toLinearIsometryEquiv rfl
  have hV (x : N) : (V x : E) = U x := rfl
  have hVs (x : N) : (V.symm x : E) = U.symm x := by
    apply U.injective
    calc
      U (V.symm x : E) = (V (V.symm x) : E) := (hV _).symm
      _ = (x : E) := by rw [V.apply_symm_apply]
      _ = U (U.symm (x : E)) := (U.apply_symm_apply x).symm
  have horth : ∀ x ∈ Nᗮ, U x ∈ Nᗮ := by
    intro x hx y hy
    let y' : N := V.symm ⟨y, hy⟩
    have hpre : U (y' : E) = y := by
      rw [← hV, show V y' = ⟨y, hy⟩ from V.apply_symm_apply ⟨y, hy⟩]
    rw [← hpre, U.inner_map_map]
    exact hx y' y'.property
  refine ⟨V, hV, hVs, (N.isReducing_iff U.toLinearMap).mpr ?_⟩
  exact ⟨(Module.End.mem_invtSubmodule_iff_forall_mem_of_mem U.toLinearMap).mpr hinv,
    (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem U.toLinearMap).mpr horth⟩

end LinearIsometryEquiv

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Two unitary actions on orthogonal complementary subspaces assemble
to an ambient unitary. No finite-dimensional hypothesis is needed. -/
theorem exists_unitary_orthogonal_sum
    (N : Submodule 𝕜 E) [N.HasOrthogonalProjection]
    (V : N ≃ₗᵢ[𝕜] N) (W : Nᗮ ≃ₗᵢ[𝕜] Nᗮ) :
    ∃ U : E ≃ₗᵢ[𝕜] E,
      (∀ x : N, U x = (V x : E)) ∧ (∀ x : Nᗮ, U x = (W x : E)) := by
  let d := N.orthogonalDecomposition
  let U := (d.trans (LinearIsometryEquiv.withLpProdCongr 2 V W)).trans d.symm
  have hU (x : WithLp 2 (N × Nᗮ)) :
      U (d.symm x) = (V x.fst : E) + (W x.snd : E) := by
    change d.symm ((LinearIsometryEquiv.withLpProdCongr 2 V W) (d (d.symm x))) = _
    rw [d.apply_symm_apply, Submodule.orthogonalDecomposition_symm_apply]
    rfl
  refine ⟨U, ?_, ?_⟩
  · intro x
    have h := hU (WithLp.toLp 2 (x, 0))
    simpa [d, Submodule.orthogonalDecomposition_symm_apply] using h
  · intro x
    have h := hU (WithLp.toLp 2 (0, x))
    simpa [d, Submodule.orthogonalDecomposition_symm_apply] using h

end Submodule

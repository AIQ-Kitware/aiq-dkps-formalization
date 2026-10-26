/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import TauCeti.Analysis.InnerProductSpace.InvariantSubspace
public import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-!
# Actual unitary restriction to an orthogonally complemented reducing subspace

Reduction, unlike mere invariance in infinite dimension, makes the
restriction surjective. The preimage of `y` is obtained by projecting
`U.symm y` onto the subspace, using commutation of its projection with
`U`. This includes infinite-dimensional and nonseparable subspaces.
-/

public section

noncomputable section

namespace LinearIsometryEquiv

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A reducing subspace with an orthogonal projection carries the
actual unitary restriction and its actual inverse. No finite dimension
or ambient completeness is needed. -/
theorem exists_restriction_of_reducing
    (U : E ≃ₗᵢ[𝕜] E) (M : Submodule 𝕜 E) [M.HasOrthogonalProjection]
    (hM : M.IsReducing U.toLinearMap) :
    ∃ V : M ≃ₗᵢ[𝕜] M,
      (∀ x : M, (V x : E) = U x) ∧ (∀ x : M, (V.symm x : E) = U.symm x) := by
  let v : M →ₗᵢ[𝕜] M :=
    { U.toLinearMap.restrict hM.mem_invtSubmodule with norm_map' := fun x => U.norm_map x }
  have hcomm : Commute M.starProjection (U : E →L[𝕜] E) :=
    Submodule.isReducing_coe_iff_commute_starProjection.mp hM
  have hsurj : Function.Surjective v := by
    intro y
    refine ⟨M.orthogonalProjectionOnto (U.symm (y : E)), ?_⟩
    apply Subtype.ext
    change U (M.starProjection (U.symm (y : E))) = (y : E)
    calc
      _ = M.starProjection (U (U.symm (y : E))) :=
        (congrArg (fun T : E →L[𝕜] E => T (U.symm (y : E))) hcomm.eq).symm
      _ = (y : E) := by
        rw [U.apply_symm_apply, M.starProjection_eq_self_iff.mpr y.property]
  let V := LinearIsometryEquiv.ofSurjective v hsurj
  have hV (x : M) : (V x : E) = U x := rfl
  refine ⟨V, hV, ?_⟩
  intro x
  apply U.injective
  calc
    U (V.symm x : E) = (V (V.symm x) : E) := (hV _).symm
    _ = (x : E) := congrArg Subtype.val (V.apply_symm_apply x)
    _ = U (U.symm (x : E)) := (U.apply_symm_apply _).symm

end LinearIsometryEquiv

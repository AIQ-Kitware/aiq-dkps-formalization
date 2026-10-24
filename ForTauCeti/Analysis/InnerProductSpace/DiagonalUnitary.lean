/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Unitary diagonal multipliers in an orthonormal basis

Multiplying every vector of a finite orthonormal basis by a unit-norm
scalar gives a linear isometry equivalence of the whole space.
-/

public section

namespace OrthonormalBasis

open scoped InnerProductSpace

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] [Fintype ι]

/-- Any prescribed unit-norm diagonal in an orthonormal basis is realized
by a surjective linear isometry. -/
theorem exists_linearIsometryEquiv_apply_eq_smul
    (e : OrthonormalBasis ι 𝕜 E) (lam : ι → 𝕜) (hlam : ∀ j, ‖lam j‖ = 1) :
    ∃ V : E ≃ₗᵢ[𝕜] E, ∀ j, V (e j) = lam j • e j := by
  classical
  let f := e.toBasis.constr 𝕜 (fun j => lam j • e j)
  have hf (j) : f (e j) = lam j • e j := e.toBasis.constr_basis 𝕜 _ j
  have horth : Orthonormal 𝕜 (f ∘ e.toBasis) := by
    rw [orthonormal_iff_ite]
    intro j k
    change inner 𝕜 (f (e j)) (f (e k)) = _
    rw [hf, hf, inner_smul_left, inner_smul_right, e.inner_eq_ite]
    by_cases hjk : j = k
    · subst k
      rw [ite_eq_left rfl, mul_one, RCLike.conj_mul, hlam]
      norm_num
    · rw [ite_eq_right hjk, mul_zero, mul_zero]
  let L := f.isometryOfOrthonormal e.orthonormal horth
  exact ⟨L.toLinearIsometryEquiv rfl, hf⟩

end OrthonormalBasis

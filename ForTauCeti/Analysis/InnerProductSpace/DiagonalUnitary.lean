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

/-- Unit-norm multipliers common to each involution-paired basis pair
extend to an ambient unitary commuting with the involution and fixing
the remaining eigenvectors. Empty paired or remaining spaces are allowed. -/
theorem exists_paired_diagonal_commuting_involution
    {n m : ℕ} (e : OrthonormalBasis ((Fin 2 × Fin n) ⊕ Fin m) 𝕜 E)
    (lam : Fin n → 𝕜) (hlam : ∀ i, ‖lam i‖ = 1)
    (J : E ≃ₗᵢ[𝕜] E) (hJ : Function.Involutive J)
    (hJ0 : ∀ i, J (e (.inl (0, i))) = e (.inl (1, i)))
    (eps : Fin m → 𝕜) (hJf : ∀ j, J (e (.inr j)) = eps j • e (.inr j)) :
    ∃ Z : E ≃ₗᵢ[𝕜] E,
      (∀ r i, Z (e (.inl (r, i))) = lam i • e (.inl (r, i))) ∧
      (∀ j, Z (e (.inr j)) = e (.inr j)) ∧ (∀ x, Z (J x) = J (Z x)) := by
  classical
  let nu : ((Fin 2 × Fin n) ⊕ Fin m) → 𝕜 := Sum.elim (fun j => lam j.2) (fun _ => 1)
  obtain ⟨Z, hZ⟩ := e.exists_linearIsometryEquiv_apply_eq_smul nu (by
    rintro (⟨r, i⟩ | j)
    · exact hlam i
    · exact norm_one)
  have hZp (r i) : Z (e (.inl (r, i))) = lam i • e (.inl (r, i)) := hZ _
  have hZf (j) : Z (e (.inr j)) = e (.inr j) := by
    simpa only [nu, Sum.elim_inr, one_smul] using hZ (.inr j)
  have hJ1 (i) : J (e (.inl (1, i))) = e (.inl (0, i)) := by rw [← hJ0, hJ]
  refine ⟨Z, hZp, hZf, ?_⟩
  have hmaps : Z.toLinearMap.comp J.toLinearMap = J.toLinearMap.comp Z.toLinearMap := by
    apply e.toBasis.ext
    intro j
    change Z (J (e j)) = J (Z (e j))
    rcases j with ⟨r, i⟩ | j
    · by_cases hr : r = 0
      · subst r
        rw [hJ0, hZp, hZp, map_smul, hJ0]
      · have hr1 : r = 1 := by omega
        subst r
        rw [hJ1, hZp, hZp, map_smul, hJ1]
    · rw [hJf, map_smul, hZf, hJf]
  exact fun x => DFunLike.congr_fun hmaps x

end OrthonormalBasis

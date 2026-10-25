/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Kernel invariance from commutation with a symmetric square

The kernel of a symmetric operator equals the kernel of its square.
Consequently any linear map commuting with that square preserves the kernel.
No completeness or dimension assumption is required.

A finite orthonormal basis also detects when an eigenvector of one
symmetric map lies in another map's kernel: each basis vector is either
annihilated or has a different eigenvalue for the symmetric map.
This is the classical orthogonality argument, proved directly here.
-/

public section

namespace LinearMap.IsSymmetric

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Commutation with the square of a symmetric operator preserves its
kernel, even if the two operators themselves do not commute. -/
theorem mapsTo_ker_of_commute_square {G P : Module.End 𝕜 E} (hG : G.IsSymmetric)
    (hP : Commute P (G * G)) : Set.MapsTo P G.ker G.ker := by
  intro x hx
  change G x = 0 at hx
  change G (P x) = 0
  have h := congrArg (fun T : Module.End 𝕜 E => T x) hP.eq
  change P (G (G x)) = G (G (P x)) at h
  rw [hx, map_zero, map_zero] at h
  have hi := hG (P x) (G (P x))
  rw [← h, inner_zero_right] at hi
  exact inner_self_eq_zero.mp hi

/-- A boundary eigenspace lies in a map's kernel if every vector of a
complete orthonormal basis is either annihilated or belongs to a different
eigenspace of the symmetric map. Neither map needs to commute with the
other, and the annihilating map need not be symmetric. -/
theorem apply_eq_zero_of_eigenvector_of_basis
    {S G : Module.End 𝕜 E} (hS : S.IsSymmetric)
    {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι 𝕜 E)
    (mu : ℝ) (x : E) (hx : S x = (mu : 𝕜) • x)
    (he : ∀ i, G (e i) = 0 ∨
      ∃ nu : ℝ, nu ≠ mu ∧ S (e i) = (nu : 𝕜) • e i) : G x = 0 := by
  classical
  rw [← e.sum_repr' x, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [map_smul]
  rcases he i with hzero | ⟨nu, hne, hnu⟩
  · rw [hzero, smul_zero]
  · have hi := hS (e i) x
    rw [hnu, hx, inner_smul_left, inner_smul_right, RCLike.conj_ofReal] at hi
    have hprod : ((nu : 𝕜) - (mu : 𝕜)) * inner 𝕜 (e i) x = 0 := by
      linear_combination hi
    have hcast : (nu : 𝕜) - (mu : 𝕜) ≠ 0 :=
      sub_ne_zero.mpr (fun h => hne (RCLike.ofReal_injective h))
    rw [(mul_eq_zero.mp hprod).resolve_left hcast, zero_smul]

end LinearMap.IsSymmetric

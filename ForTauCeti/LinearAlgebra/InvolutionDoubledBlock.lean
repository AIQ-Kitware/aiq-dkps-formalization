/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Exact reflection multiplicities on a doubled block

If an involution exchanges two disjoint subspaces, each of its signed
eigenspaces on their sum has the original subspace's dimension. The map
is the explicit symmetrization `x -> x + e R x`, for `e^2=1`.
No inner product, diagonalization or choice of eigenbasis is needed.
This is classical linear algebra used to certify the source rank of
each small real spectral transport block.
-/

public section

namespace TauCeti

variable {𝕜 E : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- A vector and its image in a disjoint subspace cannot cancel, whatever
the scalar coefficient. -/
theorem injective_symmetrization_of_disjoint
    (R : E ≃ₗ[𝕜] E) (S : Submodule 𝕜 E)
    (hS : Disjoint S (S.map R.toLinearMap)) (e : 𝕜) :
    Function.Injective (S.subtype + e • (R.toLinearMap ∘ₗ S.subtype)) := by
  let F := S.subtype + e • (R.toLinearMap ∘ₗ S.subtype)
  have hzero (x : S) (hx : F x = 0) : x = 0 := by
    have heq : (x : E) = -e • R (x : E) := by
      change (x : E) + e • R (x : E) = 0 at hx
      simpa only [neg_smul] using (eq_neg_of_add_eq_zero_left hx)
    have hmem : (x : E) ∈ S ⊓ S.map R.toLinearMap :=
      ⟨x.property, heq ▸ (S.map R.toLinearMap).smul_mem (-e)
        (Submodule.mem_map_of_mem x.property)⟩
    have hx0 : (x : E) = 0 := by simpa only [hS.eq_bot, Submodule.mem_bot] using hmem
    exact Subtype.ext hx0
  intro x y hxy
  exact sub_eq_zero.mp (hzero (x-y) (by rw [map_sub, hxy, sub_self]))

/-- Symmetrization parametrizes the entire signed eigenspace on a doubled
block. Disjointness makes the two component coordinates unique. -/
theorem range_symmetrization_eq_doubled_eigenspace
    (R : E ≃ₗ[𝕜] E) (hR : Function.Involutive R) (S : Submodule 𝕜 E)
    (hS : Disjoint S (S.map R.toLinearMap)) (e : 𝕜) (he : e ^ 2 = 1) :
    LinearMap.range (S.subtype + e • (R.toLinearMap ∘ₗ S.subtype)) =
      (S ⊔ S.map R.toLinearMap) ⊓ Module.End.eigenspace R.toLinearMap e := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    constructor
    · change (x : E) + e • R (x : E) ∈ S ⊔ S.map R.toLinearMap
      exact (S ⊔ S.map R.toLinearMap).add_mem
        ((show S ≤ S ⊔ S.map R.toLinearMap from le_sup_left) x.property)
        ((S ⊔ S.map R.toLinearMap).smul_mem e
          ((show S.map R.toLinearMap ≤ S ⊔ S.map R.toLinearMap from le_sup_right)
            (Submodule.mem_map_of_mem x.property)))
    · simp only [SetLike.mem_coe, Module.End.mem_eigenspace_iff]
      change R ((x : E) + e • R (x : E)) = e • ((x : E) + e • R (x : E))
      rw [map_add, map_smul, hR, smul_add, smul_smul, ← pow_two, he, one_smul]
      exact add_comm _ _
  · rintro ⟨hy, heigen⟩
    obtain ⟨a, ha, z, hz, rfl⟩ := Submodule.mem_sup.mp hy
    obtain ⟨b, hb, rfl⟩ := hz
    simp only [SetLike.mem_coe, Module.End.mem_eigenspace_iff] at heigen
    change R (a + R b) = e • (a + R b) at heigen
    rw [map_add, hR, smul_add] at heigen
    have hdiff : b - e • a ∈ S.map R.toLinearMap := by
      have heq : b - e • a = e • R b - R a := by
        calc
          _ = (R a+b) - (R a+e • a) := by abel
          _ = (e • a+e • R b) - (R a+e • a) := by rw [heigen]
          _ = _ := by abel
      rw [heq]
      exact (S.map R.toLinearMap).sub_mem
        ((S.map R.toLinearMap).smul_mem e (Submodule.mem_map_of_mem hb))
        (Submodule.mem_map_of_mem ha)
    have hzero : b - e • a = 0 := by
      have hm : b - e • a ∈ S ⊓ S.map R.toLinearMap :=
        ⟨S.sub_mem hb (S.smul_mem e ha), hdiff⟩
      simpa only [hS.eq_bot, Submodule.mem_bot] using hm
    refine ⟨⟨a, ha⟩, ?_⟩
    change a + e • R a = a + R b
    rw [sub_eq_zero.mp hzero, map_smul]

/-- Each signed eigenspace on a doubled block has exactly the original
block's dimension. In characteristic different from two these are the
two equal halves of the doubled block. -/
theorem finrank_doubled_inf_eigenspace [FiniteDimensional 𝕜 E]
    (R : E ≃ₗ[𝕜] E) (hR : Function.Involutive R) (S : Submodule 𝕜 E)
    (hS : Disjoint S (S.map R.toLinearMap)) (e : 𝕜) (he : e ^ 2 = 1) :
    Module.finrank 𝕜 ↥((S ⊔ S.map R.toLinearMap) ⊓
      Module.End.eigenspace R.toLinearMap e : Submodule 𝕜 E) = Module.finrank 𝕜 S := by
  rw [← range_symmetrization_eq_doubled_eigenspace R hR S hS e he]
  exact LinearMap.finrank_range_of_inj (injective_symmetrization_of_disjoint R S hS e)

end TauCeti

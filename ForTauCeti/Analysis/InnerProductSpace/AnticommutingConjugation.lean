/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# A conjugation on a real gradient eigenspace

If a complex-linear isometric involution and an isometric conjugation
commute with each other and both reverse an operator, their composite
is a conjugation preserving every real eigenspace. This is the fixed-real
coordinate system on a positive stationary-gradient level.
-/

public section

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Two commuting symmetries that reverse the same operator induce an
isometric conjugation on each real eigenspace. The construction consumes
the accepted submodule-map isometry. -/
theorem exists_eigenspace_conjugation_of_anticommuting_symmetries
    (G : E →ₗ[ℂ] E)
    (R : E ≃ₗᵢ[ℂ] E) (hR : Function.Involutive R)
    (C : E ≃ₗᵢ⋆[ℂ] E) (hC : Function.Involutive C)
    (hRC : ∀ x, R (C x) = C (R x))
    (hGR : ∀ x, G (R x) = -R (G x))
    (hGC : ∀ x, G (C x) = -C (G x)) (g : ℝ) :
    let L := Module.End.eigenspace G (g : ℂ)
    ∃ J : L ≃ₗᵢ⋆[ℂ] L, Function.Involutive J ∧
      ∀ x : L, (J x : E) = R (C x) := by
  let L := Module.End.eigenspace G (g : ℂ)
  let S : E ≃ₗᵢ⋆[ℂ] E := C.trans R
  have hS (x : E) : S (S x) = x := by
    change R (C (R (C x))) = x
    rw [← hRC, hR, hC]
  have hSG (x : E) : G (S x) = S (G x) := by
    change G (R (C x)) = R (C (G x))
    rw [hGR, hGC, map_neg, neg_neg]
  have hinv : ∀ x ∈ L, S x ∈ L := by
    intro x hx
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    rw [hSG, hx, map_smulₛₗ, Complex.conj_ofReal]
  have hmap : L.map S.toLinearMap = L := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hinv y hy
    · intro hx
      exact ⟨S x, hinv x hx, hS x⟩
  let J : L ≃ₗᵢ⋆[ℂ] L := (LinearIsometryEquiv.submoduleMap L S).trans
    (LinearIsometryEquiv.ofEq _ _ hmap)
  have hJ (x : L) : (J x : E) = S x := rfl
  refine ⟨J, ?_, fun _ => rfl⟩
  intro x
  apply Subtype.ext
  rw [hJ, hJ, hS]

end TauCeti

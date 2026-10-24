/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Extend an orthogonal projection to a reflected pair

If an involution sends a subspace to an orthogonal subspace, every orthogonal
projection on that subspace extends to a projection on their paired sum,
using its reflected copy on the other half and zero on the remainder.
A unitary scalar on each half commutes with this extension.
-/

public section

noncomputable section

namespace TauCeti

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [CompleteSpace E]

/-- An arbitrary orthogonal projection on one of two orthogonal reflected
spaces extends to an ambient orthogonal projection commuting with the
reflection and with any unitary scalar on the two spaces. -/
theorem exists_paired_projection_extension
    (N : Submodule 𝕜 E) (J R : E ≃ₗᵢ[𝕜] E) (hJ : Function.Involutive J)
    (horth : ∀ x y : N, ⟪(x : E), J y⟫_𝕜 = 0)
    (mu nu : 𝕜) (hR : ∀ x : N, R x = mu • (x : E))
    (hRJ : ∀ x : N, R (J x) = nu • J x)
    (Q : N →L[𝕜] N) (hQ : IsStarProjection Q) :
    ∃ P : E →L[𝕜] E, IsStarProjection P ∧ Commute P (R : E →L[𝕜] E) ∧
      (∀ x, P (J x) = J (P x)) ∧ ∀ x : N, P x = (Q x : E) := by
  let M₀ := Q.range
  let M := M₀.map N.subtype
  let S := M ⊔ M.map J.toLinearMap
  have hMN : M ≤ N := by
    rintro x ⟨y, _, rfl⟩
    exact y.property
  have hJS : ∀ x ∈ S, J x ∈ S := by
    intro x hx
    rcases Submodule.mem_sup.mp hx with ⟨u, hu, v, ⟨z, hz, rfl⟩, rfl⟩
    change J (u + J z) ∈ S
    rw [map_add, hJ]
    rw [add_comm]
    exact Submodule.add_mem_sup (show z ∈ M from hz) (Submodule.mem_map_of_mem hu)
  have hRS : ∀ x ∈ S, R x ∈ S := by
    intro x hx
    rcases Submodule.mem_sup.mp hx with ⟨u, hu, v, ⟨z, hz, rfl⟩, rfl⟩
    change R (u + J z) ∈ S
    rw [map_add, show R u = mu • u from hR ⟨u, hMN hu⟩,
      show R (J z) = nu • J z from hRJ ⟨z, hMN hz⟩]
    exact Submodule.add_mem_sup (M.smul_mem mu hu)
      ((M.map J.toLinearMap).smul_mem nu (Submodule.mem_map_of_mem hz))
  have hJmap : S.map J.toLinearMap = S :=
    Submodule.eq_of_le_of_finrank_eq (by rintro y ⟨x, hx, rfl⟩; exact hJS x hx)
      (J.toLinearEquiv.finrank_map_eq S)
  have hRmap : S.map R.toLinearMap = S :=
    Submodule.eq_of_le_of_finrank_eq (by rintro y ⟨x, hx, rfl⟩; exact hRS x hx)
      (R.toLinearEquiv.finrank_map_eq S)
  have hcomm (U : E ≃ₗᵢ[𝕜] E) (hU : S.map U.toLinearMap = S) (x : E) :
      S.starProjection (U x) = U (S.starProjection x) := by
    have h := U.toLinearIsometry.map_starProjection S x
    change U (S.starProjection x) = (S.map U.toLinearMap).starProjection (U x) at h
    simpa only [hU] using h.symm
  refine ⟨S.starProjection, isStarProjection_starProjection, ?_, hcomm J hJmap, ?_⟩
  · ext x
    exact hcomm R hRmap x
  · intro x
    apply S.eq_starProjection_of_mem_of_inner_eq_zero
    · apply Submodule.mem_sup_left
      exact Submodule.mem_map_of_mem (show Q x ∈ M₀ from ⟨x, rfl⟩)
    · intro w hw
      rcases Submodule.mem_sup.mp hw with ⟨u, ⟨u₀, hu₀, rfl⟩, v,
        ⟨z, ⟨z₀, hz₀, rfl⟩, rfl⟩, rfl⟩
      rw [inner_add_right]
      have hM : ⟪(x : E) - (Q x : E), (u₀ : E)⟫_𝕜 = 0 := by
        change ⟪x - Q x, u₀⟫_𝕜 = 0
        obtain ⟨_, hQeq⟩ := isStarProjection_iff_eq_starProjection_range.mp hQ
        rw [show Q x = M₀.starProjection x from congrArg (fun A : N →L[𝕜] N => A x) hQeq]
        exact M₀.starProjection_inner_eq_zero x u₀ hu₀
      have hJM : ⟪(x : E) - (Q x : E), J (z₀ : E)⟫_𝕜 = 0 := horth (x - Q x) z₀
      change ⟪(x : E) - (Q x : E), (u₀ : E)⟫_𝕜 +
        ⟪(x : E) - (Q x : E), J (z₀ : E)⟫_𝕜 = 0
      rw [hM, hJM, add_zero]

end TauCeti

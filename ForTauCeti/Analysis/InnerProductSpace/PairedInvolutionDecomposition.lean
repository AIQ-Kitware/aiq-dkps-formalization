/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Coordinates for two orthogonal spaces exchanged by an involution

If an isometric involution sends a subspace to an orthogonal subspace,
their sum has coordinates `K ⊕ K` in which the involution swaps the two
components. The remaining orthogonal complement is preserved.
-/

public section

noncomputable section

namespace TauCeti

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Add a vector of `K` to the image under `J` of another vector of `K`.
Orthogonality makes this an isometry from the Hilbert product. -/
def pairedInvolutionEmbedding (K : Submodule 𝕜 E) (J : E ≃ₗᵢ[𝕜] E)
    (horth : ∀ x y : K, ⟪(x : E), J y⟫_𝕜 = 0) : WithLp 2 (K × K) →ₗᵢ[𝕜] E where
  toLinearMap := (K.subtype ∘ₗ WithLp.fstₗ 2 𝕜 K K) +
    J.toLinearMap ∘ₗ K.subtype ∘ₗ WithLp.sndₗ 2 𝕜 K K
  norm_map' x := by
    change ‖(x.fst : E) + J x.snd‖ = ‖x‖
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), WithLp.prod_norm_sq_eq_of_L2]
    simpa only [pow_two, J.norm_map, Submodule.norm_coe] using
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ (horth x.fst x.snd)

/-- The paired embedding acts by the sum of the two orthogonal components. -/
@[simp]
theorem pairedInvolutionEmbedding_apply (K : Submodule 𝕜 E) (J : E ≃ₗᵢ[𝕜] E)
    (horth : ∀ x y : K, ⟪(x : E), J y⟫_𝕜 = 0) (x : WithLp 2 (K × K)) :
    pairedInvolutionEmbedding K J horth x = (x.fst : E) + J x.snd := by rfl

/-- The paired embedding has range equal to the sum of the original space
and its image under the isometry. -/
theorem pairedInvolutionEmbedding_range (K : Submodule 𝕜 E) (J : E ≃ₗᵢ[𝕜] E)
    (horth : ∀ x y : K, ⟪(x : E), J y⟫_𝕜 = 0) :
    (pairedInvolutionEmbedding K J horth).toLinearMap.range = K ⊔ K.map J.toLinearMap := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    change pairedInvolutionEmbedding K J horth x ∈ K ⊔ K.map J.toLinearMap
    rw [pairedInvolutionEmbedding_apply]
    exact Submodule.add_mem_sup x.fst.property (Submodule.mem_map_of_mem x.snd.property)
  · intro y hy
    rcases Submodule.mem_sup.mp hy with ⟨x, hx, z, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨WithLp.toLp 2 (⟨x, hx⟩, ⟨w, hw⟩), rfl⟩

/-- The involution exchanges the two paired coordinates. -/
theorem pairedInvolutionEmbedding_swap (K : Submodule 𝕜 E) (J : E ≃ₗᵢ[𝕜] E)
    (horth : ∀ x y : K, ⟪(x : E), J y⟫_𝕜 = 0) (hJ : Function.Involutive J)
    (x : WithLp 2 (K × K)) :
    J (pairedInvolutionEmbedding K J horth x) =
      pairedInvolutionEmbedding K J horth (WithLp.toLp 2 (x.snd, x.fst)) := by
  rw [pairedInvolutionEmbedding_apply, pairedInvolutionEmbedding_apply]
  change J ((x.fst : E) + J x.snd) = (x.snd : E) + J x.fst
  rw [map_add, hJ]
  exact add_comm _ _

/-- Complete paired coordinates by the orthogonal complement of their range. -/
def pairedInvolutionDecomposition [FiniteDimensional 𝕜 E]
    (K : Submodule 𝕜 E) (J : E ≃ₗᵢ[𝕜] E)
    (horth : ∀ x y : K, ⟪(x : E), J y⟫_𝕜 = 0) :
    let S := (pairedInvolutionEmbedding K J horth).toLinearMap.range
    WithLp 2 (WithLp 2 (K × K) × Sᗮ) ≃ₗᵢ[𝕜] E :=
  (LinearIsometryEquiv.withLpProdCongr 2
    (pairedInvolutionEmbedding K J horth).equivRange
    (LinearIsometryEquiv.refl 𝕜 _)).trans
      (pairedInvolutionEmbedding K J horth).toLinearMap.range.orthogonalDecomposition.symm

/-- In the completed coordinates, the ambient vector is the sum of its
paired components and its orthogonal remainder. -/
@[simp]
theorem pairedInvolutionDecomposition_apply [FiniteDimensional 𝕜 E]
    (K : Submodule 𝕜 E) (J : E ≃ₗᵢ[𝕜] E)
    (horth : ∀ x y : K, ⟪(x : E), J y⟫_𝕜 = 0)
    (x : WithLp 2 (WithLp 2 (K × K) ×
      (pairedInvolutionEmbedding K J horth).toLinearMap.rangeᗮ)) :
    pairedInvolutionDecomposition K J horth x =
      (x.fst.fst : E) + J x.fst.snd + (x.snd : E) := by
  simp [pairedInvolutionDecomposition]

/-- The orthogonal remainder of the paired space is invariant under the
original involution. -/
theorem pairedInvolutionEmbedding_orthogonal_invariant
    (K : Submodule 𝕜 E) (J : E ≃ₗᵢ[𝕜] E)
    (horth : ∀ x y : K, ⟪(x : E), J y⟫_𝕜 = 0) (hJ : Function.Involutive J) :
    ∀ z ∈ (pairedInvolutionEmbedding K J horth).toLinearMap.rangeᗮ,
      J z ∈ (pairedInvolutionEmbedding K J horth).toLinearMap.rangeᗮ := by
  intro z hz
  rw [Submodule.mem_orthogonal] at hz ⊢
  rintro y ⟨x, rfl⟩
  have hJy : J (pairedInvolutionEmbedding K J horth x) ∈
      (pairedInvolutionEmbedding K J horth).toLinearMap.range := by
    exact ⟨WithLp.toLp 2 (x.snd, x.fst),
      (pairedInvolutionEmbedding_swap K J horth hJ x).symm⟩
  have hinner := J.inner_map_map (J (pairedInvolutionEmbedding K J horth x)) z
  rw [hJ] at hinner
  exact hinner.trans (hz _ hJy)

/-- In the completed coordinates, the original involution is swapping
on the paired component and an isometric involution on the remainder. -/
theorem pairedInvolutionDecomposition_involution [FiniteDimensional 𝕜 E]
    (K : Submodule 𝕜 E) (J : E ≃ₗᵢ[𝕜] E)
    (horth : ∀ x y : K, ⟪(x : E), J y⟫_𝕜 = 0) (hJ : Function.Involutive J) :
    let S := (pairedInvolutionEmbedding K J horth).toLinearMap.range
    ∃ J₀ : Sᗮ ≃ₗᵢ[𝕜] Sᗮ,
      (∀ z, (J₀ z : E) = J z) ∧ Function.Involutive J₀ ∧
      ∀ x, J (pairedInvolutionDecomposition K J horth x) =
        pairedInvolutionDecomposition K J horth
          (WithLp.toLp 2 (WithLp.toLp 2 (x.fst.snd, x.fst.fst), J₀ x.snd)) := by
  let S := (pairedInvolutionEmbedding K J horth).toLinearMap.range
  have hinv := pairedInvolutionEmbedding_orthogonal_invariant K J horth hJ
  let j : Sᗮ →ₗᵢ[𝕜] Sᗮ :=
    { J.toLinearMap.restrict hinv with norm_map' := fun z => J.norm_map z }
  let J₀ := j.toLinearIsometryEquiv rfl
  have hJ₀ (z : Sᗮ) : (J₀ z : E) = J z := rfl
  refine ⟨J₀, hJ₀, ?_, ?_⟩
  · intro z
    apply Subtype.ext
    rw [hJ₀, hJ₀, hJ]
  · intro x
    rw [pairedInvolutionDecomposition_apply, pairedInvolutionDecomposition_apply]
    change J ((x.fst.fst : E) + J x.fst.snd + (x.snd : E)) =
      (x.fst.snd : E) + J x.fst.fst + (J₀ x.snd : E)
    rw [map_add, map_add, hJ, hJ₀]
    abel

/-- An ambient unitary preserving the two paired components acts blockwise
in the completed coordinates; its restriction to the remainder is unitary. -/
theorem pairedInvolutionDecomposition_operator [FiniteDimensional 𝕜 E]
    (K : Submodule 𝕜 E) (J : E ≃ₗᵢ[𝕜] E)
    (horth : ∀ x y : K, ⟪(x : E), J y⟫_𝕜 = 0)
    (U : E ≃ₗᵢ[𝕜] E) (V W : K ≃ₗᵢ[𝕜] K)
    (hV : ∀ x : K, U x = (V x : E))
    (hW : ∀ x : K, U (J x) = J (W x)) :
    let S := (pairedInvolutionEmbedding K J horth).toLinearMap.range
    ∃ Z : Sᗮ ≃ₗᵢ[𝕜] Sᗮ, (∀ z, (Z z : E) = U z) ∧
      ∀ x, U (pairedInvolutionDecomposition K J horth x) =
        pairedInvolutionDecomposition K J horth
          (WithLp.toLp 2 (WithLp.toLp 2 (V x.fst.fst, W x.fst.snd), Z x.snd)) := by
  let S := (pairedInvolutionEmbedding K J horth).toLinearMap.range
  have hinv : ∀ y ∈ S, U y ∈ S := by
    rintro y ⟨x, rfl⟩
    refine ⟨WithLp.toLp 2 (V x.fst, W x.snd), ?_⟩
    change (V x.fst : E) + J (W x.snd) = U ((x.fst : E) + J x.snd)
    rw [map_add, hV, hW]
  have hmap : S.map U.toLinearMap = S :=
    Submodule.eq_of_le_of_finrank_eq (by rintro y ⟨x, hx, rfl⟩; exact hinv x hx)
      (U.toLinearEquiv.finrank_map_eq S)
  have horthinv : ∀ z ∈ Sᗮ, U z ∈ Sᗮ := by
    intro z hz
    have hm : U z ∈ Sᗮ.map U.toLinearMap := ⟨z, hz, rfl⟩
    rwa [Submodule.map_orthogonal_equiv, hmap] at hm
  let v : Sᗮ →ₗᵢ[𝕜] Sᗮ :=
    { U.toLinearMap.restrict horthinv with norm_map' := fun z => U.norm_map z }
  let Z := v.toLinearIsometryEquiv rfl
  have hZ (z : Sᗮ) : (Z z : E) = U z := rfl
  refine ⟨Z, hZ, ?_⟩
  intro x
  rw [pairedInvolutionDecomposition_apply, pairedInvolutionDecomposition_apply]
  change U ((x.fst.fst : E) + J x.fst.snd + (x.snd : E)) =
    (V x.fst.fst : E) + J (W x.fst.snd) + (Z x.snd : E)
  rw [map_add, map_add, hV, hW, hZ]

end TauCeti

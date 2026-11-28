/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.BlockSum
public import ForTauCeti.Analysis.InnerProductSpace.Singular.Subspace
import ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.BlockSchatten

/-!
# Full trace norm of an orthogonal block sum

The trace norm (the Ky Fan sum over the entire source dimension) is
additive across orthogonal direct sums.  This is stronger than the triangle
inequality for Ky Fan sums and is the bookkeeping needed to assemble
complex principal-plane trace minimizers with no loss in the constant.

The full trace norm uses the sum of the singular-value lists of the blocks.
The underlying multiplicity formula is TauCeti's block-spectrum theorem.
-/

public section

namespace TauCeti

open scoped InnerProductSpace BigOperators
open Module (finrank)
open UnitarilyInvariantSeminorm

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The trace norm of an orthogonal direct sum equals the sum of the trace
norms of its blocks.  This also covers zero-dimensional summands. -/
theorem kyFanSum_orthogonalBlockSum_full
    {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [FiniteDimensional 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] [FiniteDimensional 𝕜 E₂]
    (A : E₁ →ₗ[𝕜] E₁) (B : E₂ →ₗ[𝕜] E₂) :
    ((A.prodMap B).withLpMap 2).kyFanSum (finrank 𝕜 (WithLp 2 (E₁ × E₂))) =
      A.kyFanSum (finrank 𝕜 E₁) + B.kyFanSum (finrank 𝕜 E₂) := by
  simp only [LinearMap.kyFanSum_def, ← Fin.sum_univ_eq_sum_range]
  exact sum_singularValues_prodMap_withLpMap A B id

/-- An orthogonal product of two unitary transports carries a block-sum
subspace onto the block-sum target subspace. -/
theorem map_orthogonalBlockSumSubmodule
    {E₁ E₂ F₁ F₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
    [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁]
    [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂]
    (U₁ : Submodule 𝕜 E₁) (U₂ : Submodule 𝕜 E₂)
    (V₁ : Submodule 𝕜 F₁) (V₂ : Submodule 𝕜 F₂)
    (W₁ : E₁ ≃ₗᵢ[𝕜] F₁) (W₂ : E₂ ≃ₗᵢ[𝕜] F₂)
    (h₁ : U₁.map W₁.toLinearMap = V₁)
    (h₂ : U₂.map W₂.toLinearMap = V₂) :
    (orthogonalBlockSumSubmodule U₁ U₂).map
        (LinearIsometryEquiv.withLpProdCongr 2 W₁ W₂).toLinearMap =
      orthogonalBlockSumSubmodule V₁ V₂ := by
  change (orthogonalBlockSumSubmodule U₁ U₂).map
    ((W₁.toLinearMap.prodMap W₂.toLinearMap).withLpMap 2) = _
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    obtain ⟨hy₁, hy₂⟩ := mem_orthogonalBlockSumSubmodule.mp hy
    rw [mem_orthogonalBlockSumSubmodule]
    have hcoe₁ : (W₁.toLinearEquiv : E₁ →ₗ[𝕜] F₁) = W₁.toLinearMap := rfl
    have hcoe₂ : (W₂.toLinearEquiv : E₂ →ₗ[𝕜] F₂) = W₂.toLinearMap := rfl
    have hmem₁ : (W₁.toLinearEquiv : E₁ →ₗ[𝕜] F₁) y.fst ∈ V₁ := by
      rw [hcoe₁, ← h₁]
      exact ⟨y.fst, hy₁, rfl⟩
    have hmem₂ : (W₂.toLinearEquiv : E₂ →ₗ[𝕜] F₂) y.snd ∈ V₂ := by
      rw [hcoe₂, ← h₂]
      exact ⟨y.snd, hy₂, rfl⟩
    change W₁ y.fst ∈ V₁ ∧ W₂ y.snd ∈ V₂
    exact ⟨hmem₁, hmem₂⟩
  · intro x hx
    obtain ⟨hx₁, hx₂⟩ := mem_orthogonalBlockSumSubmodule.mp hx
    rw [← h₁] at hx₁
    rw [← h₂] at hx₂
    obtain ⟨y₁, hy₁, hxy₁⟩ := hx₁
    obtain ⟨y₂, hy₂, hxy₂⟩ := hx₂
    refine ⟨WithLp.toLp 2 (y₁, y₂), ?_, ?_⟩
    · exact mem_orthogonalBlockSumSubmodule.mpr ⟨hy₁, hy₂⟩
    · apply WithLp.ofLp_injective 2
      apply Prod.ext
      · simpa only [LinearMap.coe_withLpMap, WithLp.map, LinearMap.prodMap_apply, WithLp.ofLp_toLp,
          WithLp.toLp_fst, WithLp.ofLp_fst] using hxy₁
      · simpa only [LinearMap.coe_withLpMap, WithLp.map, LinearMap.prodMap_apply, WithLp.ofLp_toLp,
          WithLp.toLp_snd, WithLp.ofLp_snd] using hxy₂

end TauCeti

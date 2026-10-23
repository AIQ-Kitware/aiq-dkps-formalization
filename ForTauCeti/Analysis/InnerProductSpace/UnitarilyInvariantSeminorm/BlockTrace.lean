/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.BlockSum

/-!
# Full trace norm of an orthogonal block sum

The trace norm (the Ky Fan sum over the entire source dimension) is
additive across orthogonal direct sums.  This is stronger than the triangle
inequality for Ky Fan sums and is the bookkeeping needed to assemble
complex principal-plane trace minimizers with no loss in the constant.

We use the established trace-of-modulus identity and the existing block
modulus theorem.  In particular, there is no sorting of two singular-value
lists and no separate matrix diagonalization.
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
    kyFanSum (finrank 𝕜 (WithLp 2 (E₁ × E₂))) (orthogonalBlockSum A B) =
      kyFanSum (finrank 𝕜 E₁) A + kyFanSum (finrank 𝕜 E₂) B := by
  classical
  let n₁ := finrank 𝕜 E₁
  let n₂ := finrank 𝕜 E₂
  let b₁ : OrthonormalBasis (Fin n₁) 𝕜 E₁ := stdOrthonormalBasis 𝕜 E₁
  let b₂ : OrthonormalBasis (Fin n₂) 𝕜 E₂ := stdOrthonormalBasis 𝕜 E₂
  let e : (Fin n₁ ⊕ Fin n₂) ≃ Fin (n₁ + n₂) := finSumFinEquiv
  let b : OrthonormalBasis (Fin (n₁ + n₂)) 𝕜 (WithLp 2 (E₁ × E₂)) :=
    (b₁.prod b₂).reindex e
  have hn : finrank 𝕜 (WithLp 2 (E₁ × E₂)) = n₁ + n₂ := by
    calc
      finrank 𝕜 (WithLp 2 (E₁ × E₂)) = finrank 𝕜 (E₁ × E₂) :=
        (WithLp.linearEquiv 2 𝕜 (E₁ × E₂)).finrank_eq
      _ = n₁ + n₂ := by simp [n₁, n₂, Module.finrank_prod]
  have hleft (i : Fin n₁) :
      RCLike.re ⟪operatorAbs (orthogonalBlockSum A B) (b (e (.inl i))),
          b (e (.inl i))⟫_𝕜 =
        RCLike.re ⟪operatorAbs A (b₁ i), b₁ i⟫_𝕜 := by
    rw [operatorAbs_orthogonalBlockSum]
    simp [b, OrthonormalBasis.reindex_apply]
  have hright (i : Fin n₂) :
      RCLike.re ⟪operatorAbs (orthogonalBlockSum A B) (b (e (.inr i))),
          b (e (.inr i))⟫_𝕜 =
        RCLike.re ⟪operatorAbs B (b₂ i), b₂ i⟫_𝕜 := by
    rw [operatorAbs_orthogonalBlockSum]
    simp [b, OrthonormalBasis.reindex_apply]
  calc
    kyFanSum (finrank 𝕜 (WithLp 2 (E₁ × E₂))) (orthogonalBlockSum A B) =
        ∑ k : Fin (n₁ + n₂),
          RCLike.re ⟪operatorAbs (orthogonalBlockSum A B) (b k), b k⟫_𝕜 := by
      rw [hn, kyFanSum_eq_sum_fin]
      exact (sum_re_inner_abs_self_eq_sum_singularValues
        (orthogonalBlockSum A B) hn b).symm
    _ = ∑ k : Fin n₁ ⊕ Fin n₂,
          RCLike.re ⟪operatorAbs (orthogonalBlockSum A B) (b (e k)), b (e k)⟫_𝕜 :=
      (e.sum_comp _).symm
    _ = (∑ i : Fin n₁, RCLike.re ⟪operatorAbs A (b₁ i), b₁ i⟫_𝕜) +
        (∑ i : Fin n₂, RCLike.re ⟪operatorAbs B (b₂ i), b₂ i⟫_𝕜) := by
      rw [Fintype.sum_sum_type]
      exact congrArg₂ (· + ·)
        (Finset.sum_congr rfl (fun i _ => hleft i))
        (Finset.sum_congr rfl (fun i _ => hright i))
    _ = kyFanSum (finrank 𝕜 E₁) A + kyFanSum (finrank 𝕜 E₂) B := by
      congr 1
      · exact (sum_re_inner_abs_self_eq_sum_singularValues A rfl b₁).trans
          (kyFanSum_eq_sum_fin _ A).symm
      · exact (sum_re_inner_abs_self_eq_sum_singularValues B rfl b₂).trans
          (kyFanSum_eq_sum_fin _ B).symm


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
  rw [← orthogonalBlockSum_linearIsometryEquiv W₁ W₂]
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
    simpa only [orthogonalBlockSum_apply, WithLp.toLp_fst,
      WithLp.toLp_snd] using And.intro hmem₁ hmem₂
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
      · simpa only [orthogonalBlockSum_apply, WithLp.ofLp_toLp,
          WithLp.toLp_fst, WithLp.ofLp_fst] using hxy₁
      · simpa only [orthogonalBlockSum_apply, WithLp.ofLp_toLp,
          WithLp.toLp_snd, WithLp.ofLp_snd] using hxy₂

end TauCeti

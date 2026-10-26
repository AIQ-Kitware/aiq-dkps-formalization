/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.OperatorIdeal.CompactSpectralTrace
public import ForTauCeti.Analysis.InnerProductSpace.EigenspaceBlockSum
public import TauCeti.Analysis.Normed.Lp.ProdLp
public import TauCeti.Analysis.Normed.Operator.Compact.Eigenspace
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.BlockSum
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Modulus

/-!
# Exact additive spectral penalties of compact positive blocks

Every nonnegative zero-preserving penalty is additive on orthogonal
sums of compact positive operators, in arbitrary Hilbert dimensions
over both fields. Costs may be infinite. Positive eigenspaces have
finite multiplicity; infinite-dimensional kernels are handled by the
zero penalty, rather than counted as positive spectral mass.
-/

public section

noncomputable section

namespace ContinuousLinearMap

open scoped ENNReal NNReal InnerProductSpace

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- An orthogonal block sum of compact operators is compact. -/
theorem isCompactOperator_withLpProdMap_two
    (A : E →L[𝕜] E) (B : F →L[𝕜] F)
    (hA : IsCompactOperator A) (hB : IsCompactOperator B) :
    IsCompactOperator (A.withLpProdMap 2 B) := by
  let d := WithLp.prodContinuousLinearEquiv 2 𝕜 E F
  let I₁ := d.symm.toContinuousLinearMap ∘L ContinuousLinearMap.inl 𝕜 E F
  let I₂ := d.symm.toContinuousLinearMap ∘L ContinuousLinearMap.inr 𝕜 E F
  have heq : A.withLpProdMap 2 B =
      I₁ ∘L A ∘L WithLp.fstL 2 𝕜 E F + I₂ ∘L B ∘L WithLp.sndL 2 𝕜 E F := by
    ext x
    simp [I₁, I₂, d, WithLp.ext_iff]
  rw [heq]
  exact ((hA.comp_clm (WithLp.fstL 2 𝕜 E F)).clm_comp I₁).add
    ((hB.comp_clm (WithLp.sndL 2 𝕜 E F)).clm_comp I₂)

/-- Positivity is preserved by the actual Hilbert orthogonal block sum. -/
theorem isPositive_withLpProdMap_two
    (A : E →L[𝕜] E) (B : F →L[𝕜] F) (hA : A.IsPositive) (hB : B.IsPositive) :
    (A.withLpProdMap 2 B).IsPositive := by
  apply isPositive_def.mpr
  constructor
  · intro x y
    change inner 𝕜 ((A.withLpProdMap 2 B) x) y = inner 𝕜 x ((A.withLpProdMap 2 B) y)
    rw [withLpProdMap_apply, withLpProdMap_apply, WithLp.prod_inner_apply,
      WithLp.prod_inner_apply]
    change inner 𝕜 (A x.fst) y.fst + inner 𝕜 (B x.snd) y.snd =
      inner 𝕜 x.fst (A y.fst) + inner 𝕜 x.snd (B y.snd)
    exact congrArg₂ (· + ·) (hA.inner_left_eq_inner_right x.fst y.fst)
      (hB.inner_left_eq_inner_right x.snd y.snd)
  · intro x
    change 0 ≤ RCLike.re (inner 𝕜 ((A.withLpProdMap 2 B) x) x)
    rw [withLpProdMap_apply, WithLp.prod_inner_apply]
    change 0 ≤ RCLike.re (inner 𝕜 (A x.fst) x.fst + inner 𝕜 (B x.snd) x.snd)
    rw [map_add]
    exact add_nonneg (hA.re_inner_nonneg_left _) (hB.re_inner_nonneg_left _)

variable [CompleteSpace E] [CompleteSpace F]

/-- **Additive compact block spectral trace.** Every nonnegative
zero-preserving singular-value penalty is additive on compact positive
orthogonal blocks. No continuity or monotonicity of the penalty,
finite ambient dimension, separability or summability is assumed. -/
theorem tsum_singularValue_penalty_withLpProdMap_of_positive
    (A : E →L[𝕜] E) (B : F →L[𝕜] F)
    (hAc : IsCompactOperator A) (hBc : IsCompactOperator B)
    (hA : A.IsPositive) (hB : B.IsPositive)
    (f : ℝ≥0 → ℝ≥0∞) (hf : f 0 = 0) :
    (∑' n, f ((A.withLpProdMap 2 B).singularValue n)) =
      (∑' n, f (A.singularValue n)) + ∑' n, f (B.singularValue n) := by
  have hSc := isCompactOperator_withLpProdMap_two A B hAc hBc
  have hS := isPositive_withLpProdMap_two A B hA hB
  rw [tsum_singularValue_penalty_eq_tsum_eigenspace _ hSc hS f hf,
    tsum_singularValue_penalty_eq_tsum_eigenspace A hAc hA f hf,
    tsum_singularValue_penalty_eq_tsum_eigenspace B hBc hB f hf,
    ← ENNReal.tsum_add]
  apply tsum_congr
  intro mu
  by_cases hzero : mu = 0
  · simp [hzero, hf]
  have hmu : ((mu : ℝ) : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr (by exact_mod_cast hzero)
  let : FiniteDimensional 𝕜 (Module.End.eigenspace A.toLinearMap ((mu : ℝ) : 𝕜)) :=
    hAc.finiteDimensional_eigenspace hmu
  let : FiniteDimensional 𝕜 (Module.End.eigenspace B.toLinearMap ((mu : ℝ) : 𝕜)) :=
    hBc.finiteDimensional_eigenspace hmu
  have hcount := LinearMap.finrank_eigenspace_prodMap_withLpMap_of_finite_eigenspaces
    A.toLinearMap B.toLinearMap ((mu : ℝ) : 𝕜)
  rw [coe_withLpProdMap, hcount, Nat.cast_add, add_mul]

variable {G H : Type*}
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- **Exact compact block spectral-cost additivity**, for arbitrary
rectangular operators between Hilbert spaces. Only compactness and a
nonnegative zero-preserving penalty are needed. Infinite costs and
infinite-dimensional kernels are included. -/
theorem tsum_singularValue_penalty_withLpProdMap
    (A : E →L[𝕜] F) (B : G →L[𝕜] H)
    (hAc : IsCompactOperator A) (hBc : IsCompactOperator B)
    (f : ℝ≥0 → ℝ≥0∞) (hf : f 0 = 0) :
    (∑' n, f ((A.withLpProdMap 2 B).singularValue n)) =
      (∑' n, f (A.singularValue n)) + ∑' n, f (B.singularValue n) := by
  have hAvalues : A.modulus.singularValue = A.singularValue :=
    funext (fun n => singularValue_modulus A n)
  have hBvalues : B.modulus.singularValue = B.singularValue :=
    funext (fun n => singularValue_modulus B n)
  have hAmc : IsCompactOperator A.modulus := by
    apply isCompactOperator_iff_tendsto_singularValue.mpr
    rw [hAvalues]
    exact hAc.tendsto_singularValue
  have hBmc : IsCompactOperator B.modulus := by
    apply isCompactOperator_iff_tendsto_singularValue.mpr
    rw [hBvalues]
    exact hBc.tendsto_singularValue
  have h := tsum_singularValue_penalty_withLpProdMap_of_positive A.modulus B.modulus
    hAmc hBmc A.isPositive_modulus B.isPositive_modulus f hf
  simpa only [singularValue_withLpProdMap, hAvalues, hBvalues] using h

end ContinuousLinearMap

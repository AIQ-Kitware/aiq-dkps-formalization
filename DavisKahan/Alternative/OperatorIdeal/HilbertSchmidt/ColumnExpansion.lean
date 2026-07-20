/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import ForMathlib.Analysis.InnerProductSpace.OrthogonalSeries
import Spectra.Spaces.Tensor.HilbertSchmidt

/-!
# Alternative column-expansion proof for the Hilbert--Schmidt tensor dictionary

This module preserves an independent proof of the Hilbert--Schmidt tensor
column expansion.  The canonical vendored implementation is already accepted;
this proof is retained because it replaces a closedness argument by an
orthogonal-series argument and may be useful for future upstreaming.

The proof avoids a closedness theorem for the set of tensors whose column
series converges to the original tensor.  Instead it proceeds as follows:

1. finite column sums are contractions because they are right tensor actions
   by finite-dimensional orthogonal projections;
2. pairwise orthogonality and the uniform partial-sum bound imply summability;
3. continuity of the tensor-to-operator map turns the tensor sum into the sum
   of rank-one column operators;
4. Hilbert-basis reconstruction identifies that operator sum with the original
   operator;
5. injectivity of the tensor-to-operator map identifies the tensor sum.
-/

open scoped InnerProductSpace ComplexConjugate BigOperators
open scoped HilbertTensor

namespace Spectra.HilbertSchmidtTensor

noncomputable section

universe u v

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

open ForMathlib.OrthogonalSeries

/-- Every finite column partial sum is bounded by the norm of the source
tensor. -/
theorem mathAhead_norm_sum_columnTensor_le
    {ι : Type*} (b : HilbertBasis ι ℂ F)
    (z : Space E F) (s : Finset ι) :
    ‖∑ i ∈ s, columnTensor b z i‖ ≤ ‖z‖ := by
  have hproj :
      ∑ i ∈ s, columnTensor b z i =
        HilbertTensor.mapL (ContinuousLinearMap.id ℂ E)
          ((Submodule.span ℂ (b '' (s : Set ι))).starProjection) z := by
    apply toOperator_injective
    ext x
    simp [columnTensor, toOperator_mapL_right, HilbertBasis.sum_repr]
  rw [hproj]
  calc
    ‖HilbertTensor.mapL (ContinuousLinearMap.id ℂ E)
        ((Submodule.span ℂ (b '' (s : Set ι))).starProjection) z‖
        ≤ ‖HilbertTensor.mapL (ContinuousLinearMap.id ℂ E)
            ((Submodule.span ℂ (b '' (s : Set ι))).starProjection)‖ * ‖z‖ :=
      (HilbertTensor.mapL _ _).le_opNorm z
    _ ≤ ‖z‖ := by
      rw [HilbertTensor.norm_mapL, norm_id]
      have hp :=
        (Submodule.span ℂ (b '' (s : Set ι))).norm_starProjection_le_one
      nlinarith [norm_nonneg z]

/-- The column family is summable, obtained directly from orthogonality and the
finite-projection contraction estimate. -/
theorem mathAhead_summable_columnTensor
    {ι : Type*} (b : HilbertBasis ι ℂ F) (z : Space E F) :
    Summable (columnTensor b z) := by
  apply summable_of_pairwise_inner_eq_zero_of_partial_sum_norm_le
    (columnTensor b z)
  · intro i j hij
    exact inner_columnTensor_eq_zero b z hij
  · exact norm_nonneg z
  · exact mathAhead_norm_sum_columnTensor_le b z

/-- Applying the tensor-to-operator map to the column sum reconstructs the
represented operator. -/
theorem mathAhead_toOperator_tsum_columnTensor
    {ι : Type*} (b : HilbertBasis ι ℂ F) (z : Space E F) :
    toOperator (∑' i, columnTensor b z i) = toOperator z := by
  have hsum := mathAhead_summable_columnTensor b z
  rw [← toOperatorL_apply, toOperatorL.map_tsum hsum]
  ext x
  simp_rw [columnTensor, toOperator_tmul,
    InnerProductSpace.rankOne_apply]
  have hrepr := (toOperator z).hasSum (b.hasSum_repr x)
  simpa only [map_smul, b.repr_apply_apply] using hrepr.tsum_eq

/-- The column tensors resolve the identity without a parameterized-series
closedness argument. -/
theorem mathAhead_hasSum_columnTensor
    {ι : Type*} (b : HilbertBasis ι ℂ F) (z : Space E F) :
    HasSum (columnTensor b z) z := by
  have hsum := mathAhead_summable_columnTensor b z
  apply hsum.hasSum_iff.mpr
  apply toOperator_injective
  exact mathAhead_toOperator_tsum_columnTensor b z

/-- Parseval for the replacement column decomposition. -/
theorem mathAhead_norm_sq_eq_tsum_column_norm_sq
    {ι : Type*} (b : HilbertBasis ι ℂ F) (z : Space E F) :
    ‖z‖ ^ 2 = ∑' i, ‖toOperator z (b i)‖ ^ 2 := by
  have hpyth :=
    (mathAhead_hasSum_columnTensor b z).norm_sq_eq_tsum_of_pairwise_inner_eq_zero
      (fun i j hij => inner_columnTensor_eq_zero b z hij)
  simpa [columnTensor, HilbertTensor.norm_tmul, b.norm_apply,
    mul_one, one_pow] using hpyth

/-- Square-summable operator columns give a summable tensor column series. -/
theorem mathAhead_summable_columnSeries
    {ι : Type*} (b : HilbertBasis ι ℂ F)
    (A : F →L[ℂ] E) (hA : Summable fun i => ‖A (b i)‖ ^ 2) :
    Summable fun i => A (b i) ⊗̂ₜ[ℂ] Conj.toConj (b i) := by
  apply (summable_iff_norm_sq_summable_of_pairwise_inner_eq_zero
    (fun i => A (b i) ⊗̂ₜ[ℂ] Conj.toConj (b i)) ?_).2
  · intro i j hij
    simp [HilbertTensor.inner_tmul_tmul, Conj.inner_def,
      b.orthonormal.inner_right hij]
  · simpa [HilbertTensor.norm_tmul, b.norm_apply,
      mul_one, one_pow] using hA

/-- The column-series tensor represents the original operator, using the
protected continuous-linear-map theorem for infinite sums. -/
theorem mathAhead_toOperator_ofOperator
    {ι : Type*} (b : HilbertBasis ι ℂ F)
    (A : F →L[ℂ] E) (hA : Summable fun i => ‖A (b i)‖ ^ 2) :
    toOperator (ofOperator b A hA) = A := by
  ext x
  have hseries := mathAhead_summable_columnSeries b A hA
  rw [ofOperator, ← toOperatorL_apply, toOperatorL.map_tsum hseries]
  simp_rw [toOperator_tmul, InnerProductSpace.rankOne_apply]
  have hrepr := A.hasSum (b.hasSum_repr x)
  simpa only [map_smul, b.repr_apply_apply] using hrepr.tsum_eq


/-- The square norms of the represented operator columns are summable. -/
theorem mathAhead_summable_column_norm_sq
    {ι : Type*} (b : HilbertBasis ι ℂ F) (z : Space E F) :
    Summable fun i => ‖toOperator z (b i)‖ ^ 2 := by
  have horth : Pairwise fun i j =>
      ⟪columnTensor b z i, columnTensor b z j⟫_ℂ = 0 :=
    fun i j hij => inner_columnTensor_eq_zero b z hij
  have hnorm :=
    (summable_iff_norm_sq_summable_of_pairwise_inner_eq_zero
      (columnTensor b z) horth).1
      (mathAhead_summable_columnTensor b z)
  simpa [columnTensor, HilbertTensor.norm_tmul, b.norm_apply,
    mul_one, one_pow] using hnorm

/-- Reconstructing from the columns of a represented operator recovers the
original tensor. -/
theorem mathAhead_ofOperator_toOperator
    {ι : Type*} (b : HilbertBasis ι ℂ F) (z : Space E F) :
    ofOperator b (toOperator z)
      (mathAhead_summable_column_norm_sq b z) = z := by
  apply toOperator_injective
  rw [mathAhead_toOperator_ofOperator]

/-- The reconstructed tensor norm is exactly the basis square norm. -/
theorem mathAhead_norm_ofOperator_sq
    {ι : Type*} (b : HilbertBasis ι ℂ F)
    (A : F →L[ℂ] E) (hA : Summable fun i => ‖A (b i)‖ ^ 2) :
    ‖ofOperator b A hA‖ ^ 2 = ∑' i, ‖A (b i)‖ ^ 2 := by
  rw [mathAhead_norm_sq_eq_tsum_column_norm_sq b]
  simp [mathAhead_toOperator_ofOperator b A hA]

/-- Basis square summability is equivalent to representation by a unique
Hilbert tensor. -/
theorem mathAhead_existsUnique_tensor_iff_summable_columns
    {ι : Type*} (b : HilbertBasis ι ℂ F) (A : F →L[ℂ] E) :
    (∃! z : Space E F, toOperator z = A) ↔
      Summable (fun i => ‖A (b i)‖ ^ 2) := by
  constructor
  · rintro ⟨z, rfl, _⟩
    exact mathAhead_summable_column_norm_sq b z
  · intro hA
    refine ⟨ofOperator b A hA, mathAhead_toOperator_ofOperator b A hA, ?_⟩
    intro z hz
    exact toOperator_injective
      (hz.trans (mathAhead_toOperator_ofOperator b A hA).symm)

end

end Spectra.HilbertSchmidtTensor

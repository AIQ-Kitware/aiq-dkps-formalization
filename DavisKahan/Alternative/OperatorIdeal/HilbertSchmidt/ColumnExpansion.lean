/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import ForTauCeti.Analysis.InnerProductSpace.OrthogonalSeries
import ForTauCeti.Analysis.InnerProductSpace.ProjectionGeometry
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

namespace Spectra.HilbertSchmidtTensor

-- `HilbertTensor` is `Spectra.HilbertTensor`, so its scoped notation can only be
-- opened once the `Spectra` namespace is entered.
open scoped Spectra.HilbertTensor

noncomputable section

universe u v

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

open TauCeti.OrthogonalSeries

/-- Every finite column partial sum is bounded by the norm of the source
tensor. -/
theorem mathAhead_norm_sum_columnTensor_le
    {ι : Type*} (b : HilbertBasis ι ℂ F)
    (z : Space E F) (s : Finset ι) :
    ‖∑ i ∈ s, columnTensor b z i‖ ≤ ‖z‖ := by
  -- The finite span is finite-dimensional, hence complete, hence carries an
  -- orthogonal projection.  None of that is found automatically: Mathlib
  -- withholds `FiniteDimensional.complete` as an instance because the scalar
  -- field would be an unknown metavariable.
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (b '' (s : Set ι))) :=
    FiniteDimensional.span_of_finite ℂ (s.finite_toSet.image (⇑b))
  haveI : CompleteSpace (Submodule.span ℂ (b '' (s : Set ι))) :=
    FiniteDimensional.complete ℂ _
  let P : F →L[ℂ] F :=
    (Submodule.span ℂ (b '' (s : Set ι))).starProjection
  have hPadj : P.adjoint = P := by
    exact (isSelfAdjoint_starProjection
      (Submodule.span ℂ (b '' (s : Set ι)))).adjoint_eq
  have hproj :
      ∑ i ∈ s, columnTensor b z i =
        HilbertTensor.mapL (ContinuousLinearMap.id ℂ E) (Conj.map P) z := by
    apply toOperator_injective
    rw [← hPadj, toOperator_mapL_right (B := P)]
    ext x
    rw [toOperator_sum]
    -- `x` must be pushed inside the finite sum first, otherwise the rank-one
    -- operators are never applied and `rankOne_apply` cannot fire.
    simp_rw [ContinuousLinearMap.sum_apply, columnTensor, toOperator_tmul,
      InnerProductSpace.rankOne_apply]
    -- The composition has to be unfolded before `P x` occurs syntactically.
    rw [ContinuousLinearMap.comp_apply,
      show P x = ∑ i ∈ s, ⟪b i, x⟫_ℂ • b i from
        TauCeti.Orthonormal.starProjection_span_image_apply b.orthonormal s x]
    simp only [map_sum, map_smul]
  rw [hproj]
  have hP : ‖P‖ ≤ 1 := by
    simpa [P] using
      (Submodule.span ℂ (b '' (s : Set ι))).starProjection_norm_le
  have hmap :
      ‖HilbertTensor.mapL (ContinuousLinearMap.id ℂ E) (Conj.map P)‖ ≤ 1 := by
    -- `‖id‖ = 1` would need `E` nontrivial, which is not assumed here; the
    -- inequality `‖id‖ ≤ 1` carries the estimate just as well.
    rw [HilbertTensor.norm_mapL, Conj.norm_map]
    calc ‖ContinuousLinearMap.id ℂ E‖ * ‖P‖
        ≤ 1 * 1 :=
          mul_le_mul ContinuousLinearMap.norm_id_le hP (norm_nonneg P)
            zero_le_one
      _ = 1 := one_mul 1
  -- Spelling the operator out keeps `le_opNorm` from elaborating against
  -- metavariables, which otherwise blows the `whnf` heartbeat budget.
  have hle :=
    (HilbertTensor.mapL (ContinuousLinearMap.id ℂ E) (Conj.map P)).le_opNorm z
  calc
    ‖HilbertTensor.mapL (ContinuousLinearMap.id ℂ E) (Conj.map P) z‖
        ≤ ‖HilbertTensor.mapL (ContinuousLinearMap.id ℂ E) (Conj.map P)‖ * ‖z‖ :=
      hle
    _ ≤ 1 * ‖z‖ :=
      mul_le_mul_of_nonneg_right hmap (norm_nonneg z)
    _ = ‖z‖ := one_mul _

/-- The column family is summable, obtained directly from orthogonality and the
finite-projection contraction estimate. -/
theorem mathAhead_summable_columnTensor
    {ι : Type*} (b : HilbertBasis ι ℂ F) (z : Space E F) :
    Summable (columnTensor b z) := by
  -- The scalar field occurs only in the orthogonality hypothesis, never in the
  -- `Summable` goal, so it has to be supplied.
  apply summable_of_pairwise_inner_eq_zero_of_partial_sum_norm_le (𝕜 := ℂ)
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
  have hseries := mathAhead_summable_columnTensor b z
  ext x
  have hcol : ∀ i : ι,
      (rightTensor x).adjoint (columnTensor b z i) =
        ⟪b i, x⟫_ℂ • toOperator z (b i) := by
    intro i
    rw [columnTensor, ← toOperator_apply, toOperator_tmul,
      InnerProductSpace.rankOne_apply]
  have hval :
      (rightTensor x).adjoint (∑' i, columnTensor b z i) =
        toOperator (∑' i, columnTensor b z i) x := rfl
  have h1 : HasSum (fun i => ⟪b i, x⟫_ℂ • toOperator z (b i))
      (toOperator (∑' i, columnTensor b z i) x) := by
    simpa only [hcol, hval] using
      hseries.hasSum.mapL ((rightTensor x).adjoint)
  have h2 : HasSum (fun i => ⟪b i, x⟫_ℂ • toOperator z (b i))
      (toOperator z x) := by
    simpa only [map_smul, b.repr_apply_apply] using
      (b.hasSum_repr x).mapL (toOperator z)
  exact h1.unique h2

/-- The column tensors resolve the identity without a parameterized-series
closedness argument. -/
theorem mathAhead_hasSum_columnTensor
    {ι : Type*} (b : HilbertBasis ι ℂ F) (z : Space E F) :
    HasSum (columnTensor b z) z := by
  have hsum := mathAhead_summable_columnTensor b z
  have htsum : (∑' i, columnTensor b z i) = z := by
    apply toOperator_injective
    exact mathAhead_toOperator_tsum_columnTensor b z
  -- Rewriting the goal backwards would also fold `z` inside `columnTensor b z`;
  -- rewrite the summed value in the hypothesis instead.
  have hres := hsum.hasSum
  rwa [htsum] at hres

/-- Parseval for the replacement column decomposition. -/
theorem mathAhead_norm_sq_eq_tsum_column_norm_sq
    {ι : Type*} (b : HilbertBasis ι ℂ F) (z : Space E F) :
    ‖z‖ ^ 2 = ∑' i, ‖toOperator z (b i)‖ ^ 2 := by
  have hpyth :=
    (mathAhead_hasSum_columnTensor b z).norm_sq_eq_tsum_of_pairwise_inner_eq_zero
      (fun i j hij => inner_columnTensor_eq_zero b z hij)
  simpa [columnTensor, HilbertTensor.norm_tmul, b.orthonormal.norm_eq_one,
    mul_one, one_pow] using hpyth

/-- Square-summable operator columns give a summable tensor column series. -/
theorem mathAhead_summable_columnSeries
    {ι : Type*} (b : HilbertBasis ι ℂ F)
    (A : F →L[ℂ] E) (hA : Summable fun i => ‖A (b i)‖ ^ 2) :
    Summable fun i => A (b i) ⊗̂ₜ[ℂ] Conj.toConj (b i) := by
  have horth : Pairwise fun i j =>
      ⟪A (b i) ⊗̂ₜ[ℂ] Conj.toConj (b i),
        A (b j) ⊗̂ₜ[ℂ] Conj.toConj (b j)⟫_ℂ = 0 := by
    intro i j hij
    simp [HilbertTensor.inner_tmul_tmul, Conj.inner_def,
      b.orthonormal.inner_eq_zero hij.symm]
  refine (summable_iff_norm_sq_summable_of_pairwise_inner_eq_zero (𝕜 := ℂ)
    _ horth).2 ?_
  simpa [HilbertTensor.norm_tmul, Conj.norm_toConj,
    b.orthonormal.norm_eq_one, mul_one, one_pow] using hA

/-- The column-series tensor represents the original operator, using the
same basis reconstruction but the independent orthogonal-series summability
proof above. -/
theorem mathAhead_toOperator_ofOperator
    {ι : Type*} (b : HilbertBasis ι ℂ F)
    (A : F →L[ℂ] E) (hA : Summable fun i => ‖A (b i)‖ ^ 2) :
    toOperator (ofOperator b A hA) = A := by
  have hseries := mathAhead_summable_columnSeries b A hA
  ext x
  have hcol : ∀ i : ι,
      (rightTensor x).adjoint
          (A (b i) ⊗̂ₜ[ℂ] Conj.toConj (b i)) =
        ⟪b i, x⟫_ℂ • A (b i) := by
    intro i
    rw [← toOperator_apply, toOperator_tmul,
      InnerProductSpace.rankOne_apply]
  have hval :
      (rightTensor x).adjoint
          (∑' i, A (b i) ⊗̂ₜ[ℂ] Conj.toConj (b i)) =
        toOperator (ofOperator b A hA) x := rfl
  have h1 : HasSum (fun i => ⟪b i, x⟫_ℂ • A (b i))
      (toOperator (ofOperator b A hA) x) := by
    simpa only [hcol, hval] using
      hseries.hasSum.mapL ((rightTensor x).adjoint)
  have h2 : HasSum (fun i => ⟪b i, x⟫_ℂ • A (b i)) (A x) := by
    simpa only [map_smul, b.repr_apply_apply] using
      A.hasSum (b.hasSum_repr x)
  exact h1.unique h2


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
  simpa [columnTensor, HilbertTensor.norm_tmul, b.orthonormal.norm_eq_one,
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

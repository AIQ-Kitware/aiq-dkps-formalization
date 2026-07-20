/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Orthogonal series from bounded finite partial sums

This Mathlib-only module develops general Hilbert-space series facts that were
needed while repairing a rectangular Hilbert--Schmidt tensor construction.
The results are independent of Davis--Kahan theory and of the Spectra package.

The main point is that pairwise orthogonality converts unconditional
summability into scalar square summability.  A uniform bound on all finite
partial sums therefore gives summability directly, without a separate
closedness theorem for a parameterized family of series.
-/

open Filter
open scoped BigOperators

namespace ForMathlib.OrthogonalSeries

noncomputable section

universe u v

variable {𝕜 : Type u} {H : Type v}
variable [RCLike 𝕜]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- Pythagoras for a finite sum of pairwise orthogonal vectors. -/
theorem norm_sq_finset_sum_of_pairwise_inner_eq_zero
    {ι : Type*} (f : ι → H)
    (horth : Pairwise fun i j => ⟪f i, f j⟫_𝕜 = 0)
    (s : Finset ι) :
    ‖∑ i ∈ s, f i‖ ^ 2 = ∑ i ∈ s, ‖f i‖ ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hinner : ⟪f a, ∑ i ∈ s, f i⟫_𝕜 = 0 := by
        rw [inner_sum]
        exact Finset.sum_eq_zero fun i hi =>
          horth (fun hai => ha (hai ▸ hi))
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      have hpyth :=
        norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
          (f a) (∑ i ∈ s, f i) hinner
      calc
        ‖f a + ∑ i ∈ s, f i‖ ^ 2 =
            ‖f a‖ ^ 2 + ‖∑ i ∈ s, f i‖ ^ 2 := by
          simpa only [pow_two] using hpyth
        _ = ‖f a‖ ^ 2 + ∑ i ∈ s, ‖f i‖ ^ 2 := by rw [ih]

/-- The square norm of the difference of two finite orthogonal partial sums is
exactly the sum of the omitted square norms in the two directions. -/
theorem norm_sq_sdiff_sum_of_pairwise_inner_eq_zero
    {ι : Type*} [DecidableEq ι] (f : ι → H)
    (horth : Pairwise fun i j => ⟪f i, f j⟫_𝕜 = 0)
    (s₁ s₂ : Finset ι) :
    ‖(∑ i ∈ s₁, f i) - ∑ i ∈ s₂, f i‖ ^ 2 =
      (∑ i ∈ s₁ \ s₂, ‖f i‖ ^ 2) +
        ∑ i ∈ s₂ \ s₁, ‖f i‖ ^ 2 := by
  rw [← Finset.sum_sdiff_sub_sum_sdiff, sub_eq_add_neg,
    ← Finset.sum_neg_distrib]
  let g : ι → H := fun i => if i ∈ s₁ then f i else -f i
  have hgorth : Pairwise fun i j => ⟪g i, g j⟫_𝕜 = 0 := by
    intro i j hij
    by_cases hi : i ∈ s₁ <;> by_cases hj : j ∈ s₁ <;>
      simp [g, hi, hj, horth hij]
  have hg₁ : ∀ i ∈ s₁ \ s₂, g i = f i := by
    intro i hi
    exact if_pos (Finset.sdiff_subset hi)
  have hg₂ : ∀ i ∈ s₂ \ s₁, g i = -f i := by
    intro i hi
    exact if_neg (Finset.mem_sdiff.mp hi).2
  have hgnorm : ∀ i, ‖g i‖ = ‖f i‖ := by
    intro i
    dsimp only [g]
    split_ifs <;> simp
  have hdisj : Disjoint (s₁ \ s₂) (s₂ \ s₁) :=
    disjoint_sdiff_sdiff
  have hpyth := norm_sq_finset_sum_of_pairwise_inner_eq_zero
    g hgorth (s₁ \ s₂ ∪ s₂ \ s₁)
  rw [Finset.sum_union hdisj] at hpyth
  convert! hpyth using 4
  · refine Finset.sum_congr rfl fun i hi => ?_
    simp only [hg₁ i hi]
  · refine Finset.sum_congr rfl fun i hi => ?_
    simp only [hg₂ i hi]
  · simp only [hgnorm]
  · simp only [hgnorm]

/-- For a pairwise orthogonal family in a complete Hilbert space,
unconditional summability is equivalent to summability of the square norms. -/
theorem summable_iff_norm_sq_summable_of_pairwise_inner_eq_zero
    {ι : Type*} [CompleteSpace H] (f : ι → H)
    (horth : Pairwise fun i j => ⟪f i, f j⟫_𝕜 = 0) :
    Summable f ↔ Summable fun i => ‖f i‖ ^ 2 := by
  classical
  simp only [summable_iff_cauchySeq_finset,
    NormedAddCommGroup.cauchySeq_iff, norm_neg_add, Real.norm_eq_abs]
  constructor
  · intro hf ε hε
    obtain ⟨a, ha⟩ := hf _ (Real.sqrt_pos.mpr hε)
    refine ⟨a, ?_⟩
    intro s₁ hs₁ s₂ hs₂
    rw [← Finset.sum_sdiff_sub_sum_sdiff]
    refine (abs_sub _ _).trans_lt ?_
    have hnonneg : ∀ i, 0 ≤ ‖f i‖ ^ 2 := fun i => sq_nonneg _
    simp only [Finset.abs_sum_of_nonneg' hnonneg]
    have hsq :
        ((∑ i ∈ s₁ \ s₂, ‖f i‖ ^ 2) +
          ∑ i ∈ s₂ \ s₁, ‖f i‖ ^ 2) < Real.sqrt ε ^ 2 := by
      rw [← norm_sq_sdiff_sum_of_pairwise_inner_eq_zero f horth,
        sq_lt_sq, abs_of_nonneg (Real.sqrt_nonneg _),
        abs_of_nonneg (norm_nonneg _)]
      exact ha s₁ hs₁ s₂ hs₂
    have hsqrt := Real.sq_sqrt (le_of_lt hε)
    linarith
  · intro hf ε hε
    have hε' : 0 < ε ^ 2 / 2 := half_pos (sq_pos_of_pos hε)
    obtain ⟨a, ha⟩ := hf _ hε'
    refine ⟨a, ?_⟩
    intro s₁ hs₁ s₂ hs₂
    refine (abs_lt_of_sq_lt_sq' ?_ (le_of_lt hε)).2
    have has : a ≤ s₁ ⊓ s₂ := le_inf hs₁ hs₂
    rw [norm_sq_sdiff_sum_of_pairwise_inner_eq_zero f horth]
    have hs₁' : ∑ x ∈ s₁ \ s₂, ‖f x‖ ^ 2 < ε ^ 2 / 2 := by
      convert ha _ hs₁ _ has
      have hsub : s₁ ⊓ s₂ ⊆ s₁ := Finset.inter_subset_left
      rw [← Finset.sum_sdiff hsub, add_tsub_cancel_right,
        Finset.abs_sum_of_nonneg']
      · simp
      · exact fun i => sq_nonneg _
    have hs₂' : ∑ x ∈ s₂ \ s₁, ‖f x‖ ^ 2 < ε ^ 2 / 2 := by
      convert ha _ hs₂ _ has
      have hsub : s₁ ⊓ s₂ ⊆ s₂ := Finset.inter_subset_right
      rw [← Finset.sum_sdiff hsub, add_tsub_cancel_right,
        Finset.abs_sum_of_nonneg']
      · simp
      · exact fun i => sq_nonneg _
    linarith

/-- A pairwise orthogonal family is summable when all finite partial sums have a
common norm bound. -/
theorem summable_of_pairwise_inner_eq_zero_of_partial_sum_norm_le
    {ι : Type*} [CompleteSpace H] (f : ι → H)
    (horth : Pairwise fun i j => ⟪f i, f j⟫_𝕜 = 0)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ s : Finset ι, ‖∑ i ∈ s, f i‖ ≤ C) :
    Summable f := by
  apply (summable_iff_norm_sq_summable_of_pairwise_inner_eq_zero f horth).2
  apply summable_of_sum_le
  · intro i
    exact sq_nonneg _
  · intro s
    rw [← norm_sq_finset_sum_of_pairwise_inner_eq_zero f horth]
    nlinarith [hbound s, norm_nonneg (∑ i ∈ s, f i)]

/-- Parseval for any pairwise orthogonal family with a specified sum. -/
theorem HasSum.norm_sq_eq_tsum_of_pairwise_inner_eq_zero
    {ι : Type*} [CompleteSpace H] {f : ι → H} {z : H}
    (hsum : HasSum f z)
    (horth : Pairwise fun i j => ⟪f i, f j⟫_𝕜 = 0) :
    ‖z‖ ^ 2 = ∑' i, ‖f i‖ ^ 2 := by
  have hnorm : Summable fun i => ‖f i‖ ^ 2 :=
    (summable_iff_norm_sq_summable_of_pairwise_inner_eq_zero f horth).1
      hsum.summable
  have hleft :
      Tendsto (fun s : Finset ι => ‖∑ i ∈ s, f i‖ ^ 2)
        (SummationFilter.unconditional ι).filter (𝓝 (‖z‖ ^ 2)) :=
    (continuous_norm.pow 2).tendsto z |>.comp hsum
  have hright0 :
      Tendsto (fun s : Finset ι => ∑ i ∈ s, ‖f i‖ ^ 2)
        (SummationFilter.unconditional ι).filter
        (𝓝 (∑' i, ‖f i‖ ^ 2)) :=
    hnorm.hasSum
  have hright :
      Tendsto (fun s : Finset ι => ‖∑ i ∈ s, f i‖ ^ 2)
        (SummationFilter.unconditional ι).filter
        (𝓝 (∑' i, ‖f i‖ ^ 2)) := by
    simpa only [norm_sq_finset_sum_of_pairwise_inner_eq_zero f horth]
      using hright0
  exact tendsto_nhds_unique hleft hright

end

end ForMathlib.OrthogonalSeries

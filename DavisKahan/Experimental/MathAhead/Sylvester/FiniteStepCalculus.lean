/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.MathAhead.Sylvester.SelfAdjointBorelCalculus

/-!
# Finite spectral-step calculus

This file provides the finite measurable functional-calculus identities used by
the separated Sylvester reconstruction.  It is independent of the compact-cover
construction: the compiler-side topology helpers only need to produce a finite
measurable disjoint cover and representatives.
-/

namespace ForMathlib
namespace DavisKahanExt

open MeasureTheory Set Filter
open scoped InnerProductSpace BigOperators
open Spectra
open Spectra.QuantumMechanics.SpectralTheory

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Complex-valued finite step symbol attached to measurable cells. -/
noncomputable def finiteStepSymbol {n : ℕ}
    (cell : Fin n → Set ℝ) (rep : Fin n → ℝ) : ℝ → ℂ :=
  fun x => ∑ i, Set.indicator (cell i) (fun _ => (rep i : ℂ)) x

/-- The finite step symbol is measurable. -/
theorem measurable_finiteStepSymbol {n : ℕ}
    (cell : Fin n → Set ℝ) (hcell : ∀ i, MeasurableSet (cell i))
    (rep : Fin n → ℝ) : Measurable (finiteStepSymbol cell rep) := by
  unfold finiteStepSymbol
  exact Finset.measurable_sum _ fun i _ => measurable_const.indicator (hcell i)

/-- A crude global bound for the finite step symbol. -/
theorem bounded_finiteStepSymbol {n : ℕ}
    (cell : Fin n → Set ℝ) (rep : Fin n → ℝ) :
    ∃ C : ℝ, ∀ x, ‖finiteStepSymbol cell rep x‖ ≤ C := by
  refine ⟨∑ i, |rep i|, fun x => ?_⟩
  unfold finiteStepSymbol
  calc
    ‖∑ i, Set.indicator (cell i) (fun _ => (rep i : ℂ)) x‖
        ≤ ∑ i, ‖Set.indicator (cell i) (fun _ => (rep i : ℂ)) x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i, |rep i| := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hx : x ∈ cell i
      · rw [Set.indicator_of_mem hx, Complex.norm_real, Real.norm_eq_abs]
      · rw [Set.indicator_of_notMem hx, norm_zero]
        exact abs_nonneg _

/-- The bounded calculus is additive over a finite step function. -/
theorem boundedSelfAdjointBorelCalculusC_finiteStep
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A)
    {n : ℕ} (cell : Fin n → Set ℝ)
    (hcell : ∀ i, MeasurableSet (cell i)) (rep : Fin n → ℝ) :
    boundedSelfAdjointBorelCalculusC A hA
      (finiteStepSymbol cell rep)
      (measurable_finiteStepSymbol cell hcell rep)
      (bounded_finiteStepSymbol cell rep) =
      ∑ i, (rep i : ℂ) •
        boundedSelfAdjointSpectralProjection A hA (cell i) (hcell i) := by
  classical
  unfold boundedSelfAdjointBorelCalculusC finiteStepSymbol
  induction n with
  | zero =>
      simp [spectralCalculus_congr]
  | succ n ih =>
      let i0 : Fin (n + 1) := ⟨0, Nat.succ_pos _⟩
      let tailCell : Fin n → Set ℝ := fun i => cell i.succ
      let tailRep : Fin n → ℝ := fun i => rep i.succ
      have htailm : Measurable (finiteStepSymbol tailCell tailRep) :=
        measurable_finiteStepSymbol tailCell (fun i => hcell i.succ) tailRep
      have htailb := bounded_finiteStepSymbol tailCell tailRep
      have hheadm : Measurable
          (Set.indicator (cell i0) fun _ => (rep i0 : ℂ)) :=
        measurable_const.indicator (hcell i0)
      have hheadb : ∃ C : ℝ, ∀ x,
          ‖Set.indicator (cell i0) (fun _ => (rep i0 : ℂ)) x‖ ≤ C := by
        refine ⟨|rep i0|, fun x => ?_⟩
        by_cases hx : x ∈ cell i0
        · rw [Set.indicator_of_mem hx, Complex.norm_real, Real.norm_eq_abs]
        · rw [Set.indicator_of_notMem hx, norm_zero]
          exact abs_nonneg _
      have hsplit : finiteStepSymbol cell rep = fun x =>
          Set.indicator (cell i0) (fun _ => (rep i0 : ℂ)) x +
            finiteStepSymbol tailCell tailRep x := by
        funext x
        rw [finiteStepSymbol]
        simpa [i0, tailCell, tailRep, Fin.sum_univ_succ]
      rw [spectralCalculus_congr (boundedSelfAdjointGroup A hA) hsplit
        (measurable_finiteStepSymbol cell hcell rep)
        (bounded_finiteStepSymbol cell rep)
        (hheadm.add htailm) (bounded_add hheadb htailb)]
      rw [spectralCalculus_add (boundedSelfAdjointGroup A hA)
        _ _ hheadm hheadb htailm htailb
        (hheadm.add htailm) (bounded_add hheadb htailb)]
      have hhead : spectralCalculus (boundedSelfAdjointGroup A hA)
          (Set.indicator (cell i0) fun _ => (rep i0 : ℂ)) hheadm hheadb =
          (rep i0 : ℂ) • boundedSelfAdjointSpectralProjection A hA
            (cell i0) (hcell i0) := by
        have hfun : (Set.indicator (cell i0) fun _ => (rep i0 : ℂ)) =
            fun x => (rep i0 : ℂ) *
              Set.indicator (cell i0) (fun _ => (1 : ℂ)) x := by
          funext x
          by_cases hx : x ∈ cell i0 <;>
            simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
        rw [spectralCalculus_congr (boundedSelfAdjointGroup A hA) hfun
          hheadm hheadb
          (measurable_const.mul (measurable_const.indicator (hcell i0)))
          ⟨|rep i0|, fun x => by
            rw [norm_mul]
            by_cases hx : x ∈ cell i0
            · rw [Set.indicator_of_mem hx, norm_one, mul_one, Complex.norm_real,
                Real.norm_eq_abs]
            · rw [Set.indicator_of_notMem hx, norm_zero, mul_zero]
              exact abs_nonneg _⟩]
        rw [spectralCalculus_smul (boundedSelfAdjointGroup A hA)
          (rep i0 : ℂ) (Set.indicator (cell i0) fun _ => (1 : ℂ))
          (measurable_const.indicator (hcell i0)) (indicator_one_bdd (cell i0))]
        rfl
      rw [hhead]
      have ihtail := boundedSelfAdjointBorelCalculusC_finiteStep
        A hA tailCell (fun i => hcell i.succ) tailRep
      unfold boundedSelfAdjointBorelCalculusC at ihtail
      rw [ihtail]
      simp [i0, tailCell, tailRep, Fin.sum_univ_succ]

/-- Two measurable spectral projections depend only on the intersection of the
sets with the real spectrum. -/
theorem spectralPVM_proj_congr_of_inter_spectrum_eq
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A)
    {s t : Set ℝ} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hst : s ∩ realSpectrum A = t ∩ realSpectrum A) :
    boundedSelfAdjointSpectralProjection A hA s hs =
      boundedSelfAdjointSpectralProjection A hA t ht := by
  rw [← boundedSelfAdjointBorelCalculusC_indicator A hA s hs,
    ← boundedSelfAdjointBorelCalculusC_indicator A hA t ht]
  apply boundedSelfAdjointBorelCalculusC_congr_on_spectrum A hA
  intro x hx
  have : x ∈ s ↔ x ∈ t := by
    have hmem : x ∈ s ∩ realSpectrum A ↔ x ∈ t ∩ realSpectrum A := by rw [hst]
    simpa [hx] using hmem
  by_cases hxs : x ∈ s
  · have hxt : x ∈ t := this.mp hxs
    simp [Set.indicator_of_mem hxs, Set.indicator_of_mem hxt]
  · have hxt : x ∉ t := fun h => hxs (this.mpr h)
    simp [Set.indicator_of_notMem hxs, Set.indicator_of_notMem hxt]

/-- Pairwise disjoint measurable cells give pairwise orthogonal spectral
projections. -/
theorem spectralProjection_pairwise_orthogonal
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A)
    {n : ℕ} (cell : Fin n → Set ℝ)
    (hcell : ∀ i, MeasurableSet (cell i))
    (hdisj : Set.PairwiseDisjoint Set.univ cell) :
    ∀ i j, i ≠ j →
      boundedSelfAdjointSpectralProjection A hA (cell i) (hcell i) ∘L
        boundedSelfAdjointSpectralProjection A hA (cell j) (hcell j) = 0 := by
  intro i j hij
  let P := boundedSelfAdjointSpectralPVM A hA
  change P.proj (cell i) (hcell i) * P.proj (cell j) (hcell j) = 0
  rw [P.proj_inter]
  have hd : Disjoint (cell i) (cell j) := hdisj (Set.mem_univ i) (Set.mem_univ j) hij
  have hinter : cell i ∩ cell j = ∅ := Set.disjoint_iff_inter_eq_empty.mp hd
  exact (P.proj_congr hinter (hcell i |>.inter (hcell j)) MeasurableSet.empty).trans
    P.proj_empty

/-- A finite disjoint spectral cover sums to the identity. -/
theorem spectralProjection_finset_sum_eq_id
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A)
    {n : ℕ} (cell : Fin n → Set ℝ)
    (hcell : ∀ i, MeasurableSet (cell i))
    (hdisj : Set.PairwiseDisjoint Set.univ cell)
    (hcover : realSpectrum A ⊆ ⋃ i, cell i) :
    ∑ i, boundedSelfAdjointSpectralProjection A hA (cell i) (hcell i) =
      ContinuousLinearMap.id ℂ H := by
  let P := boundedSelfAdjointSpectralPVM A hA
  have hunion : P.proj (⋃ i, cell i) (MeasurableSet.iUnion hcell) =
      P.proj Set.univ MeasurableSet.univ := by
    apply spectralPVM_proj_congr_of_inter_spectrum_eq A hA
    ext x
    constructor
    · intro hx
      exact ⟨Set.mem_univ x, hx.2⟩
    · intro hx
      exact ⟨hcover hx.2, hx.2⟩
  rw [← P.proj_univ, ← hunion]
  induction n with
  | zero =>
      simp
  | succ n ih =>
      let i0 : Fin (n + 1) := ⟨0, Nat.succ_pos _⟩
      let tail : Fin n → Set ℝ := fun i => cell i.succ
      have htaildisj : Set.PairwiseDisjoint Set.univ tail := by
        intro i hi j hj hij
        exact hdisj (Set.mem_univ i.succ) (Set.mem_univ j.succ)
          (fun h => hij (Fin.succ_injective h))
      have hheadtail : Disjoint (cell i0) (⋃ i, tail i) := by
        rw [Set.disjoint_iUnion_right]
        intro i
        exact hdisj (Set.mem_univ i0) (Set.mem_univ i.succ) (by simp [i0])
      rw [show (⋃ i : Fin (n + 1), cell i) = cell i0 ∪ ⋃ i : Fin n, tail i by
        ext x
        simp [i0, tail, Fin.exists_fin_succ]]
      rw [P.proj_union (hcell i0) (MeasurableSet.iUnion fun i => hcell i.succ) hheadtail]
      simp [i0, tail, Fin.sum_univ_succ]
      exact congrArg (fun T => P.proj (cell i0) (hcell i0) + T) ih

/-- Left multiplication by a spectral block selects its own coefficient from a
finite spectral step. -/
theorem spectralProjection_select_left
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A)
    {n : ℕ} (cell : Fin n → Set ℝ)
    (hcell : ∀ i, MeasurableSet (cell i))
    (rep : Fin n → ℂ)
    (hdisj : Set.PairwiseDisjoint Set.univ cell) (i : Fin n) :
    boundedSelfAdjointSpectralProjection A hA (cell i) (hcell i) ∘L
      (∑ j, rep j • boundedSelfAdjointSpectralProjection A hA (cell j) (hcell j)) =
      rep i • boundedSelfAdjointSpectralProjection A hA (cell i) (hcell i) := by
  rw [ContinuousLinearMap.comp_finset_sum]
  apply Finset.sum_eq_single i
  · intro j hj hji
    rw [ContinuousLinearMap.comp_smul,
      spectralProjection_pairwise_orthogonal A hA cell hcell hdisj i j hji]
    simp
  · intro hi
    exact absurd (Finset.mem_univ i) hi
  · rw [ContinuousLinearMap.comp_smul]
    let P := boundedSelfAdjointSpectralPVM A hA
    change rep i • (P.proj (cell i) (hcell i) * P.proj (cell i) (hcell i)) = _
    rw [P.proj_idem]

/-- Right multiplication by a spectral block selects its own coefficient. -/
theorem spectralProjection_select_right
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A)
    {n : ℕ} (cell : Fin n → Set ℝ)
    (hcell : ∀ i, MeasurableSet (cell i))
    (rep : Fin n → ℂ)
    (hdisj : Set.PairwiseDisjoint Set.univ cell) (i : Fin n) :
    (∑ j, rep j • boundedSelfAdjointSpectralProjection A hA (cell j) (hcell j)) ∘L
      boundedSelfAdjointSpectralProjection A hA (cell i) (hcell i) =
      rep i • boundedSelfAdjointSpectralProjection A hA (cell i) (hcell i) := by
  rw [ContinuousLinearMap.finset_sum_comp]
  apply Finset.sum_eq_single i
  · intro j hj hji
    rw [ContinuousLinearMap.smul_comp]
    have hzero := spectralProjection_pairwise_orthogonal A hA cell hcell hdisj j i hji
    rw [hzero]
    simp
  · intro hi
    exact absurd (Finset.mem_univ i) hi
  · rw [ContinuousLinearMap.smul_comp]
    let P := boundedSelfAdjointSpectralPVM A hA
    change rep i • (P.proj (cell i) (hcell i) * P.proj (cell i) (hcell i)) = _
    rw [P.proj_idem]

/-- The choice-based real step symbol used by the original finite-step file. -/
noncomputable def chosenFiniteStepSymbol {n : ℕ}
    (cell : Fin n → Set ℝ) (rep : Fin n → ℝ) (x : ℝ) : ℝ :=
  if hx : ∃ i, x ∈ cell i then rep (Classical.choose hx) else x

/-- On a pairwise disjoint cover, the choice-based step symbol equals the
finite indicator sum at every covered point. -/
theorem chosenFiniteStepSymbol_eq {n : ℕ}
    (cell : Fin n → Set ℝ) (rep : Fin n → ℝ)
    (hdisj : Set.PairwiseDisjoint Set.univ cell)
    {x : ℝ} (hcover : x ∈ ⋃ i, cell i) :
    ((chosenFiniteStepSymbol cell rep x : ℝ) : ℂ) =
      finiteStepSymbol cell rep x := by
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hcover
  have hex : ∃ j, x ∈ cell j := ⟨i, hxi⟩
  let j := Classical.choose hex
  have hxj : x ∈ cell j := Classical.choose_spec hex
  have hji : j = i := by
    by_contra hne
    exact Set.disjoint_left.mp
      (hdisj (Set.mem_univ j) (Set.mem_univ i) hne) hxj hxi
  subst j
  rw [chosenFiniteStepSymbol, dif_pos hex, finiteStepSymbol]
  rw [Finset.sum_eq_single i]
  · rw [Set.indicator_of_mem hxi]
  · intro k hk hki
    have hxk : x ∉ cell k := by
      intro hxk
      exact Set.disjoint_left.mp
        (hdisj (Set.mem_univ k) (Set.mem_univ i) hki) hxk hxi
    rw [Set.indicator_of_notMem hxk]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- The exact finite-step Borel identity required by the Sylvester file. -/
theorem boundedSelfAdjointBorelCalculus_eq_finset_sum_indicator [Nontrivial H]
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A)
    {n : ℕ} (cell : Fin n → Set ℝ)
    (hcell : ∀ i, MeasurableSet (cell i))
    (hdisj : Set.PairwiseDisjoint Set.univ cell)
    (rep : Fin n → ℝ)
    (hcover : realSpectrum A ⊆ ⋃ i, cell i) :
    boundedSelfAdjointBorelCalculus A hA
      (chosenFiniteStepSymbol cell rep)
      (by
        classical
        apply Measurable.dite
        · exact measurableSet_iUnion fun i => hcell i
        · intro x hx
          exact measurable_const
        · intro x hx
          exact measurable_id)
      (by
        refine ⟨∑ i, |rep i|, Finset.sum_nonneg fun i _ => abs_nonneg _, fun x hx => ?_⟩
        have hcov := hcover hx
        obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hcov
        have hex : ∃ j, x ∈ cell j := ⟨i, hxi⟩
        rw [chosenFiniteStepSymbol, dif_pos hex]
        exact Finset.single_le_sum (fun j _ => abs_nonneg (rep j)) (Finset.mem_univ _)) =
      ∑ i, (rep i : ℂ) •
        boundedSelfAdjointSpectralProjection A hA (cell i) (hcell i) := by
  classical
  have hbounded : BoundedOnSpectrum A (chosenFiniteStepSymbol cell rep) := by
    refine ⟨∑ i, |rep i|, Finset.sum_nonneg fun i _ => abs_nonneg _, fun x hx => ?_⟩
    have hcov := hcover hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hcov
    have hex : ∃ j, x ∈ cell j := ⟨i, hxi⟩
    rw [chosenFiniteStepSymbol, dif_pos hex]
    exact Finset.single_le_sum (fun j _ => abs_nonneg (rep j)) (Finset.mem_univ _)
  unfold boundedSelfAdjointBorelCalculus
  have hcongr : boundedSelfAdjointBorelCalculusC A hA
      (spectrumRestrictedSymbol A (chosenFiniteStepSymbol cell rep))
      _ _ =
      boundedSelfAdjointBorelCalculusC A hA
        (finiteStepSymbol cell rep)
        (measurable_finiteStepSymbol cell hcell rep)
        (bounded_finiteStepSymbol cell rep) := by
    apply boundedSelfAdjointBorelCalculusC_congr_on_spectrum A hA
    intro x hx
    rw [spectrumRestrictedSymbol, Set.indicator_of_mem hx]
    exact chosenFiniteStepSymbol_eq cell rep hdisj (hcover hx)
  rw [hcongr, boundedSelfAdjointBorelCalculusC_finiteStep A hA cell hcell rep]

end
end DavisKahanExt
end ForMathlib

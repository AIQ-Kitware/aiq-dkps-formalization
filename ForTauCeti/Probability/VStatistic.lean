/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5

Staged for Tau Ceti, roadmap topic T14.  Mathlib is not the destination
(`ForTauCeti/README.md`); what follows is where this material would have gone on
the closed Mathlib track — additions to `Mathlib/Probability/`.

Formalized by Claude Opus 5 (claude-opus-5[1m]).
-/
module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod

/-! # Two-coordinate marginals of a product measure, and the mean of a V-statistic

A *V-statistic of order two* is a double average `(1/n²) ∑ᵢ ∑ⱼ f (X i) (X j)` over an
independent sample.  Averages of a function of one coordinate are covered by the law of large
numbers; a double average is not, because the summands share coordinates, and the classical
routes — Hoeffding's decomposition, or Varadarajan's theorem on almost-sure weak convergence of
empirical measures — are both absent from Mathlib.

This file supplies the first piece: under a product measure the pair of two *distinct*
coordinates has the product law, so the expectation of a V-statistic splits into its
off-diagonal and diagonal parts,

  `∫ ∑ᵢ ∑ⱼ f (ω i) (ω j) = n (n - 1) ∫∫ f + n ∫ f x x`.

That identity is what an elementary second-moment proof of the weak law for V-statistics starts
from.
-/

public section

namespace TauCeti

open MeasureTheory ProbabilityTheory

variable {ι : Type*} [Fintype ι] {α : Type*} [MeasurableSpace α]

/-- Under a product of probability measures, two **distinct** coordinates are jointly
distributed as the product measure. -/
theorem map_evalPair_pi (P : Measure α) [IsProbabilityMeasure P] {i j : ι} (hij : i ≠ j) :
    (Measure.pi (fun _ : ι => P)).map (fun ω : ι → α => (ω i, ω j)) = P.prod P := by
  have hindep : IndepFun (fun ω : ι → α => ω i) (fun ω : ι → α => ω j)
      (Measure.pi (fun _ : ι => P)) :=
    (iIndepFun_pi (X := fun _ : ι => (id : α → α)) fun _ => aemeasurable_id).indepFun hij
  have hmap : ∀ k : ι,
      (Measure.pi (fun _ : ι => P)).map (fun ω : ι → α => ω k) = P :=
    fun k => (measurePreserving_eval (fun _ : ι => P) k).map_eq
  rw [(indepFun_iff_map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable).mp hindep,
    hmap i, hmap j]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [Fintype ι] in
/-- Integrating a function of two distinct coordinates is integrating against the product
measure. -/
theorem integral_evalPair_pi [Fintype ι] (P : Measure α) [IsProbabilityMeasure P]
    {i j : ι} (hij : i ≠ j) {f : α × α → E} (hf : AEStronglyMeasurable f (P.prod P)) :
    ∫ ω, f (ω i, ω j) ∂(Measure.pi (fun _ : ι => P)) = ∫ q, f q ∂(P.prod P) := by
  rw [← map_evalPair_pi (ι := ι) P hij,
    integral_map ((measurable_pi_apply i).prodMk (measurable_pi_apply j)).aemeasurable
      (by rwa [map_evalPair_pi (ι := ι) P hij])]

omit [Fintype ι] [NormedSpace ℝ E] in
/-- A function of two distinct coordinates is integrable exactly when it is integrable against
the product measure. -/
theorem integrable_evalPair_pi [Fintype ι] (P : Measure α) [IsProbabilityMeasure P]
    {i j : ι} (hij : i ≠ j) {f : α × α → E} (hf : Integrable f (P.prod P)) :
    Integrable (fun ω : ι → α => f (ω i, ω j)) (Measure.pi (fun _ : ι => P)) := by
  have hf' : Integrable f
      ((Measure.pi (fun _ : ι => P)).map (fun ω : ι → α => (ω i, ω j))) := by
    rwa [map_evalPair_pi (ι := ι) P hij]
  exact (integrable_map_measure hf'.aestronglyMeasurable
    ((measurable_pi_apply i).prodMk (measurable_pi_apply j)).aemeasurable).mp hf'

/-- Integrating a function of a single coordinate is integrating against the base measure. -/
theorem integral_eval_pi (P : Measure α) [IsProbabilityMeasure P] (i : ι) {g : α → E}
    (hg : AEStronglyMeasurable g P) :
    ∫ ω, g (ω i) ∂(Measure.pi (fun _ : ι => P)) = ∫ x, g x ∂P := by
  have hmap := (measurePreserving_eval (fun _ : ι => P) i).map_eq
  have hg' : AEStronglyMeasurable g
      ((Measure.pi (fun _ : ι => P)).map (fun ω : ι → α => ω i)) := by rwa [hmap]
  conv_rhs => rw [← hmap]
  rw [integral_map (measurable_pi_apply i).aemeasurable hg']

omit [Fintype ι] [NormedSpace ℝ E] in
/-- A function of a single coordinate is integrable exactly when it is integrable against the
base measure. -/
theorem integrable_eval_pi [Fintype ι] (P : Measure α) [IsProbabilityMeasure P] (i : ι) {g : α → E}
    (hg : Integrable g P) :
    Integrable (fun ω : ι → α => g (ω i)) (Measure.pi (fun _ : ι => P)) := by
  have hmap := (measurePreserving_eval (fun _ : ι => P) i).map_eq
  have hg' : Integrable g ((Measure.pi (fun _ : ι => P)).map (fun ω : ι → α => ω i)) := by
    rwa [hmap]
  exact (integrable_map_measure hg'.aestronglyMeasurable
    (measurable_pi_apply i).aemeasurable).mp hg'

/--
**The mean of a V-statistic of order two.**

Under a product of `n` copies of `P`, the double sum splits into `n (n - 1)` off-diagonal terms,
each distributed as the product measure, and `n` diagonal terms, each distributed as `P`.
-/
theorem integral_doubleSum_pi {n : ℕ} (P : Measure α) [IsProbabilityMeasure P]
    {f : α → α → ℝ} (hf : Integrable (Function.uncurry f) (P.prod P))
    (hdiag : Integrable (fun x => f x x) P) :
    ∫ ω, (∑ i : Fin n, ∑ j : Fin n, f (ω i) (ω j))
        ∂(Measure.pi (fun _ : Fin n => P))
      = ((n : ℝ) * ((n : ℝ) - 1)) * (∫ q, Function.uncurry f q ∂(P.prod P))
        + (n : ℝ) * ∫ x, f x x ∂P := by
  classical
  set A : ℝ := ∫ x, f x x ∂P with hA
  set B : ℝ := ∫ q, Function.uncurry f q ∂(P.prod P) with hB
  have hterm : ∀ i j : Fin n,
      Integrable (fun ω : Fin n → α => f (ω i) (ω j)) (Measure.pi (fun _ : Fin n => P)) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      exact integrable_eval_pi (ι := Fin n) P i hdiag
    · exact integrable_evalPair_pi (ι := Fin n) P hij hf
  have hval : ∀ i j : Fin n,
      ∫ ω, f (ω i) (ω j) ∂(Measure.pi (fun _ : Fin n => P))
        = if i = j then A else B := by
    intro i j
    by_cases hij : i = j
    · subst hij
      simp only [hA]
      exact integral_eval_pi (ι := Fin n) P i hdiag.aestronglyMeasurable
    · simp only [hij, reduceIte, hB]
      exact integral_evalPair_pi (ι := Fin n) P hij hf.aestronglyMeasurable
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hterm i j)]
  have hstep : ∀ i : Fin n,
      ∫ ω, (∑ j : Fin n, f (ω i) (ω j)) ∂(Measure.pi (fun _ : Fin n => P))
        = ((n : ℝ) - 1) * B + A := by
    intro i
    rw [integral_finsetSum _ (fun j _ => hterm i j)]
    have hsplit : ∀ j : Fin n,
        (∫ ω, f (ω i) (ω j) ∂(Measure.pi (fun _ : Fin n => P)))
          = B + (if i = j then A - B else 0) := by
      intro j
      rw [hval i j]
      by_cases h : i = j <;> simp [h]
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Finset.sum_ite_eq Finset.univ i (fun _ => A - B)]
    simp only [Finset.mem_univ, reduceIte, nsmul_eq_mul]
    ring
  simp_rw [hstep]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end TauCeti

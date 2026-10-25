/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6.1 Sol
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.RealMatchingAttainment
public import ForTauCeti.Analysis.InnerProductSpace.SchattenExponentContinuity

/-!
# Continuous matching values and the real nuclear endpoint

A fixed compact scalar interval defines the positive pair value without
choosing an exponent-dependent optimizer. Compact-minimum continuity
therefore applies even at zero chords and changing phases. On `1<p<2`
this equals the proved clipped pair formula; at one it equals the closed
nuclear pair weight. Finite matching minima inherit exponent continuity.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.RealTransport

open SchattenPhaseTransition
open Set

/-- Variational positive-class pair weight on a fixed compact interval. -/
def realVariationalPairWeight (p theta psi : ℝ) : ℝ :=
  let h := (max theta psi + min theta psi)/2
  let d := (max theta psi - min theta psi)/2
  sInf (fourEdgeCost (fun s => s^p) h '' Icc d h)

/-- Compact pair minima vary continuously at every positive exponent. -/
theorem continuousOn_realVariationalPairWeight (theta psi : ℝ) :
    ContinuousOn (fun p => realVariationalPairWeight p theta psi) (Ioi 0) := by
  rw [continuousOn_iff_continuous_domRestrict]
  apply isCompact_Icc.continuous_sInf
  unfold fourEdgeCost fourPhasePenalty
  apply continuous_const.mul
  apply Continuous.add
  · apply Continuous.rpow (by fun_prop) (continuous_subtype_val.comp continuous_fst)
    intro x
    exact Or.inr x.1.property
  · apply Continuous.rpow (by fun_prop) (continuous_subtype_val.comp continuous_fst)
    intro x
    exact Or.inr x.1.property

private theorem ordered_pair_parameters (theta psi : ℝ)
    (htheta : theta ∈ Icc 0 (Real.pi/2)) (hpsi : psi ∈ Icc 0 (Real.pi/2)) :
    let h := (max theta psi + min theta psi)/2
    let d := (max theta psi - min theta psi)/2
    0 ≤ d ∧ d ≤ h ∧ h+d ≤ Real.pi/2 := by
  dsimp only
  have hle : min theta psi ≤ max theta psi := min_le_max
  have hmin : 0 ≤ min theta psi := le_min htheta.1 hpsi.1
  have hmax : max theta psi ≤ Real.pi/2 := max_le htheta.2 hpsi.2
  constructor
  · linarith
  constructor <;> linarith

/-- Identification with the exact positive Schatten pair formula. -/
theorem realVariationalPairWeight_eq_positive
    (p theta psi : ℝ) (hp1 : 1 < p) (hp2 : p < 2)
    (htheta : theta ∈ Icc 0 (Real.pi/2)) (hpsi : psi ∈ Icc 0 (Real.pi/2)) :
    realVariationalPairWeight p theta psi = realPositiveSchattenPairWeight p theta psi := by
  let h := (max theta psi + min theta psi)/2
  let d := (max theta psi - min theta psi)/2
  obtain ⟨hd, hdh, hhd⟩ := ordered_pair_parameters theta psi htheta hpsi
  have hh : h ≤ Real.pi/2 := by
    change 0 ≤ d at hd
    change h+d ≤ Real.pi/2 at hhd
    linarith
  have hopt := (optimalPhase_spec p h hp1.le (hd.trans hdh)).1.2
  have hclip : max d (optimalPhase p h) ∈ Icc d h :=
    ⟨le_max_left _ _, max_le hdh hopt⟩
  have hmin := (phasePower_isMinOn_truncated_iff p h d _ hp1 hp2 hd hdh hh hclip).mpr rfl
  have heq : realVariationalPairWeight p theta psi =
      fourEdgeCost (fun s => s^p) h (max d (optimalPhase p h)) := by
    apply IsLeast.csInf_eq
    refine ⟨mem_image_of_mem _ hclip, ?_⟩
    rintro _ ⟨delta, hdelta, rfl⟩
    rw [four_schatten_edgeCost p h _ hh ⟨hd.trans hclip.1, hclip.2⟩,
      four_schatten_edgeCost p h _ hh ⟨hd.trans hdelta.1, hdelta.2⟩]
    exact mul_le_mul_of_nonneg_left (hmin hdelta) (by norm_num)
  rw [heq, four_schatten_edgeCost p h _ hh ⟨hd.trans hclip.1, hclip.2⟩]
  rfl

/-- The nuclear positive pair cost, including zero and right endpoints. -/
theorem realVariationalPairWeight_one (theta psi : ℝ)
    (htheta : theta ∈ Icc 0 (Real.pi/2)) (hpsi : psi ∈ Icc 0 (Real.pi/2)) :
    realVariationalPairWeight 1 theta psi = 4 * Real.sin ((theta+psi)/2) := by
  let h := (max theta psi + min theta psi)/2
  let d := (max theta psi - min theta psi)/2
  obtain ⟨hd, hdh, hhd⟩ := ordered_pair_parameters theta psi htheta hpsi
  obtain ⟨hvalue, hmin⟩ := four_nuclear_edge_minimum h d hd hdh hhd
  have hfun : fourEdgeCost (fun s : ℝ => s^((1 : ℝ))) h = fourEdgeCost id h := by
    funext delta
    simp only [fourEdgeCost, fourPhasePenalty, Real.rpow_one, id_eq]
  change sInf (fourEdgeCost (fun s : ℝ => s^((1 : ℝ))) h '' Icc d h) = _
  rw [hfun]
  have heq : sInf (fourEdgeCost id h '' Icc d h) = fourEdgeCost id h h := by
    apply IsLeast.csInf_eq
    refine ⟨mem_image_of_mem _ ⟨hdh, le_rfl⟩, ?_⟩
    rintro _ ⟨delta, hdelta, rfl⟩
    exact hmin hdelta
  rw [heq, hvalue]
  simp only [h, max_add_min]

variable {ι : Type*} [Fintype ι]

/-- Matching cost with variational positive pair weights. -/
def realVariationalMatchingCost (p : ℝ) (theta : ι → ℝ) (s : Equiv.Perm ι) : ℝ := by
  classical
  exact ∑ i, if s i = i then realSingleSchattenCost p (theta i)
    else realVariationalPairWeight p (theta i) (theta (s i))/2

/-- The finite variational matching minimum. -/
def realVariationalMatchingMinimum (p : ℝ) (theta : ι → ℝ) : ℝ :=
  (realSchattenMatchings ι).inf' (realSchattenMatchings_nonempty ι)
    (realVariationalMatchingCost p theta)

/-- Closed positive-class nuclear cost for a pair of principal angles. -/
@[expose]
def realNuclearPairWeight (theta psi : ℝ) : ℝ :=
  4 * Real.sin ((theta+psi)/2)

theorem realNuclearPairWeight_comm (theta psi : ℝ) :
    realNuclearPairWeight theta psi = realNuclearPairWeight psi theta := by
  simp only [realNuclearPairWeight, add_comm]

/-- Literal closed real nuclear matching cost. Fixed vertices use the
one-angle canonical/reflection minimum; edges use `4*sin((theta+psi)/2)`. -/
def realNuclearMatchingCost (theta : ι → ℝ) (s : Equiv.Perm ι) : ℝ := by
  classical
  exact ∑ i, if s i = i then min (4*Real.sin (theta i/2)) 2
    else realNuclearPairWeight (theta i) (theta (s i))/2

/-- The closed finite nuclear matching problem on a labelled angle list. -/
def realNuclearMatchingMinimum (theta : ι → ℝ) : ℝ :=
  (realSchattenMatchings ι).inf' (realSchattenMatchings_nonempty ι)
    (realNuclearMatchingCost theta)

/-- Finite matching values are continuous across all positive exponents,
including the nuclear endpoint. -/
theorem continuousOn_realVariationalMatchingMinimum (theta : ι → ℝ) :
    ContinuousOn (fun p => realVariationalMatchingMinimum p theta) (Ioi 0) := by
  classical
  apply ContinuousOn.finset_inf'_apply
  intro s _
  apply continuousOn_finsetSum
  intro i _
  by_cases hfix : s i = i
  · simp only [ite_eq_left hfix]
    change ContinuousOn (fun p => min (2 * phaseChord (theta i)^p) ((2 : ℝ)^p)) (Ioi 0)
    have hpow (a : ℝ) : ContinuousOn (fun p : ℝ => a^p) (Ioi 0) :=
      continuousOn_const.rpow continuousOn_id (fun _ hp => Or.inr hp)
    exact (continuousOn_const.mul (hpow _)).inf (hpow _)
  · simpa only [ite_eq_right hfix] using
      (continuousOn_realVariationalPairWeight (theta i) (theta (s i))).div_const 2

/-- Identification with the proved positive-edge Schatten matching cost. -/
theorem realVariationalMatchingCost_eq_positive
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (theta : ι → ℝ)
    (htheta : ∀ i, theta i ∈ Icc 0 (Real.pi/2)) (s : Equiv.Perm ι) :
    realVariationalMatchingCost p theta s = realPositiveSchattenMatchingCost p theta s := by
  classical
  unfold realVariationalMatchingCost realPositiveSchattenMatchingCost
  apply Finset.sum_congr rfl
  intro i _
  rw [realVariationalPairWeight_eq_positive p _ _ hp1 hp2 (htheta i) (htheta (s i))]

/-- Identification of the finite matching minima for `1<p<2`. -/
theorem realVariationalMatchingMinimum_eq_positive
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (theta : ι → ℝ)
    (htheta : ∀ i, theta i ∈ Icc 0 (Real.pi/2)) :
    realVariationalMatchingMinimum p theta = realPositiveSchattenMatchingMinimum p theta := by
  unfold realVariationalMatchingMinimum realPositiveSchattenMatchingMinimum
  congr 1
  funext s
  exact realVariationalMatchingCost_eq_positive p hp1 hp2 theta htheta s

/-- At one, the continuous matching family is the closed nuclear formula. -/
theorem realVariationalMatchingMinimum_one (theta : ι → ℝ)
    (htheta : ∀ i, theta i ∈ Icc 0 (Real.pi/2)) :
    realVariationalMatchingMinimum 1 theta = realNuclearMatchingMinimum theta := by
  have hcost (s : Equiv.Perm ι) :
      realVariationalMatchingCost 1 theta s = realNuclearMatchingCost theta s := by
    classical
    unfold realVariationalMatchingCost realNuclearMatchingCost
    apply Finset.sum_congr rfl
    intro i _
    rw [realVariationalPairWeight_one _ _ (htheta i) (htheta (s i))]
    norm_num [realSingleSchattenCost, phaseChord, realNuclearPairWeight, ← mul_assoc]
  unfold realVariationalMatchingMinimum realNuclearMatchingMinimum
  congr 1
  exact funext hcost

/-- The original clipped Schatten pair formula has the exact nuclear
endpoint, without introducing a different optimizer choice at one. -/
theorem realPositiveSchattenPairWeight_one (theta psi : ℝ)
    (htheta : theta ∈ Icc 0 (Real.pi/2)) (hpsi : psi ∈ Icc 0 (Real.pi/2)) :
    realPositiveSchattenPairWeight 1 theta psi = realNuclearPairWeight theta psi := by
  let h := (max theta psi + min theta psi)/2
  let d := (max theta psi - min theta psi)/2
  obtain ⟨hd, hdh, hhd⟩ := ordered_pair_parameters theta psi htheta hpsi
  have h0 : 0 ≤ h := hd.trans hdh
  have hpi : h ≤ Real.pi/2 := by
    change 0 ≤ d at hd
    change h+d ≤ Real.pi/2 at hhd
    linarith
  change 2 * phasePower 1 h (max d (optimalPhase 1 h)) = _
  rw [optimalPhase_one h h0 hpi, max_eq_right hdh]
  simp only [phasePower, Real.rpow_one, phaseChord]
  dsimp only [realNuclearPairWeight, h]
  rw [max_add_min]
  ring_nf
  simp

/-- The original positive-edge Schatten matching minimum includes the
nuclear exponent with exactly its closed sine weights. -/
theorem realPositiveSchattenMatchingMinimum_one (theta : ι → ℝ)
    (htheta : ∀ i, theta i ∈ Icc 0 (Real.pi/2)) :
    realPositiveSchattenMatchingMinimum 1 theta = realNuclearMatchingMinimum theta := by
  have hcost (s : Equiv.Perm ι) :
      realPositiveSchattenMatchingCost 1 theta s = realNuclearMatchingCost theta s := by
    classical
    unfold realPositiveSchattenMatchingCost realNuclearMatchingCost
    apply Finset.sum_congr rfl
    intro i _
    rw [realPositiveSchattenPairWeight_one _ _ (htheta i) (htheta (s i))]
    norm_num [realSingleSchattenCost, phaseChord, ← mul_assoc]
  unfold realPositiveSchattenMatchingMinimum realNuclearMatchingMinimum
  congr 1
  exact funext hcost

end TauCeti.DavisKahan.FiniteDimensional.RealTransport

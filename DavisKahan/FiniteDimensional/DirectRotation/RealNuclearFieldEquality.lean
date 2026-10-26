/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.RealNuclearOptimality
public import ForTauCeti.Data.Fintype.Involution
public import Mathlib.Logic.Equiv.Sum

/-!
# Equality in the real nuclear spectral lower bound

Each unmatched nuclear angle dominates `2 sin(theta)`, with equality only
at zero and right angles. A coupled pair dominates the sum of those
values, with equality exactly for equal angles. Thus equality in a
labelled matching requires an angle-preserving involution without fixed
points on the strictly acute positive levels.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.RealTransport

open Set
open scoped BigOperators

/-- The complex nuclear spectral value bounds the real canonical cost. -/
theorem nuclear_sine_le_canonical (theta : ℝ)
    (htheta : theta ∈ Icc 0 (Real.pi/2)) :
    2 * Real.sin theta ≤ 4 * Real.sin (theta/2) := by
  have hs : 0 ≤ Real.sin (theta/2) := Real.sin_nonneg_of_nonneg_of_le_pi
    (by linarith [htheta.1]) (by linarith [htheta.2, Real.pi_pos])
  have hid : 2 * Real.sin theta = 4 * Real.sin (theta/2) * Real.cos (theta/2) := by
    conv_lhs => rw [show theta = 2*(theta/2) by ring, Real.sin_two_mul]
    ring
  rw [hid]
  nlinarith [Real.cos_le_one (theta/2)]

/-- The canonical nuclear cost strictly exceeds the sine value at every
positive physical angle. -/
theorem nuclear_sine_lt_canonical (theta : ℝ) (htheta : 0 < theta)
    (hpi : theta ≤ Real.pi/2) :
    2 * Real.sin theta < 4 * Real.sin (theta/2) := by
  have hs : 0 < Real.sin (theta/2) := Real.sin_pos_of_pos_of_lt_pi
    (by linarith) (by linarith [Real.pi_pos])
  have hc := Real.cos_lt_cos_of_nonneg_of_le_pi (x := 0) (y := theta/2)
    le_rfl (by linarith [Real.pi_pos]) (by linarith)
  rw [Real.cos_zero] at hc
  have hid : 2 * Real.sin theta = 4 * Real.sin (theta/2) * Real.cos (theta/2) := by
    conv_lhs => rw [show theta = 2*(theta/2) by ring, Real.sin_two_mul]
    ring
  rw [hid]
  nlinarith

/-- Every real nuclear singleton dominates the complex sine value. -/
theorem nuclear_sine_le_singleton (theta : ℝ)
    (htheta : theta ∈ Icc 0 (Real.pi/2)) :
    2 * Real.sin theta ≤ min (4 * Real.sin (theta/2)) 2 :=
  le_min (nuclear_sine_le_canonical theta htheta) (by linarith [Real.sin_le_one theta])

/-- A nuclear singleton has zero field penalty only at zero or a right
angle, including both endpoints. -/
theorem nuclear_singleton_eq_sine_iff (theta : ℝ)
    (htheta : theta ∈ Icc 0 (Real.pi/2)) :
    min (4 * Real.sin (theta/2)) 2 = 2 * Real.sin theta ↔
      theta = 0 ∨ theta = Real.pi/2 := by
  constructor
  · intro heq
    by_contra h
    push Not at h
    have ht : 0 < theta := lt_of_le_of_ne htheta.1 (Ne.symm h.1)
    have hp : theta < Real.pi/2 := lt_of_le_of_ne htheta.2 h.2
    have hs := Real.strictMonoOn_sin
      (show theta ∈ Icc (-(Real.pi/2)) (Real.pi/2) from
        ⟨by linarith [Real.pi_pos], htheta.2⟩)
      (show Real.pi/2 ∈ Icc (-(Real.pi/2)) (Real.pi/2) from
        ⟨by linarith [Real.pi_pos], le_rfl⟩) hp
    rw [Real.sin_pi_div_two] at hs
    have hstrict := lt_min (nuclear_sine_lt_canonical theta ht htheta.2)
      (show 2 * Real.sin theta < 2 by linarith)
    rw [heq] at hstrict
    exact (lt_irrefl _) hstrict
  · rintro (rfl | rfl)
    · norm_num
    · apply le_antisymm
      · simpa only [Real.sin_pi_div_two, mul_one] using
          (min_le_right (4 * Real.sin (Real.pi/2/2)) (2 : ℝ))
      · exact nuclear_sine_le_singleton _ htheta

private theorem nuclear_sine_pair_sum (theta psi : ℝ) :
    2 * Real.sin theta + 2 * Real.sin psi =
      4 * Real.sin ((theta+psi)/2) * Real.cos ((theta-psi)/2) := by
  rw [← mul_add, Real.sin_add_sin]
  ring

/-- Every coupled nuclear pair dominates the two complex sine values. -/
theorem nuclear_sine_sum_le_pair (theta psi : ℝ)
    (htheta : theta ∈ Icc 0 (Real.pi/2)) (hpsi : psi ∈ Icc 0 (Real.pi/2)) :
    2 * Real.sin theta + 2 * Real.sin psi ≤ realNuclearPairWeight theta psi := by
  have hs : 0 ≤ Real.sin ((theta+psi)/2) := Real.sin_nonneg_of_nonneg_of_le_pi
    (by linarith [htheta.1, hpsi.1]) (by linarith [htheta.2, hpsi.2, Real.pi_pos])
  rw [nuclear_sine_pair_sum, realNuclearPairWeight]
  nlinarith [Real.cos_le_one ((theta-psi)/2)]

/-- A coupled nuclear pair has zero field penalty exactly when its two
angles agree. This includes repeated zero and right angles. -/
theorem nuclear_pair_eq_sine_sum_iff (theta psi : ℝ)
    (htheta : theta ∈ Icc 0 (Real.pi/2)) (hpsi : psi ∈ Icc 0 (Real.pi/2)) :
    realNuclearPairWeight theta psi = 2 * Real.sin theta + 2 * Real.sin psi ↔
      theta = psi := by
  constructor
  · intro heq
    by_contra hne
    have hh : 0 < (theta+psi)/2 := by
      rcases lt_or_gt_of_ne hne with h | h <;> linarith [htheta.1, hpsi.1]
    have hs : 0 < Real.sin ((theta+psi)/2) := Real.sin_pos_of_pos_of_lt_pi hh
      (by linarith [htheta.2, hpsi.2, Real.pi_pos])
    have hd : 0 < |(theta-psi)/2| := abs_pos.mpr (by intro h; apply hne; linarith)
    have hdp : |(theta-psi)/2| ≤ Real.pi := abs_le.mpr
      ⟨by linarith [htheta.1, hpsi.2, Real.pi_pos],
        by linarith [htheta.2, hpsi.1, Real.pi_pos]⟩
    have hc := Real.cos_lt_cos_of_nonneg_of_le_pi (x := 0) le_rfl hdp hd
    rw [Real.cos_zero, Real.cos_abs] at hc
    rw [nuclear_sine_pair_sum, realNuclearPairWeight] at heq
    nlinarith
  · intro heq
    subst psi
    simp only [realNuclearPairWeight, show (theta+theta)/2 = theta by ring]
    ring

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
private theorem nuclear_matching_vertex_bound [DecidableEq ι] (theta : ι → ℝ)
    (htheta : ∀ i, theta i ∈ Icc 0 (Real.pi/2)) (s : Equiv.Perm ι) (i : ι) :
    (2 * Real.sin (theta i) + 2 * Real.sin (theta (s i)))/2 ≤
      if s i = i then min (4 * Real.sin (theta i/2)) 2
        else realNuclearPairWeight (theta i) (theta (s i))/2 := by
  classical
  by_cases hfix : s i = i
  · simpa only [hfix, ite_true, add_self_div_two] using
      nuclear_sine_le_singleton _ (htheta i)
  · rw [ite_eq_right hfix]
    exact div_le_div_of_nonneg_right
      (nuclear_sine_sum_le_pair _ _ (htheta i) (htheta (s i))) (by norm_num)

private theorem nuclear_matching_sine_sum (theta : ι → ℝ) (s : Equiv.Perm ι) :
    (∑ i, (2 * Real.sin (theta i) + 2 * Real.sin (theta (s i)))/2) =
      ∑ i, 2 * Real.sin (theta i) := by
  rw [← Finset.sum_div, Finset.sum_add_distrib,
    Equiv.sum_comp s (fun i => 2 * Real.sin (theta i))]
  ring

/-- The complex sine value is a lower bound for every real labelled
matching, independently of whether the permutation is involutive. -/
theorem nuclear_sine_sum_le_matching (theta : ι → ℝ)
    (htheta : ∀ i, theta i ∈ Icc 0 (Real.pi/2)) (s : Equiv.Perm ι) :
    (∑ i, 2 * Real.sin (theta i)) ≤ realNuclearMatchingCost theta s := by
  classical
  rw [← nuclear_matching_sine_sum theta s]
  exact Finset.sum_le_sum (fun i _ => nuclear_matching_vertex_bound theta htheta s i)

/-- Equality in the nuclear matching lower bound requires preservation
of each angle level and forbids fixed points at strictly acute positive
angles. Conversely, these two conditions suffice. -/
theorem realNuclearMatchingCost_eq_sine_sum_iff (theta : ι → ℝ)
    (htheta : ∀ i, theta i ∈ Icc 0 (Real.pi/2)) (s : Equiv.Perm ι) :
    realNuclearMatchingCost theta s = (∑ i, 2 * Real.sin (theta i)) ↔
      (∀ i, theta (s i) = theta i) ∧
        (∀ i, 0 < theta i → theta i < Real.pi/2 → s i ≠ i) := by
  classical
  have hvertex := nuclear_matching_vertex_bound theta htheta s
  have hsum := nuclear_matching_sine_sum theta s
  constructor
  · intro heq
    have hpoint := (Finset.sum_eq_sum_iff_of_le
      (fun i (_ : i ∈ Finset.univ) => hvertex i)).mp
      (show (∑ i, (2 * Real.sin (theta i) + 2 * Real.sin (theta (s i)))/2) =
          realNuclearMatchingCost theta s from hsum.trans heq.symm)
    constructor
    · intro i
      by_cases hfix : s i = i
      · rw [hfix]
      · have hi := hpoint i (Finset.mem_univ i)
        rw [ite_eq_right hfix] at hi
        exact ((nuclear_pair_eq_sine_sum_iff _ _ (htheta i) (htheta (s i))).mp
          (by linarith)).symm
    · intro i hi0 hip hfix
      have hi := hpoint i (Finset.mem_univ i)
      rw [hfix, ite_eq_left rfl, add_self_div_two] at hi
      rcases (nuclear_singleton_eq_sine_iff _ (htheta i)).mp hi.symm with hz | hz
      · linarith
      · linarith
  · rintro ⟨hangle, hfree⟩
    rw [← hsum]
    unfold realNuclearMatchingCost
    apply Finset.sum_congr rfl
    intro i _
    by_cases hfix : s i = i
    · rw [ite_eq_left hfix, hfix, add_self_div_two]
      apply (nuclear_singleton_eq_sine_iff _ (htheta i)).mpr
      by_contra h
      push Not at h
      exact hfree i (lt_of_le_of_ne (htheta i).1 (Ne.symm h.1))
        (lt_of_le_of_ne (htheta i).2 h.2) hfix
    · rw [ite_eq_right hfix]
      rw [(nuclear_pair_eq_sine_sum_iff _ _ (htheta i) (htheta (s i))).mpr
        (hangle i).symm]

/-- Equality in the global nuclear matching lower bound is equivalent
to a pairing preserving every angle and fixing no strictly acute level. -/
theorem realNuclearMatchingMinimum_eq_sine_sum_iff_exists (theta : ι → ℝ)
    (htheta : ∀ i, theta i ∈ Icc 0 (Real.pi/2)) :
    realNuclearMatchingMinimum theta = (∑ i, 2 * Real.sin (theta i)) ↔
      ∃ s : Equiv.Perm ι, Function.Involutive s ∧
        (∀ i, theta (s i) = theta i) ∧
          (∀ i, 0 < theta i → theta i < Real.pi/2 → s i ≠ i) := by
  constructor
  · intro heq
    obtain ⟨s, hs, hcost⟩ := exists_attains_realNuclearMatchingMinimum theta
    exact ⟨s, hs, (realNuclearMatchingCost_eq_sine_sum_iff theta htheta s).mp
      (hcost.trans heq)⟩
  · rintro ⟨s, hs, hangle, hfree⟩
    apply le_antisymm
    · exact (realNuclearMatchingMinimum_le theta s hs).trans_eq
        ((realNuclearMatchingCost_eq_sine_sum_iff theta htheta s).mpr ⟨hangle, hfree⟩)
    · obtain ⟨t, _, hcost⟩ := exists_attains_realNuclearMatchingMinimum theta
      exact (nuclear_sine_sum_le_matching theta htheta t).trans_eq hcost

/-- A level-preserving pairing without acute fixed points exists exactly
when each strictly acute positive angle has even labelled multiplicity.
Zero and right-angle multiplicities have no parity restriction. -/
theorem exists_nuclear_equality_matching_iff_even_multiplicities (theta : ι → ℝ) :
    (∃ s : Equiv.Perm ι, Function.Involutive s ∧
      (∀ i, theta (s i) = theta i) ∧
        (∀ i, 0 < theta i → theta i < Real.pi/2 → s i ≠ i)) ↔
      ∀ t ∈ Ioo 0 (Real.pi/2), Even (Nat.card {i : ι // theta i = t}) := by
  classical
  constructor
  · rintro ⟨s, hs, hangle, hfree⟩ t ht
    let st := s.subtypePerm (p := fun i => theta i = t)
      (fun i => by rw [hangle i])
    have hst : Function.Involutive st := fun i => Subtype.ext (hs i.val)
    have hstfree (i : {i : ι // theta i = t}) : st i ≠ i := by
      intro heq
      exact hfree i.val (by rw [i.property]; exact ht.1)
        (by rw [i.property]; exact ht.2) (congrArg Subtype.val heq)
    simpa only [Nat.card_eq_fintype_card] using
      TauCeti.Fintype.even_card_of_fixedPointFree_involutive st hst hstfree
  · intro heven
    have hlocal (t : ℝ) :
        ∃ s : Equiv.Perm {i : ι // theta i = t}, Function.Involutive s ∧
          ∀ i, 0 < t → t < Real.pi/2 → s i ≠ i := by
      by_cases ht : t ∈ Ioo 0 (Real.pi/2)
      · obtain ⟨f, hf, hfree⟩ :=
          (TauCeti.Fintype.exists_fixedPointFree_involutive_iff_even_card
            (α := {i : ι // theta i = t})).mpr
              (by simpa only [Nat.card_eq_fintype_card] using heven t ht)
        exact ⟨hf.toPerm f, hf, fun i _ _ => hfree i⟩
      · exact ⟨Equiv.refl _, fun _ => rfl, fun _ h0 hp => False.elim (ht ⟨h0, hp⟩)⟩
    choose st hst hfree using hlocal
    let e := Equiv.sigmaFiberEquiv theta
    let S := Equiv.sigmaCongrRight st
    let s : Equiv.Perm ι := (e.symm.trans S).trans e
    have hS : Function.Involutive S := by
      rintro ⟨t, i⟩
      exact congrArg (Sigma.mk t) (hst t i)
    have hs : Function.Involutive s := by
      intro i
      change e (S (e.symm (e (S (e.symm i))))) = i
      rw [e.symm_apply_apply, hS, e.apply_symm_apply]
    have hsapply (i : ι) : s i = (st (theta i) ⟨i, rfl⟩).val := rfl
    refine ⟨s, hs, fun i => (st (theta i) ⟨i, rfl⟩).property, ?_⟩
    intro i h0 hp hfix
    exact hfree (theta i) ⟨i, rfl⟩ h0 hp
      (Subtype.ext ((hsapply i).symm.trans hfix))

/-- The real nuclear matching minimum attains the complex sine value if
and only if every strictly acute positive angle has even multiplicity.
The criterion includes every zero, repeated and right-angle case. -/
theorem realNuclearMatchingMinimum_eq_sine_sum_iff_even_multiplicities
    (theta : ι → ℝ) (htheta : ∀ i, theta i ∈ Icc 0 (Real.pi/2)) :
    realNuclearMatchingMinimum theta = (∑ i, 2 * Real.sin (theta i)) ↔
      ∀ t ∈ Ioo 0 (Real.pi/2), Even (Nat.card {i : ι // theta i = t}) := by
  rw [realNuclearMatchingMinimum_eq_sine_sum_iff_exists theta htheta,
    exists_nuclear_equality_matching_iff_even_multiplicities]

/-- An odd strictly acute angle level is exactly the obstruction to
attaining the sine lower bound, and forces a strictly positive gap. -/
theorem sine_sum_lt_realNuclearMatchingMinimum_iff_odd_multiplicity
    (theta : ι → ℝ) (htheta : ∀ i, theta i ∈ Icc 0 (Real.pi/2)) :
    (∑ i, 2 * Real.sin (theta i)) < realNuclearMatchingMinimum theta ↔
      ∃ t ∈ Ioo 0 (Real.pi/2), Odd (Nat.card {i : ι // theta i = t}) := by
  classical
  have hcriterion := realNuclearMatchingMinimum_eq_sine_sum_iff_even_multiplicities
    theta htheta
  constructor
  · intro hlt
    have hnot : ¬∀ t ∈ Ioo 0 (Real.pi/2), Even (Nat.card {i : ι // theta i = t}) := by
      intro h
      rw [hcriterion.mpr h] at hlt
      exact (lt_irrefl _) hlt
    push Not at hnot
    obtain ⟨t, ht, hn⟩ := hnot
    exact ⟨t, ht, Nat.not_even_iff_odd.mp hn⟩
  · rintro ⟨t, ht, hodd⟩
    have hne : realNuclearMatchingMinimum theta ≠ ∑ i, 2 * Real.sin (theta i) := by
      intro heq
      exact (Nat.not_even_iff_odd.mpr hodd) (hcriterion.mp heq t ht)
    obtain ⟨s, _, hcost⟩ := exists_attains_realNuclearMatchingMinimum theta
    exact lt_of_le_of_ne ((nuclear_sine_sum_le_matching theta htheta s).trans_eq hcost)
      (Ne.symm hne)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Equality in the unrestricted ambient real nuclear spectral lower
bound has an exact parity criterion on the original accepted angles.
Only strictly acute positive levels need even multiplicity. -/
theorem realTransportPowerMinimum_one_eq_sine_sum_iff_even_multiplicities
    (K L : Submodule ℝ E) (hKL : Module.finrank ℝ K = Module.finrank ℝ L) :
    realTransportPowerMinimum 1 K L =
        (∑ i : Fin (Module.finrank ℝ K), 2 * Real.sin (K.principalAngles L i)) ↔
      ∀ t ∈ Ioo 0 (Real.pi/2),
        Even (Nat.card {i : Fin (Module.finrank ℝ K) // K.principalAngles L i = t}) := by
  classical
  let theta : Fin (Module.finrank ℝ K) → ℝ := fun i => K.principalAngles L i
  let J := {i : Fin (Module.finrank ℝ K) // 0 < theta i}
  have htheta (i) : theta i ∈ Icc 0 (Real.pi/2) :=
    ⟨K.principalAngles_nonneg L i, K.principalAngles_le_pi_div_two L i⟩
  have hzero (i : {i // ¬0 < theta i}) : 2 * Real.sin (theta i.val) = 0 := by
    have hi : theta i.val = 0 := le_antisymm (le_of_not_gt i.property) (htheta i.val).1
    simp [hi]
  have hsum := Fintype.sum_subtype_add_sum_subtype (fun i => 0 < theta i)
    (fun i => 2 * Real.sin (theta i))
  rw [Finset.sum_eq_zero (fun i _ => hzero i), add_zero] at hsum
  have hcard (t : ℝ) (ht : 0 < t) :
      Nat.card {i : J // theta i.val = t} =
        Nat.card {i : Fin (Module.finrank ℝ K) // theta i = t} := by
    apply Nat.card_congr
    exact
      { toFun := fun i => ⟨i.val.val, i.property⟩
        invFun := fun i => ⟨⟨i.val, by rw [i.property]; exact ht⟩, i.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [realTransportPowerMinimum_one_eq_nuclearMatching K L hKL, ← hsum,
    realNuclearMatchingMinimum_eq_sine_sum_iff_even_multiplicities
      (fun i : J => theta i.val) (fun i => htheta i.val)]
  constructor
  · intro h t ht
    exact (hcard t ht.1) ▸ h t ht
  · intro h t ht
    exact (hcard t ht.1).symm ▸ h t ht

end TauCeti.DavisKahan.FiniteDimensional.RealTransport

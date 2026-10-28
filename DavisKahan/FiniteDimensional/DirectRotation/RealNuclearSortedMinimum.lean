/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.RealNuclearHeadNormalization
public import ForTauCeti.Combinatorics.Matching.WeightedFin

/-!
# Two adjacent sums for the real nuclear matching minimum

The leading-orbit exchange proves a lower bound for every involution, with
optional singletons. Adjacent pair constructions give the reverse inequality.
No perfect-matching assumption or strict ordering is imposed.

The sorting step uses classical exchange/finite induction. The transport
application and unresolved priority are recorded in the provenance note.
-/

public section
noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.RealTransport

open Set WeightedInvolution

/-- Adjacent pairs, with a scalar zero appended to an odd list. -/
@[expose] def nuclearAdjacentSum : {n : ℕ} → (Fin n → ℝ) → ℝ
  | 0, _ => 0
  | 1, theta => nuclearCanonicalCost (theta 0)
  | n + 2, theta => realNuclearPairWeight (theta 0) (theta 1) +
      nuclearAdjacentSum (fun i : Fin n => theta i.succ.succ)

/-- The two proposed sorted costs: no leading reflection, or one leading
reflection followed by adjacent pairs. The empty case is zero. -/
@[expose] def nuclearSortedMinimum : {n : ℕ} → (Fin n → ℝ) → ℝ
  | 0, _ => 0
  | n + 1, theta => min (nuclearAdjacentSum theta)
      (2 + nuclearAdjacentSum (fun i : Fin n => theta i.succ))

private theorem sorted_le_reflection {n : ℕ} (theta : Fin (n + 1) → ℝ) :
    nuclearSortedMinimum theta ≤
      2 + nuclearSortedMinimum (fun i : Fin n => theta i.succ) := by
  cases n with
  | zero => exact min_le_right _ _
  | succ n =>
    change min (realNuclearPairWeight (theta 0) (theta 1) +
        nuclearAdjacentSum (fun i : Fin n => theta i.succ.succ))
      (2 + nuclearAdjacentSum (fun i : Fin (n + 1) => theta i.succ)) ≤
      2 + min (nuclearAdjacentSum (fun i : Fin (n + 1) => theta i.succ))
        (2 + nuclearAdjacentSum (fun i : Fin n => theta i.succ.succ))
    rcases le_total
        (nuclearAdjacentSum (fun i : Fin (n + 1) => theta i.succ))
        (2 + nuclearAdjacentSum (fun i : Fin n => theta i.succ.succ)) with h | h
    · rw [min_eq_left h]
      exact min_le_right _ _
    · rw [min_eq_right h]
      have hmin := min_le_left
        (realNuclearPairWeight (theta 0) (theta 1) +
          nuclearAdjacentSum (fun i : Fin n => theta i.succ.succ))
        (2 + nuclearAdjacentSum (fun i : Fin (n + 1) => theta i.succ))
      linarith [realNuclearPairWeight_le_four (theta 0) (theta 1)]

private theorem sorted_le_pair {n : ℕ} (theta : Fin (n + 2) → ℝ)
    (htheta : ∀ i, theta i ∈ Icc 0 (Real.pi / 2)) (horder : Antitone theta) :
    nuclearSortedMinimum theta ≤ realNuclearPairWeight (theta 0) (theta 1) +
      nuclearSortedMinimum (fun i : Fin n => theta i.succ.succ) := by
  cases n with
  | zero => exact min_le_left _ _
  | succ n =>
    let a := theta 0
    let b := theta 1
    let d := theta ((0 : Fin (n + 1)).succ.succ)
    have hda : d ≤ a := horder (Fin.zero_le _)
    have hed : realNuclearPairWeight b d ≤ realNuclearPairWeight a b := by
      rw [realNuclearPairWeight_comm b d]
      exact realNuclearPairWeight_mono_left d a b
        (htheta _).1 hda (htheta 0).2 (htheta 1)
    change min (realNuclearPairWeight a b +
        nuclearAdjacentSum (fun i : Fin (n + 1) => theta i.succ.succ))
      (2 + (realNuclearPairWeight b d +
        nuclearAdjacentSum (fun i : Fin n => theta i.succ.succ.succ))) ≤
      realNuclearPairWeight a b +
        min (nuclearAdjacentSum (fun i : Fin (n + 1) => theta i.succ.succ))
          (2 + nuclearAdjacentSum (fun i : Fin n => theta i.succ.succ.succ))
    rcases le_total
        (nuclearAdjacentSum (fun i : Fin (n + 1) => theta i.succ.succ))
        (2 + nuclearAdjacentSum (fun i : Fin n => theta i.succ.succ.succ)) with h | h
    · rw [min_eq_left h]
      exact min_le_left _ _
    · rw [min_eq_right h]
      have hmin := min_le_right
        (realNuclearPairWeight a b +
          nuclearAdjacentSum (fun i : Fin (n + 1) => theta i.succ.succ))
        (2 + (realNuclearPairWeight b d +
          nuclearAdjacentSum (fun i : Fin n => theta i.succ.succ.succ)))
      linarith

/-- The two-sum value bounds every nuclear matching, not just perfect
matchings. The angle list is ordered, but zeros, ties and right angles are allowed. -/
theorem nuclearSortedMinimum_le_energy (n : ℕ) (theta : Fin n → ℝ)
    (htheta : ∀ i, theta i ∈ Icc 0 (Real.pi / 2)) (horder : Antitone theta)
    (s : Fin n → Fin n) (hs : Function.Involutive s) :
    nuclearSortedMinimum theta ≤ nuclearMatchingEnergy theta s := by
  induction n using Nat.twoStepInduction with
  | zero => simp [nuclearSortedMinimum, nuclearMatchingEnergy, cost]
  | one =>
    have hs0 : s 0 = 0 := Subsingleton.elim _ _
    simp only [nuclearSortedMinimum, nuclearAdjacentSum, nuclearMatchingEnergy,
      cost, Fin.sum_univ_one, hs0, ite_true, add_zero]
    exact le_rfl
  | more n ih ih1 =>
    obtain ⟨t, ht, hcost, hhead⟩ := exists_nuclear_head_normalization theta htheta horder s hs
    let c (i : Fin (n + 2)) := min (nuclearCanonicalCost (theta i)) 2
    let w (i j : Fin (n + 2)) := realNuclearPairWeight (theta i) (theta j)
    rcases hhead with ⟨ht0, hc0⟩ | ht01
    · obtain ⟨r, hr, hsplit⟩ := exists_tail_of_fixed c w t ht ht0
      change nuclearMatchingEnergy theta t = c 0 +
        nuclearMatchingEnergy (fun i : Fin (n + 1) => theta i.succ) r at hsplit
      have hbound := ih1 (fun i : Fin (n + 1) => theta i.succ)
        (fun i => htheta i.succ)
        (fun _ _ h => horder (Fin.succ_le_succ_iff.mpr h)) r hr
      calc
        nuclearSortedMinimum theta ≤
            2 + nuclearSortedMinimum (fun i : Fin (n + 1) => theta i.succ) :=
          sorted_le_reflection theta
        _ ≤ 2 + nuclearMatchingEnergy (fun i : Fin (n + 1) => theta i.succ) r :=
          by linarith
        _ = nuclearMatchingEnergy theta t := by rw [hsplit]; exact congrArg (· + _) hc0.symm
        _ ≤ nuclearMatchingEnergy theta s := hcost
    · obtain ⟨r, hr, hsplit⟩ := exists_tail_of_pair c w
        (fun _ _ => realNuclearPairWeight_comm _ _) t ht ht01
      change nuclearMatchingEnergy theta t = realNuclearPairWeight (theta 0) (theta 1) +
        nuclearMatchingEnergy (fun i : Fin n => theta i.succ.succ) r at hsplit
      have hbound := ih (fun i : Fin n => theta i.succ.succ)
        (fun i => htheta i.succ.succ)
        (fun _ _ h => horder (Fin.succ_le_succ_iff.mpr (Fin.succ_le_succ_iff.mpr h))) r hr
      calc
        nuclearSortedMinimum theta ≤ realNuclearPairWeight (theta 0) (theta 1) +
            nuclearSortedMinimum (fun i : Fin n => theta i.succ.succ) :=
          sorted_le_pair theta htheta horder
        _ ≤ realNuclearPairWeight (theta 0) (theta 1) +
            nuclearMatchingEnergy (fun i : Fin n => theta i.succ.succ) r := by linarith
        _ = nuclearMatchingEnergy theta t := hsplit.symm
        _ ≤ nuclearMatchingEnergy theta s := hcost

/-- Adjacent pairs and a possible final canonical singleton have cost
at most the adjacent sum. The native singleton is allowed to choose the
cheaper reflection, so this is an upper bound before global optimality. -/
theorem exists_nuclear_energy_le_adjacent (n : ℕ) (theta : Fin n → ℝ) :
    ∃ s : Fin n → Fin n, Function.Involutive s ∧
      nuclearMatchingEnergy theta s ≤ nuclearAdjacentSum theta := by
  induction n using Nat.twoStepInduction with
  | zero => exact ⟨id, fun _ => rfl, by simp [nuclearMatchingEnergy, cost, nuclearAdjacentSum]⟩
  | one =>
    refine ⟨id, fun _ => rfl, ?_⟩
    change (∑ i : Fin 1, min (nuclearCanonicalCost (theta i)) 2) ≤ _
    rw [Fin.sum_univ_one]
    exact min_le_left _ _
  | more n ih _ =>
    obtain ⟨s, hs, hcost⟩ := ih (fun i : Fin n => theta i.succ.succ)
    refine ⟨prependPair s, prependPair_involutive s hs, ?_⟩
    have hsplit : nuclearMatchingEnergy theta (prependPair s) =
        realNuclearPairWeight (theta 0) (theta 1) +
          nuclearMatchingEnergy (fun i : Fin n => theta i.succ.succ) s :=
      cost_prependPair _ _ (fun _ _ => realNuclearPairWeight_comm _ _) s
    rw [hsplit]
    change _ ≤ realNuclearPairWeight (theta 0) (theta 1) +
      nuclearAdjacentSum (fun i : Fin n => theta i.succ.succ)
    linarith

/-- One of the two adjacent patterns gives a matching of cost at most
the proposed value, including empty and singleton lists. -/
theorem exists_nuclear_energy_le_sorted (n : ℕ) (theta : Fin n → ℝ) :
    ∃ s : Fin n → Fin n, Function.Involutive s ∧
      nuclearMatchingEnergy theta s ≤ nuclearSortedMinimum theta := by
  cases n with
  | zero => exact ⟨id, fun _ => rfl, by simp [nuclearMatchingEnergy, cost, nuclearSortedMinimum]⟩
  | succ n =>
    by_cases h : nuclearAdjacentSum theta ≤
        2 + nuclearAdjacentSum (fun i : Fin n => theta i.succ)
    · obtain ⟨s, hs, hcost⟩ := exists_nuclear_energy_le_adjacent (n + 1) theta
      refine ⟨s, hs, ?_⟩
      change _ ≤ min _ _
      rw [min_eq_left h]
      exact hcost
    · obtain ⟨s, hs, hcost⟩ := exists_nuclear_energy_le_adjacent n
        (fun i : Fin n => theta i.succ)
      refine ⟨prependFixed s, prependFixed_involutive s hs, ?_⟩
      have hsplit : nuclearMatchingEnergy theta (prependFixed s) =
          min (nuclearCanonicalCost (theta 0)) 2 +
            nuclearMatchingEnergy (fun i : Fin n => theta i.succ) s :=
        cost_prependFixed _ _ s
      change _ ≤ min _ _
      rw [min_eq_right (not_le.mp h).le, hsplit]
      linarith [min_le_right (nuclearCanonicalCost (theta 0)) (2 : ℝ)]

/-- The function-based exchange energy is the existing labelled nuclear
matching cost on permutations. -/
theorem nuclearMatchingEnergy_eq_cost {ι : Type*} [Fintype ι] [DecidableEq ι]
    (theta : ι → ℝ) (s : Equiv.Perm ι) :
    nuclearMatchingEnergy theta s = realNuclearMatchingCost theta s := by
  simp only [nuclearMatchingEnergy, cost, realNuclearMatchingCost,
    nuclearCanonicalCost, realNuclearPairWeight, add_zero]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> rfl

/-- **Two adjacent sums for the exact nuclear matching minimum.**
All optional singleton choices, repeated/zero/right angles and both empty
and singleton lists are included. This is a global finite matching theorem. -/
theorem realNuclearMatchingMinimum_eq_sorted (n : ℕ) (theta : Fin n → ℝ)
    (htheta : ∀ i, theta i ∈ Icc 0 (Real.pi / 2)) (horder : Antitone theta) :
    realNuclearMatchingMinimum theta = nuclearSortedMinimum theta := by
  apply le_antisymm
  · obtain ⟨s, hs, hcost⟩ := exists_nuclear_energy_le_sorted n theta
    let S := Function.Involutive.toPerm s hs
    have hbound : realNuclearMatchingMinimum theta ≤ realNuclearMatchingCost theta S :=
      Finset.inf'_le _ ((mem_realSchattenMatchings S).mpr hs)
    have heq : realNuclearMatchingCost theta S = nuclearMatchingEnergy theta s :=
      (nuclearMatchingEnergy_eq_cost theta S).symm
    exact hbound.trans (heq.trans_le hcost)
  · obtain ⟨s, hs, heq⟩ := Finset.exists_mem_eq_inf'
      (realSchattenMatchings_nonempty (Fin n)) (realNuclearMatchingCost theta)
    have hinv := (mem_realSchattenMatchings s).mp hs
    have hbound := nuclearSortedMinimum_le_energy n theta htheta horder s hinv
    rw [nuclearMatchingEnergy_eq_cost, heq.symm] at hbound
    exact hbound

/-- Relabelling preserves the nuclear matching cost, with repeated angles
retained as distinct vertices. -/
theorem realNuclearMatchingCost_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (theta : κ → ℝ) (s : Equiv.Perm κ) (e : ι ≃ κ) :
    realNuclearMatchingCost (theta ∘ e) ((e.trans s).trans e.symm) =
      realNuclearMatchingCost theta s := by
  classical
  unfold realNuclearMatchingCost
  rw [← e.sum_comp (fun i => if s i = i then min (4 * Real.sin (theta i / 2)) 2
    else realNuclearPairWeight (theta i) (theta (s i)) / 2)]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Equiv.trans_apply, Function.comp_apply, Equiv.apply_symm_apply,
    Equiv.symm_apply_eq]

private theorem nuclear_minimum_reindex_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (theta : κ → ℝ) (e : ι ≃ κ) :
    realNuclearMatchingMinimum (theta ∘ e) ≤ realNuclearMatchingMinimum theta := by
  classical
  obtain ⟨s, hs, heq⟩ := Finset.exists_mem_eq_inf'
    (realSchattenMatchings_nonempty κ) (realNuclearMatchingCost theta)
  have hinv := (mem_realSchattenMatchings s).mp hs
  let t := (e.trans s).trans e.symm
  have ht : Function.Involutive t := by
    intro i
    simp only [t, Equiv.trans_apply, Equiv.apply_symm_apply]
    exact (congrArg e.symm (hinv (e i))).trans (e.symm_apply_apply i)
  have hbound : realNuclearMatchingMinimum (theta ∘ e) ≤
      realNuclearMatchingCost (theta ∘ e) t :=
    Finset.inf'_le _ ((mem_realSchattenMatchings t).mpr ht)
  rw [realNuclearMatchingCost_reindex] at hbound
  exact hbound.trans_eq heq.symm

/-- Exact invariance of the nuclear matching minimum under any finite
vertex relabelling. This includes the empty type. -/
theorem realNuclearMatchingMinimum_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (theta : κ → ℝ) (e : ι ≃ κ) :
    realNuclearMatchingMinimum (theta ∘ e) = realNuclearMatchingMinimum theta := by
  apply le_antisymm (nuclear_minimum_reindex_le theta e)
  have h := nuclear_minimum_reindex_le (theta ∘ e) e.symm
  simpa only [Function.comp_def, Equiv.apply_symm_apply] using h

end TauCeti.DavisKahan.FiniteDimensional.RealTransport

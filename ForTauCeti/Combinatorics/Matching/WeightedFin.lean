/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Combinatorics.Matching.WeightedInvolution
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Removing leading orbits of a weighted finite matching

The actual remaining involution is retained when a leading fixed vertex or
leading two-cycle is removed. These classical finite-sum identities include
empty tails and arbitrary singleton/edge costs.
-/

public section
noncomputable section

namespace TauCeti.WeightedInvolution

open scoped BigOperators

/-- Remove a fixed leading vertex, retaining the exact tail cost. -/
theorem exists_tail_of_fixed {n : ℕ} (c : Fin (n + 1) → ℝ)
    (w : Fin (n + 1) → Fin (n + 1) → ℝ) (s : Fin (n + 1) → Fin (n + 1))
    (hs : Function.Involutive s) (h0 : s 0 = 0) :
    ∃ t : Fin n → Fin n, Function.Involutive t ∧
      cost c w s = c 0 + cost (fun x => c x.succ) (fun x y => w x.succ y.succ) t := by
  have hne (x : Fin n) : s x.succ ≠ 0 := by
    intro h
    exact Fin.succ_ne_zero x (hs.injective (h.trans h0.symm))
  let t (x : Fin n) := (s x.succ).pred (hne x)
  have ht (x : Fin n) : (t x).succ = s x.succ := Fin.succ_pred _ _
  refine ⟨t, ?_, ?_⟩
  · intro x
    apply Fin.succ_injective
    rw [ht, ht, hs x.succ]
  · rw [cost, Fin.sum_univ_succ]
    simp only [h0, ite_true]
    apply congrArg (fun r : ℝ => c 0 + r)
    unfold cost
    apply Finset.sum_congr rfl
    intro x _
    simp only [← ht x, Fin.succ_inj]

/-- Remove a leading two-cycle, retaining the exact tail cost. -/
theorem exists_tail_of_pair {n : ℕ} (c : Fin (n + 2) → ℝ)
    (w : Fin (n + 2) → Fin (n + 2) → ℝ) (hw : ∀ x y, w x y = w y x)
    (s : Fin (n + 2) → Fin (n + 2)) (hs : Function.Involutive s) (h0 : s 0 = 1) :
    ∃ t : Fin n → Fin n, Function.Involutive t ∧
      cost c w s = w 0 1 +
        cost (fun x => c x.succ.succ) (fun x y => w x.succ.succ y.succ.succ) t := by
  have h1 : s 1 = 0 := by rw [← h0, hs 0]
  have hne0 (x : Fin n) : s x.succ.succ ≠ 0 := by
    intro h
    have h' : x.succ.succ = 1 := hs.injective (h.trans h1.symm)
    have hval := congrArg Fin.val h'
    simp only [Fin.val_succ, Fin.val_one] at hval
    omega
  have hne1 (x : Fin n) : (s x.succ.succ).pred (hne0 x) ≠ 0 := by
    intro h
    have h' := congrArg Fin.succ h
    rw [Fin.succ_pred] at h'
    have h'' : x.succ.succ = 0 := hs.injective (h'.trans h0.symm)
    exact Fin.succ_ne_zero x.succ h''
  let t (x : Fin n) := ((s x.succ.succ).pred (hne0 x)).pred (hne1 x)
  have ht (x : Fin n) : (t x).succ.succ = s x.succ.succ := by
    simp only [t, Fin.succ_pred]
  refine ⟨t, ?_, ?_⟩
  · intro x
    apply Fin.succ_injective
    apply Fin.succ_injective
    rw [ht, ht, hs x.succ.succ]
  · rw [cost, Fin.sum_univ_succ, Fin.sum_univ_succ]
    change (if s 0 = 0 then c 0 else w 0 (s 0) / 2) +
      ((if s 1 = 1 then c 1 else w 1 (s 1) / 2) +
        ∑ x : Fin n, if s x.succ.succ = x.succ.succ then c x.succ.succ
          else w x.succ.succ (s x.succ.succ) / 2) = _
    have htail : (∑ x : Fin n, if s x.succ.succ = x.succ.succ then c x.succ.succ
        else w x.succ.succ (s x.succ.succ) / 2) =
        cost (fun x => c x.succ.succ) (fun x y => w x.succ.succ y.succ.succ) t := by
      unfold cost
      apply Finset.sum_congr rfl
      intro x _
      simp only [← ht x, Fin.succ_inj]
    simp only [h0, h1, (Ne.symm Fin.zero_ne_one), Fin.zero_ne_one, ite_false, htail]
    rw [hw 1 0]
    ring

/-- Add a leading fixed vertex to a matching. -/
@[expose] def prependFixed {n : ℕ} (t : Fin n → Fin n) : Fin (n + 1) → Fin (n + 1) :=
  Fin.cases 0 (fun x => (t x).succ)

theorem prependFixed_involutive {n : ℕ} (t : Fin n → Fin n) (ht : Function.Involutive t) :
    Function.Involutive (prependFixed t) := by
  intro x
  refine Fin.cases ?_ (fun i => ?_) x
  · rfl
  · change (t (t i)).succ = i.succ
    rw [ht i]

theorem cost_prependFixed {n : ℕ} (c : Fin (n + 1) → ℝ)
    (w : Fin (n + 1) → Fin (n + 1) → ℝ) (t : Fin n → Fin n) :
    cost c w (prependFixed t) =
      c 0 + cost (fun x => c x.succ) (fun x y => w x.succ y.succ) t := by
  simp only [cost, Fin.sum_univ_succ, prependFixed, Fin.cases_zero, Fin.cases_succ,
    Fin.succ_inj, ite_true]

/-- Add a leading two-cycle to a matching. -/
@[expose] def prependPair {n : ℕ} (t : Fin n → Fin n) : Fin (n + 2) → Fin (n + 2) :=
  Fin.cases 1 (Fin.cases 0 (fun x => (t x).succ.succ))

theorem prependPair_involutive {n : ℕ} (t : Fin n → Fin n) (ht : Function.Involutive t) :
    Function.Involutive (prependPair t) := by
  intro x
  refine Fin.cases ?_ (fun i => ?_) x
  · rfl
  · refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change (t (t j)).succ.succ = j.succ.succ
      rw [ht j]

theorem cost_prependPair {n : ℕ} (c : Fin (n + 2) → ℝ)
    (w : Fin (n + 2) → Fin (n + 2) → ℝ) (hw : ∀ x y, w x y = w y x)
    (t : Fin n → Fin n) :
    cost c w (prependPair t) = w 0 1 +
      cost (fun x => c x.succ.succ) (fun x y => w x.succ.succ y.succ.succ) t := by
  have h0 : prependPair t 0 = 1 := rfl
  have h1 : prependPair t 1 = 0 := rfl
  have ht (x : Fin n) : prependPair t x.succ.succ = (t x).succ.succ := rfl
  rw [cost, Fin.sum_univ_succ, Fin.sum_univ_succ]
  change (if prependPair t 0 = 0 then c 0 else w 0 (prependPair t 0) / 2) +
    ((if prependPair t 1 = 1 then c 1 else w 1 (prependPair t 1) / 2) +
      ∑ x : Fin n, if prependPair t x.succ.succ = x.succ.succ then c x.succ.succ
        else w x.succ.succ (prependPair t x.succ.succ) / 2) = _
  simp only [h0, h1, ht, Fin.zero_ne_one, Ne.symm Fin.zero_ne_one, ite_false, Fin.succ_inj]
  rw [hw 1 0]
  unfold cost
  ring

end TauCeti.WeightedInvolution

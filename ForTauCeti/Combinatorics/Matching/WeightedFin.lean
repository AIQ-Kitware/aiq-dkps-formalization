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

An involution fixing the leading vertex, or interchanging the first two
vertices, has a unique exact decomposition into that orbit and a tail
involution. This is a statement about the entire map, independent of costs.
The weighted removal identities follow from these decompositions, including
empty tails and arbitrary costs in a division semiring. Only the two-cycle
cost identities require `2 ≠ 0`. These are classical finite matching facts.
-/

public section
noncomputable section

namespace TauCeti.WeightedInvolution

open scoped BigOperators

/-- Add a leading fixed vertex to a matching. -/
def prependFixed {n : ℕ} (t : Fin n → Fin n) : Fin (n + 1) → Fin (n + 1) :=
  Fin.cases 0 (fun x => (t x).succ)

@[simp] theorem prependFixed_zero {n : ℕ} (t : Fin n → Fin n) :
    prependFixed t 0 = 0 := (rfl)

@[simp] theorem prependFixed_succ {n : ℕ} (t : Fin n → Fin n) (x : Fin n) :
    prependFixed t x.succ = (t x).succ := (rfl)

theorem prependFixed_involutive {n : ℕ} (t : Fin n → Fin n) (ht : Function.Involutive t) :
    Function.Involutive (prependFixed t) := by
  intro x
  refine Fin.cases ?_ (fun i => ?_) x
  · rfl
  · simp only [prependFixed_succ, ht i]

/-- Add a leading two-cycle to a matching. -/
def prependPair {n : ℕ} (t : Fin n → Fin n) : Fin (n + 2) → Fin (n + 2) :=
  Fin.cases 1 (Fin.cases 0 (fun x => (t x).succ.succ))

@[simp] theorem prependPair_zero {n : ℕ} (t : Fin n → Fin n) :
    prependPair t 0 = 1 := (rfl)

@[simp] theorem prependPair_one {n : ℕ} (t : Fin n → Fin n) :
    prependPair t 1 = 0 := (rfl)

@[simp] theorem prependPair_succ_succ {n : ℕ} (t : Fin n → Fin n) (x : Fin n) :
    prependPair t x.succ.succ = (t x).succ.succ := (rfl)

theorem prependPair_involutive {n : ℕ} (t : Fin n → Fin n) (ht : Function.Involutive t) :
    Function.Involutive (prependPair t) := by
  intro x
  refine Fin.cases ?_ (fun i => ?_) x
  · rfl
  · refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp only [prependPair_succ_succ, ht j]

/-- An involution fixing the first vertex is obtained from a unique tail
involution by adjoining that fixed vertex. All map values are retained. -/
theorem existsUnique_prependFixed {n : ℕ} (s : Fin (n + 1) → Fin (n + 1))
    (hs : Function.Involutive s) (h0 : s 0 = 0) :
    ∃! t : Fin n → Fin n, Function.Involutive t ∧ s = prependFixed t := by
  have hne (x : Fin n) : s x.succ ≠ 0 := by
    intro h
    exact Fin.succ_ne_zero x (hs.injective (h.trans h0.symm))
  let t (x : Fin n) := (s x.succ).pred (hne x)
  have ht (x : Fin n) : (t x).succ = s x.succ := Fin.succ_pred _ _
  have hst : s = prependFixed t := by
    funext x
    refine Fin.cases ?_ (fun i => ?_) x
    · simpa only [prependFixed_zero] using h0
    · simpa only [prependFixed_succ] using (ht i).symm
  refine ⟨t, ⟨?_, hst⟩, ?_⟩
  · intro x
    apply Fin.succ_injective
    rw [ht, ht, hs x.succ]
  · intro u hu
    funext x
    have h := congrFun (hu.2.symm.trans hst) x.succ
    simpa only [prependFixed_succ, Fin.succ_inj] using h

/-- An involution pairing its first two vertices is obtained from a unique
tail involution by adjoining that two-cycle. No cost or scalar field occurs. -/
theorem existsUnique_prependPair {n : ℕ} (s : Fin (n + 2) → Fin (n + 2))
    (hs : Function.Involutive s) (h0 : s 0 = 1) :
    ∃! t : Fin n → Fin n, Function.Involutive t ∧ s = prependPair t := by
  have h1 : s 1 = 0 := by rw [← h0, hs 0]
  have hne0 (x : Fin n) : s x.succ.succ ≠ 0 := by
    intro h
    exact Fin.succ_succ_ne_one x (hs.injective (h.trans h1.symm))
  have hne1 (x : Fin n) : (s x.succ.succ).pred (hne0 x) ≠ 0 := by
    intro h
    have h' := congrArg Fin.succ h
    rw [Fin.succ_pred] at h'
    exact Fin.succ_ne_zero x.succ (hs.injective (h'.trans h0.symm))
  let t (x : Fin n) := ((s x.succ.succ).pred (hne0 x)).pred (hne1 x)
  have ht (x : Fin n) : (t x).succ.succ = s x.succ.succ := by
    simp only [t, Fin.succ_pred]
  have hst : s = prependPair t := by
    funext x
    refine Fin.cases ?_ (fun i => ?_) x
    · simpa only [prependPair_zero] using h0
    · refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [Fin.succ_zero_eq_one, prependPair_one] using h1
      · simpa only [prependPair_succ_succ] using (ht j).symm
  refine ⟨t, ⟨?_, hst⟩, ?_⟩
  · intro x
    apply Fin.succ_injective
    apply Fin.succ_injective
    rw [ht, ht, hs x.succ.succ]
  · intro u hu
    funext x
    have h := congrFun (hu.2.symm.trans hst) x.succ.succ
    simpa only [prependPair_succ_succ, Fin.succ_inj] using h

variable {R : Type*} [DivisionSemiring R]

@[simp] theorem cost_prependFixed {n : ℕ} (c : Fin (n + 1) → R)
    (w : Fin (n + 1) → Fin (n + 1) → R) (t : Fin n → Fin n) :
    cost c w (prependFixed t) =
      c 0 + cost (fun x => c x.succ) (fun x y => w x.succ y.succ) t := by
  simp only [cost_eq_sum, Fin.sum_univ_succ, prependFixed_zero, prependFixed_succ,
    Fin.succ_inj, ite_true]

@[simp] theorem cost_prependPair [NeZero (2 : R)] {n : ℕ} (c : Fin (n + 2) → R)
    (w : Fin (n + 2) → Fin (n + 2) → R) (hw : ∀ x y, w x y = w y x)
    (t : Fin n → Fin n) :
    cost c w (prependPair t) = w 0 1 +
      cost (fun x => c x.succ.succ) (fun x y => w x.succ.succ y.succ.succ) t := by
  rw [cost_eq_sum, Fin.sum_univ_succ, Fin.sum_univ_succ]
  -- Name the two head entries before simplifying their dependent `if`s.
  change (if prependPair t 0 = 0 then c 0 else w 0 (prependPair t 0) / 2) +
    ((if prependPair t 1 = 1 then c 1 else w 1 (prependPair t 1) / 2) +
      ∑ x : Fin n, if prependPair t x.succ.succ = x.succ.succ then c x.succ.succ
        else w x.succ.succ (prependPair t x.succ.succ) / 2) = _
  simp only [prependPair_zero, prependPair_one, prependPair_succ_succ,
    Fin.zero_ne_one, Ne.symm Fin.zero_ne_one, ite_false, Fin.succ_inj]
  rw [hw 1 0]
  rw [cost_eq_sum]
  rw [← add_assoc, add_halves]

/-- Remove a fixed leading vertex, retaining the exact tail cost. -/
theorem exists_tail_of_fixed {n : ℕ} (c : Fin (n + 1) → R)
    (w : Fin (n + 1) → Fin (n + 1) → R) (s : Fin (n + 1) → Fin (n + 1))
    (hs : Function.Involutive s) (h0 : s 0 = 0) :
    ∃ t : Fin n → Fin n, Function.Involutive t ∧
      cost c w s = c 0 + cost (fun x => c x.succ) (fun x y => w x.succ y.succ) t := by
  obtain ⟨t, ht, rfl⟩ := (existsUnique_prependFixed s hs h0).exists
  exact ⟨t, ht, cost_prependFixed c w t⟩

/-- Remove a leading two-cycle, retaining the exact tail cost. -/
theorem exists_tail_of_pair [NeZero (2 : R)] {n : ℕ} (c : Fin (n + 2) → R)
    (w : Fin (n + 2) → Fin (n + 2) → R) (hw : ∀ x y, w x y = w y x)
    (s : Fin (n + 2) → Fin (n + 2)) (hs : Function.Involutive s) (h0 : s 0 = 1) :
    ∃ t : Fin n → Fin n, Function.Involutive t ∧
      cost c w s = w 0 1 +
        cost (fun x => c x.succ.succ) (fun x y => w x.succ.succ y.succ.succ) t := by
  obtain ⟨t, ht, rfl⟩ := (existsUnique_prependPair s hs h0).exists
  exact ⟨t, ht, cost_prependPair c w hw t⟩

end TauCeti.WeightedInvolution

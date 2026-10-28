/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.GroupTheory.Perm.Basic
public import ForTauCeti.Logic.Equiv.Involutive
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FieldSimp

/-!
# Local exchanges in weighted involutions

Fixed points have singleton costs; each two-cycle has a symmetric edge cost,
counted half at each endpoint. Relabelling a fixed point with an edge endpoint
and exchanging two edges give exact local cost identities.

Costs and relabelling work over a division semiring. The subtraction formula
uses a division ring, while exchanges use a field with `2 ≠ 0`. No order,
positivity or analytic properties of the weights are used.
The cost is independent of a chosen decidable equality on the vertices.

These are classical finite matching manipulations, implemented for the real
nuclear transport sorting argument. No priority claim is made for the
combinatorial operations. The source-level transport provenance is maintained
in `dev/spectral-transport-unification.md`.
-/

public section
noncomputable section

namespace TauCeti.WeightedInvolution

open scoped BigOperators

variable {α : Type*} {R : Type*} [Fintype α]

section DivisionSemiring

variable [DivisionSemiring R]

/-- Singleton costs on fixed points and half an edge cost at each endpoint. -/
def cost (c : α → R) (w : α → α → R) (s : α → α) : R := by
  classical
  exact ∑ x, if s x = x then c x else w x (s x) / 2

/-- The defining finite sum; consumers need not unfold `cost`. -/
theorem cost_eq_sum [DecidableEq α] (c : α → R) (w : α → α → R) (s : α → α) :
    cost c w s = ∑ x, if s x = x then c x else w x (s x) / 2 := by
  unfold cost
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> rfl

/-- The identity matching has only singleton costs. -/
@[simp] theorem cost_id (c : α → R) (w : α → α → R) :
    cost c w id = ∑ x, c x := by
  classical
  simp only [cost_eq_sum, id_eq, ite_true]

/-- Relabelling arbitrary finite vertex types preserves cost. Neither symmetry
of the weights nor involutivity of the map is required. -/
theorem cost_reindex {β : Type*} [Fintype β]
    (c : α → R) (w : α → α → R) (s : α → α) (e : α ≃ β) :
    cost (fun x => c (e.symm x)) (fun x y => w (e.symm x) (e.symm y)) (e.conj s) =
      cost c w s := by
  classical
  rw [cost_eq_sum, cost_eq_sum, ← e.symm.sum_comp]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Equiv.conj_apply, Equiv.symm_apply_apply, ← Equiv.eq_symm_apply]

end DivisionSemiring

section DivisionRing

variable [DivisionRing R]

/-- A change supported on finitely many vertices changes only their cost
contributions. This localizes exchanges without an ordered scalar field. -/
theorem cost_sub_cost_eq_sum [DecidableEq α] (c : α → R) (w : α → α → R) (s t : α → α)
    (S : Finset α) (hoff : ∀ x ∉ S, s x = t x) :
    cost c w s - cost c w t = ∑ x ∈ S,
      ((if s x = x then c x else w x (s x) / 2) -
        (if t x = x then c x else w x (t x) / 2)) := by
  rw [cost_eq_sum, cost_eq_sum, ← Finset.sum_sub_distrib]
  symm
  apply Fintype.sum_subset
  intro x hx
  by_contra hxS
  exact hx (by rw [hoff x hxS, sub_self])

end DivisionRing

section Field

variable [Field R] [DecidableEq α] [NeZero (2 : R)]

/-- Exchange a fixed vertex `a` with the endpoint `d` of an edge `b--d`.
The new edge is `a--b`, and `d` becomes fixed. -/
theorem cost_conjugate_fixed_edge (c : α → R) (w : α → α → R)
    (hw : ∀ x y, w x y = w y x) (s : α → α) (hs : Function.Involutive s)
    (a b d : α) (hsa : s a = a) (hsb : s b = d) (hbd : b ≠ d) :
    cost c w ((Equiv.swap a d).conj s) + c a + w b d =
      cost c w s + c d + w a b := by
  have hsd : s d = b := by rw [← hsb, hs b]
  have hab : a ≠ b := by
    rintro rfl
    exact hbd (hsa.symm.trans hsb)
  have had : a ≠ d := by simpa only [hsa, hsb] using hs.injective.ne hab
  let t := (Equiv.swap a d).conj s
  let term (v : α → α) (x : α) := if v x = x then c x else w x (v x) / 2
  suffices h : cost c w t - cost c w s = c d + w a b - (c a + w b d) by
    linear_combination h
  calc
    _ = ∑ x ∈ ({a, b, d} : Finset α), (term t x - term s x) := by
      apply cost_sub_cost_eq_sum
      intro x hx
      have ⟨hxa, hxb, hxd⟩ : x ≠ a ∧ x ≠ b ∧ x ≠ d := by
        simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hx
      have hsxa : s x ≠ a := by simpa only [ne_eq, hs.eq_iff, hsa] using hxa
      have hsxd : s x ≠ d := by simpa only [ne_eq, hs.eq_iff, hsd] using hxb
      simp only [t, Equiv.conj_apply, Equiv.symm_swap,
        Equiv.swap_apply_of_ne_of_ne hxa hxd,
        Equiv.swap_apply_of_ne_of_ne hsxa hsxd]
    _ = _ := by
      have hta : t a = b := by
        simp only [t, Equiv.conj_apply, Equiv.symm_swap, Equiv.swap_apply_left, hsd,
          Equiv.swap_apply_of_ne_of_ne hab.symm hbd]
      have htb : t b = a := by
        simp only [t, Equiv.conj_apply, Equiv.symm_swap,
          Equiv.swap_apply_of_ne_of_ne hab.symm hbd, hsb, Equiv.swap_apply_right]
      have htd : t d = d := by simp [t, Equiv.conj_apply, hsa]
      simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
        had, or_self, not_false_eq_true, Finset.sum_singleton,
        term, hta, htb, htd, hsa, hsb, hsd, hab.symm, hab, hbd.symm, hbd,
        ite_true, ite_false]
      rw [hw b a, hw d b]
      field_simp
      ring1

/-- Exchange two disjoint edges `a--u` and `b--v` for `a--b` and `u--v`. -/
theorem cost_conjugate_two_edges (c : α → R) (w : α → α → R)
    (hw : ∀ x y, w x y = w y x) (s : α → α) (hs : Function.Involutive s)
    (a b u v : α) (hab : a ≠ b) (hau : a ≠ u) (hav : a ≠ v)
    (hbv : b ≠ v) (hsa : s a = u) (hsb : s b = v) :
    cost c w ((Equiv.swap b u).conj s) + w a u + w b v =
      cost c w s + w a b + w u v := by
  have hsu : s u = a := by rw [← hsa, hs a]
  have hsv : s v = b := by rw [← hsb, hs b]
  have hbu : b ≠ u := by simpa only [hsv, hsa] using hs.injective.ne hav.symm
  have huv : u ≠ v := by simpa only [hsa, hsb] using hs.injective.ne hab
  let t := (Equiv.swap b u).conj s
  let term (f : α → α) (x : α) := if f x = x then c x else w x (f x) / 2
  suffices h : cost c w t - cost c w s = w a b + w u v - (w a u + w b v) by
    linear_combination h
  calc
    _ = ∑ x ∈ ({a, b, u, v} : Finset α), (term t x - term s x) := by
      apply cost_sub_cost_eq_sum
      intro x hx
      have ⟨hxa, hxb, hxu, hxv⟩ : x ≠ a ∧ x ≠ b ∧ x ≠ u ∧ x ≠ v := by
        simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hx
      have hsxb : s x ≠ b := by simpa only [ne_eq, hs.eq_iff, hsb] using hxv
      have hsxu : s x ≠ u := by simpa only [ne_eq, hs.eq_iff, hsu] using hxa
      simp only [t, Equiv.conj_apply, Equiv.symm_swap,
        Equiv.swap_apply_of_ne_of_ne hxb hxu,
        Equiv.swap_apply_of_ne_of_ne hsxb hsxu]
    _ = _ := by
      have hta : t a = b := by
        simp only [t, Equiv.conj_apply, Equiv.symm_swap,
          Equiv.swap_apply_of_ne_of_ne hab hau, hsa, Equiv.swap_apply_right]
      have htb : t b = a := by
        simp only [t, Equiv.conj_apply, Equiv.symm_swap, Equiv.swap_apply_left, hsu,
          Equiv.swap_apply_of_ne_of_ne hab hau]
      have htu : t u = v := by
        simp only [t, Equiv.conj_apply, Equiv.symm_swap, Equiv.swap_apply_right, hsb,
          Equiv.swap_apply_of_ne_of_ne hbv.symm huv.symm]
      have htv : t v = u := by
        simp only [t, Equiv.conj_apply, Equiv.symm_swap,
          Equiv.swap_apply_of_ne_of_ne hbv.symm huv.symm, hsv, Equiv.swap_apply_left]
      simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
        term, hta, htb, htu, htv, hsa, hsb, hsu, hsv,
        hab, hau, hav, hbu, hbv, huv, hab.symm, hau.symm, hbv.symm, huv.symm,
        or_self, not_false_eq_true, Finset.sum_singleton, ite_false]
      rw [hw b a, hw v u, hw u a, hw v b]
      field_simp
      ring1

/-- Join two fixed vertices, leaving all other matching orbits unchanged. -/
def joinFixed (s : α → α) (a b : α) : α → α := fun x => Equiv.swap a b (s x)

omit [Fintype α] in
@[simp] theorem joinFixed_apply (s : α → α) (a b x : α) :
    joinFixed s a b x = Equiv.swap a b (s x) := (rfl)

omit [Fintype α] in
theorem joinFixed_involutive (s : α → α) (hs : Function.Involutive s)
    (a b : α) (hsa : s a = a) (hsb : s b = b) :
    Function.Involutive (joinFixed s a b) := by
  intro x
  by_cases hxa : x = a
  · subst x
    simp [hsa, hsb]
  by_cases hxb : x = b
  · subst x
    simp [hsa, hsb]
  have hsxa : s x ≠ a := by simpa only [ne_eq, hs.eq_iff, hsa] using hxa
  have hsxb : s x ≠ b := by simpa only [ne_eq, hs.eq_iff, hsb] using hxb
  simp only [joinFixed_apply, Equiv.swap_apply_of_ne_of_ne hsxa hsxb, hs x,
    Equiv.swap_apply_of_ne_of_ne hxa hxb]

/-- Joining two fixed points replaces exactly their singleton costs by
one symmetric edge cost. -/
theorem cost_joinFixed (c : α → R) (w : α → α → R)
    (hw : ∀ x y, w x y = w y x) (s : α → α) (hs : Function.Involutive s)
    (a b : α) (hab : a ≠ b) (hsa : s a = a) (hsb : s b = b) :
    cost c w (joinFixed s a b) + c a + c b = cost c w s + w a b := by
  let t := joinFixed s a b
  let term (f : α → α) (x : α) := if f x = x then c x else w x (f x) / 2
  suffices h : cost c w t - cost c w s = w a b - (c a + c b) by
    linear_combination h
  calc
    _ = ∑ x ∈ ({a, b} : Finset α), (term t x - term s x) := by
      apply cost_sub_cost_eq_sum
      intro x hx
      have ⟨hxa, hxb⟩ : x ≠ a ∧ x ≠ b := by
        simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hx
      have hsxa : s x ≠ a := by simpa only [ne_eq, hs.eq_iff, hsa] using hxa
      have hsxb : s x ≠ b := by simpa only [ne_eq, hs.eq_iff, hsb] using hxb
      exact Equiv.swap_apply_of_ne_of_ne hsxa hsxb
    _ = _ := by
      have hta : t a = b := by simp [t, hsa]
      have htb : t b = a := by simp [t, hsb]
      simp only [Finset.sum_insert, Finset.mem_singleton, hab, not_false_eq_true,
        Finset.sum_singleton, term, hta, htb, hsa, hsb, hab.symm, ite_true, ite_false]
      rw [hw b a]
      field_simp
      ring1

end Field

end TauCeti.WeightedInvolution

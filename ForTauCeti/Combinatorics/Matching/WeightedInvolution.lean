/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Local exchanges in weighted involutions

Fixed points have singleton costs; each two-cycle has a symmetric edge cost,
counted half at each endpoint. Relabelling a fixed point with an edge endpoint
and exchanging two edges give exact local cost identities.

These are classical finite matching manipulations, implemented for the real
nuclear transport sorting argument. No priority claim is made for the
combinatorial operations. The source-level transport provenance is maintained
in `dev/spectral-transport-unification.md`.
-/

public section
noncomputable section

namespace TauCeti.WeightedInvolution

open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Singleton costs on fixed points and half an edge cost at each endpoint. -/
@[expose]
def cost (c : α → ℝ) (w : α → α → ℝ) (s : α → α) : ℝ :=
  ∑ x, if s x = x then c x else w x (s x) / 2

/-- Relabelling by an involutive permutation. -/
@[expose]
def conjugate (q : Equiv.Perm α) (s : α → α) : α → α :=
  fun x => q (s (q.symm x))

omit [Fintype α] [DecidableEq α] in
theorem conjugate_involutive (q : Equiv.Perm α) (s : α → α)
    (hs : Function.Involutive s) : Function.Involutive (conjugate q s) := by
  intro x
  change q (s (q.symm (q (s (q.symm x))))) = x
  rw [q.symm_apply_apply, hs (q.symm x), q.apply_symm_apply]

omit [DecidableEq α] in
private theorem sum_balance (f g : α → ℝ) (S : Finset α) (a b : ℝ)
    (hoff : ∀ x ∉ S, f x = g x)
    (hlocal : (∑ x ∈ S, f x) + a = (∑ x ∈ S, g x) + b) :
    (∑ x, f x) + a = (∑ x, g x) + b := by
  classical
  have hc : (∑ x ∈ Sᶜ, f x) = ∑ x ∈ Sᶜ, g x := by
    apply Finset.sum_congr rfl
    intro x hx
    exact hoff x (Finset.mem_compl.mp hx)
  have hf := Finset.sum_add_sum_compl S f
  have hg := Finset.sum_add_sum_compl S g
  linarith

/-- Exchange a fixed vertex `a` with the endpoint `d` of an edge `b--d`.
The new edge is `a--b`, and `d` becomes fixed. -/
theorem cost_conjugate_fixed_edge (c : α → ℝ) (w : α → α → ℝ)
    (hw : ∀ x y, w x y = w y x) (s : α → α) (hs : Function.Involutive s)
    (a b d : α) (hab : a ≠ b) (hsa : s a = a) (hsb : s b = d) (hbd : b ≠ d) :
    cost c w (conjugate (Equiv.swap a d) s) + c a + w b d =
      cost c w s + c d + w a b := by
  have hsd : s d = b := by rw [← hsb, hs b]
  have had : a ≠ d := by
    intro h
    have h' := congrArg s h
    rw [hsa, hsd] at h'
    exact hab h'
  let t := conjugate (Equiv.swap a d) s
  let term (v : α → α) (x : α) := if v x = x then c x else w x (v x) / 2
  change (∑ x, term t x) + c a + w b d = (∑ x, term s x) + c d + w a b
  suffices h : (∑ x, term t x) + (c a + w b d) =
      (∑ x, term s x) + (c d + w a b) by linarith
  apply sum_balance (term t) (term s) {a, b, d} (c a + w b d) (c d + w a b)
  · intro x hx
    have hxa : x ≠ a := by
      intro h
      exact hx (by simp [h])
    have hxb : x ≠ b := by
      intro h
      exact hx (by simp [h])
    have hxd : x ≠ d := by
      intro h
      exact hx (by simp [h])
    have hsxa : s x ≠ a := by
      intro h
      have h' := congrArg s h
      rw [hs x, hsa] at h'
      exact hxa h'
    have hsxd : s x ≠ d := by
      intro h
      have h' := congrArg s h
      rw [hs x, hsd] at h'
      exact hxb h'
    have ht : t x = s x := by
      simp only [t, conjugate, Equiv.symm_swap,
        Equiv.swap_apply_of_ne_of_ne hxa hxd,
        Equiv.swap_apply_of_ne_of_ne hsxa hsxd]
    simp only [term, ht]
  · have hta : t a = b := by
      simp only [t, conjugate, Equiv.symm_swap, Equiv.swap_apply_left, hsd,
        Equiv.swap_apply_of_ne_of_ne hab.symm hbd]
    have htb : t b = a := by
      simp only [t, conjugate, Equiv.symm_swap,
        Equiv.swap_apply_of_ne_of_ne hab.symm hbd, hsb, Equiv.swap_apply_right]
    have htd : t d = d := by simp [t, conjugate, hsa]
    simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
      had, or_self, not_false_eq_true, Finset.sum_singleton,
      term, hta, htb, htd, hsa, hsb, hsd, hab.symm, hab, hbd.symm, hbd,
      ite_true, ite_false]
    rw [hw b a, hw d b]
    ring

/-- Exchange two disjoint edges `a--u` and `b--v` for `a--b` and `u--v`. -/
theorem cost_conjugate_two_edges (c : α → ℝ) (w : α → α → ℝ)
    (hw : ∀ x y, w x y = w y x) (s : α → α) (hs : Function.Involutive s)
    (a b u v : α) (hab : a ≠ b) (hau : a ≠ u) (hav : a ≠ v)
    (hbu : b ≠ u) (hbv : b ≠ v) (huv : u ≠ v) (hsa : s a = u) (hsb : s b = v) :
    cost c w (conjugate (Equiv.swap b u) s) + w a u + w b v =
      cost c w s + w a b + w u v := by
  have hsu : s u = a := by rw [← hsa, hs a]
  have hsv : s v = b := by rw [← hsb, hs b]
  let t := conjugate (Equiv.swap b u) s
  let term (f : α → α) (x : α) := if f x = x then c x else w x (f x) / 2
  change (∑ x, term t x) + w a u + w b v = (∑ x, term s x) + w a b + w u v
  suffices h : (∑ x, term t x) + (w a u + w b v) =
      (∑ x, term s x) + (w a b + w u v) by linarith
  apply sum_balance (term t) (term s) {a, b, u, v} _ _
  · intro x hx
    have hxa : x ≠ a := by intro h; exact hx (by simp [h])
    have hxb : x ≠ b := by intro h; exact hx (by simp [h])
    have hxu : x ≠ u := by intro h; exact hx (by simp [h])
    have hxv : x ≠ v := by intro h; exact hx (by simp [h])
    have hsxb : s x ≠ b := by
      intro h
      have h' := congrArg s h
      rw [hs x, hsb] at h'
      exact hxv h'
    have hsxu : s x ≠ u := by
      intro h
      have h' := congrArg s h
      rw [hs x, hsu] at h'
      exact hxa h'
    have ht : t x = s x := by
      simp only [t, conjugate, Equiv.symm_swap,
        Equiv.swap_apply_of_ne_of_ne hxb hxu,
        Equiv.swap_apply_of_ne_of_ne hsxb hsxu]
    simp only [term, ht]
  · have hta : t a = b := by
      simp only [t, conjugate, Equiv.symm_swap,
        Equiv.swap_apply_of_ne_of_ne hab hau, hsa, Equiv.swap_apply_right]
    have htb : t b = a := by
      simp only [t, conjugate, Equiv.symm_swap, Equiv.swap_apply_left, hsu,
        Equiv.swap_apply_of_ne_of_ne hab hau]
    have htu : t u = v := by
      simp only [t, conjugate, Equiv.symm_swap, Equiv.swap_apply_right, hsb,
        Equiv.swap_apply_of_ne_of_ne hbv.symm huv.symm]
    have htv : t v = u := by
      simp only [t, conjugate, Equiv.symm_swap,
        Equiv.swap_apply_of_ne_of_ne hbv.symm huv.symm, hsv, Equiv.swap_apply_left]
    simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
      term, hta, htb, htu, htv, hsa, hsb, hsu, hsv,
      hab, hau, hav, hbu, hbv, huv, hab.symm, hau.symm, hbv.symm, huv.symm,
      or_self, not_false_eq_true, Finset.sum_singleton, ite_false]
    rw [hw b a, hw v u, hw u a, hw v b]
    ring

/-- Join two fixed vertices, leaving all other matching orbits unchanged. -/
@[expose]
def joinFixed (s : α → α) (a b : α) : α → α := fun x => Equiv.swap a b (s x)

omit [Fintype α] in
theorem joinFixed_involutive (s : α → α) (hs : Function.Involutive s)
    (a b : α) (hsa : s a = a) (hsb : s b = b) :
    Function.Involutive (joinFixed s a b) := by
  intro x
  by_cases hxa : x = a
  · subst x
    simp [joinFixed, hsa, hsb]
  by_cases hxb : x = b
  · subst x
    simp [joinFixed, hsa, hsb]
  have hsxa : s x ≠ a := by
    intro h
    have h' := congrArg s h
    rw [hs x, hsa] at h'
    exact hxa h'
  have hsxb : s x ≠ b := by
    intro h
    have h' := congrArg s h
    rw [hs x, hsb] at h'
    exact hxb h'
  simp only [joinFixed, Equiv.swap_apply_of_ne_of_ne hsxa hsxb, hs x,
    Equiv.swap_apply_of_ne_of_ne hxa hxb]

/-- Joining two fixed points replaces exactly their singleton costs by
one symmetric edge cost. -/
theorem cost_joinFixed (c : α → ℝ) (w : α → α → ℝ)
    (hw : ∀ x y, w x y = w y x) (s : α → α) (hs : Function.Involutive s)
    (a b : α) (hab : a ≠ b) (hsa : s a = a) (hsb : s b = b) :
    cost c w (joinFixed s a b) + c a + c b = cost c w s + w a b := by
  let t := joinFixed s a b
  let term (f : α → α) (x : α) := if f x = x then c x else w x (f x) / 2
  change (∑ x, term t x) + c a + c b = (∑ x, term s x) + w a b
  suffices h : (∑ x, term t x) + (c a + c b) =
      (∑ x, term s x) + w a b by linarith
  apply sum_balance (term t) (term s) {a, b} _ _
  · intro x hx
    have hxa : x ≠ a := by intro h; exact hx (by simp [h])
    have hxb : x ≠ b := by intro h; exact hx (by simp [h])
    have hsxa : s x ≠ a := by
      intro h
      have h' := congrArg s h
      rw [hs x, hsa] at h'
      exact hxa h'
    have hsxb : s x ≠ b := by
      intro h
      have h' := congrArg s h
      rw [hs x, hsb] at h'
      exact hxb h'
    have ht : t x = s x := Equiv.swap_apply_of_ne_of_ne hsxa hsxb
    simp only [term, ht]
  · have hta : t a = b := by simp [t, joinFixed, hsa]
    have htb : t b = a := by simp [t, joinFixed, hsb]
    simp only [Finset.sum_insert, Finset.mem_singleton, hab, not_false_eq_true,
      Finset.sum_singleton, term, hta, htb, hsa, hsb, hab.symm, ite_true, ite_false]
    rw [hw b a]
    ring

end TauCeti.WeightedInvolution

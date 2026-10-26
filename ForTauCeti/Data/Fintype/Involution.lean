/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Algebra.Ring.Parity

/-!
# Pairing a finite type

A finite type admits a fixed-point-free involution exactly when its
cardinality is even. The forward direction counts the smaller and larger
members of each pair in finite coordinates; the converse transports the
Boolean flip on a product.

## Provenance

Classical finite-set counting, proved here for the DKPS nuclear transport
multiplicity criterion. This is a new Lean implementation in the
AIQ-Kitware DKPS repository, not an extraction from an external proof.
-/

public section

namespace TauCeti.Fintype

open _root_.Fintype

variable {α : Type*} [Fintype α]

/-- A fixed-point-free involution pairs all elements of a finite type. -/
theorem even_card_of_fixedPointFree_involutive (f : α → α)
    (hf : Function.Involutive f) (hfree : ∀ x, f x ≠ x) : Even (card α) := by
  classical
  let e := equivFin α
  let lo := Finset.univ.filter (fun x => e x < e (f x))
  let hi := Finset.univ.filter (fun x => ¬e x < e (f x))
  have hcard : lo.card = hi.card := by
    apply Finset.card_bij (fun x _ => f x)
    · intro x hx
      have hxlt : e x < e (f x) := (Finset.mem_filter.mp hx).2
      simp only [hi, Finset.mem_filter, Finset.mem_univ, true_and, hf x]
      exact not_lt.mpr hxlt.le
    · intro x _ y _ hxy
      exact hf.injective hxy
    · intro y hy
      have hle : e (f y) ≤ e y := not_lt.mp (Finset.mem_filter.mp hy).2
      have hlt : e (f y) < e y := lt_of_le_of_ne hle
        (fun heq => hfree y (e.injective heq))
      refine ⟨f y, ?_, hf y⟩
      simpa only [lo, Finset.mem_filter, Finset.mem_univ, true_and, hf y] using hlt
  have hsplit : lo.card + hi.card = card α := by
    simpa only [lo, hi, Finset.card_univ] using
      Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun x => e x < e (f x))
  exact ⟨lo.card, by omega⟩

/-- Even cardinality is sufficient for a complete pairing, including
the empty type. No order or chosen enumeration is part of the statement. -/
theorem exists_fixedPointFree_involutive_iff_even_card :
    (∃ f : α → α, Function.Involutive f ∧ ∀ x, f x ≠ x) ↔ Even (card α) := by
  classical
  constructor
  · rintro ⟨f, hf, hfree⟩
    exact even_card_of_fixedPointFree_involutive f hf hfree
  · rintro ⟨n, hn⟩
    let e : α ≃ Fin n × Bool := equivOfCardEq (by simp [hn]; omega)
    let f : α → α := fun x => e.symm ((e x).1, !(e x).2)
    refine ⟨f, ?_, ?_⟩
    · intro x
      simp [f]
    · intro x hx
      have h := congrArg (fun y => (e y).2) hx
      simp [f] at h

end TauCeti.Fintype

/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import Mathlib.Logic.Equiv.Basic

/-!
# Involutivity under equivalences

The standard conjugation of maps preserves and reflects involutivity.
This is an elementary property of Mathlib's `Equiv.conj`, not a new
conjugation construction.
-/

public section

namespace Equiv

/-- Transporting a self-map across an equivalence preserves and reflects
involutivity, without any finiteness assumption. -/
@[simp] theorem involutive_conj_iff {α : Sort*} {β : Sort*} (e : α ≃ β) (s : α → α) :
    Function.Involutive (e.conj s) ↔ Function.Involutive s := by
  constructor
  · intro h x
    simpa only [conj_apply, symm_apply_apply] using congrArg e.symm (h (e x))
  · intro h x
    simpa only [conj_apply, symm_apply_apply, apply_symm_apply] using
      congrArg e (h (e.symm x))

end Equiv

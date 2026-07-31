/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5

Staged for Tau Ceti.  Mathlib is not the destination (`ForTauCeti/README.md`);
what follows is where this material would have gone on the closed Mathlib track —
an addition to `Mathlib/Algebra/GroupWithZero/Commute.lean`, beside
`Commute.ringInverse_ringInverse`.

Formalized by Claude Opus 5 (claude-opus-5[1m]).
-/

import Mathlib.Algebra.Group.Semiconj.Units
import Mathlib.Algebra.GroupWithZero.Commute

/-! # `Ring.inverse` and semiconjugation

Mathlib states the semiconjugation-respects-inverses fact for `Units`
(`SemiconjBy.units_inv_right`).  Operator-algebra arguments do not get their
invertibility that way: it arrives as `IsUnit` and the inverse is taken with
`Ring.inverse`, so using the `Units` lemma means unfolding through `IsUnit.unit`
by hand at every site.

**That unfolding was written out twice in `DavisKahan/SpectralTheory/`, as the
same six-line `calc` with different letters**, once for `P * N = N * P` and once
for `X * N = M * X`.  A third copy sat in a third theorem of the same file.  This
module is the missing bridge, and it is four lines because the mathematics is
already in Mathlib.
-/

namespace TauCeti

/-- **`Ring.inverse` respects semiconjugation.**

If `a` semiconjugates a unit `n` to a unit `m` — that is, `a * n = m * a` — then
it semiconjugates their inverses.

The commuting case `m = n` is the one that appears most: if `a` commutes with a
unit `n`, it commutes with `n⁻¹`. -/
theorem ringInverse_semiconj {M : Type*} [MonoidWithZero M] {a n m : M}
    (hn : IsUnit n) (hm : IsUnit m) (h : a * n = m * a) :
    a * Ring.inverse n = Ring.inverse m * a := by
  obtain ⟨un, rfl⟩ := hn
  obtain ⟨um, rfl⟩ := hm
  rw [Ring.inverse_unit, Ring.inverse_unit]
  exact SemiconjBy.units_inv_right h

/-- The commuting case: `a` commutes with a unit `n`, hence with `Ring.inverse n`. -/
theorem commute_ringInverse {M : Type*} [MonoidWithZero M] {a n : M}
    (hn : IsUnit n) (h : Commute a n) : Commute a (Ring.inverse n) :=
  ringInverse_semiconj hn hn h

end TauCeti

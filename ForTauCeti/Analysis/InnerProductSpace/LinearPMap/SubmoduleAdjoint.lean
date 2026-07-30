/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5

Staged for Tau Ceti, and ultimately for Mathlib: additions to
`Mathlib/Analysis/InnerProductSpace/LinearPMap.lean`, beside `Submodule.adjoint`.

Added 2026-07-30 under lane `MATHLIB-ADJ-DENSE`.
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap

public section

/-!
# The double adjoint of a submodule

`Submodule.adjoint` sends a submodule of `E × F` to one of `F × E`; it is the
graph-level form of the adjoint of an unbounded operator, and Mathlib's
`LinearPMap.adjoint_graph_eq_graph_adjoint` identifies `Γ(T†)` with
`Γ(T).adjoint`.

Mathlib does not record how the operation composes with itself.  That gap is
what stops the von Neumann theorem — *the adjoint of a closed densely defined
operator is again densely defined* — from being stated, because that proof needs
`g.adjoint.adjoint = g` for a closed graph.

This module supplies the inclusion that holds unconditionally.

## Main results

* `Submodule.le_adjoint_adjoint`: `g ≤ g.adjoint.adjoint`, for **any** submodule.

## The reverse inclusion

`g.adjoint.adjoint ≤ g` is **not** proved here.  It is false without closedness
(the double adjoint is a closed submodule, so it contains the closure of `g`),
and proving it needs an orthogonal projection, hence the `WithLp 2 (E × F)`
inner-product structure that `Submodule.adjoint` is defined through.

The argument, recorded so the next attempt does not have to rediscover the
witness.  Let `g` be closed and `x ∉ g`.  Projecting in `WithLp 2 (E × F)` gives
`y = (y₁, y₂)` orthogonal to `g` with `⟪y, x⟫ ≠ 0`.  Then

`(a, b) := (-y₂, y₁)`

is the separating element of `g.adjoint`:

* `(a, b) ∈ g.adjoint` unfolds, via `Submodule.mem_adjoint_iff`, to
  `∀ (c, d) ∈ g, ⟪d, -y₂⟫ - ⟪c, y₁⟫ = 0`, which is exactly `y ⟂ g`;
* the pairing that `x ∈ g.adjoint.adjoint` would force to vanish is
  `⟪b, x.1⟫ - ⟪a, x.2⟫ = ⟪y₁, x.1⟫ + ⟪y₂, x.2⟫ = ⟪y, x⟫ ≠ 0`.

So the only genuinely fiddly step is transporting `g` into `WithLp 2 (E × F)` to
obtain the projection; the separation itself is the two lines above.
-/

open scoped InnerProductSpace

namespace Submodule

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- **A submodule sits inside its double adjoint.**

This inclusion is unconditional: no closedness, no completeness, and no contact
with the `WithLp 2` structure `Submodule.adjoint` is defined through.  Unfolding
`Submodule.mem_adjoint_iff` twice produces the defining relation of `g` with its
two arguments exchanged, and conjugating exchanges them back. -/
theorem le_adjoint_adjoint (g : Submodule 𝕜 (E × F)) : g ≤ g.adjoint.adjoint := by
  intro x hx
  rw [Submodule.mem_adjoint_iff]
  intro a b hab
  rw [Submodule.mem_adjoint_iff] at hab
  have h := hab x.1 x.2 (by simpa using hx)
  have h2 := congrArg (starRingEnd 𝕜) h
  simp only [map_sub, inner_conj_symm, map_zero] at h2
  exact sub_eq_zero.mpr (sub_eq_zero.mp h2).symm

end Submodule

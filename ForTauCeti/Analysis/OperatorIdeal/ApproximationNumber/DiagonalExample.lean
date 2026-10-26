/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.FiniteDimensional
public import ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm

/-!
# The diagonal acceptance example

The diagonal operator's approximation numbers are its entries. The former local
identity and projection examples were retired in favor of accepted
`ApproximationNumber.MinMax` and `.Projection`; their deletion does not remove
this diagonal result. Its finite-dimensional carrier and explicit basis are
retained here.

## Scope: this is the square case

`TauCeti.diagOp` takes one orthonormal basis on one space, so its source and
target coincide.  The roadmap's example asks for a rectangular coordinate map
**including unequal source and target dimensions**, and that is still open: it
needs the singular values of a rectangular diagonal map, which
`singularValues_diagOp` does not supply.

## Sources

*Follows nothing in particular*: this is a test of the library's own API against
a concrete operator the roadmap names.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForTauCeti`.
* Extraction class: **authored in place**, for Tau Ceti.
* Original authors / copyright: Jon Crall, Claude Opus 5; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Spectra influence: **none** — imports only sibling `ForTauCeti` modules.
-/

public section

namespace ContinuousLinearMap

open Module (finrank)
open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- **Acceptance example: a diagonal operator's approximation numbers are its
diagonal entries.**

For antitone nonnegative `x`, the operator scaling the `i`-th basis direction by
`x i` has `aᵢ = x i`.  This is the acceptance entry that most directly tests
that the abstraction computes: the answer is readable straight off the
definition, so any indexing or ordering error in the `approximationNumber` API
surfaces here rather than in a theorem whose value nobody knows independently.

Proved from the public API in two steps — `approximationNumber_eq_singularValues`
and `TauCeti.singularValues_diagOp` — with the defining infimum never unfolded.

The square/rectangular scope caveat is in this file's module docstring. -/
theorem approximationNumber_diagOp {n : ℕ} (hn : finrank 𝕜 E = n)
    (b : OrthonormalBasis (Fin n) 𝕜 E) {x : Fin n → ℝ}
    (hx_anti : Antitone x) (hx0 : ∀ i, 0 ≤ x i) (i : Fin n) :
    (TauCeti.diagOp b x).toContinuousLinearMap.approximationNumber (i : ℕ) = x i := by
  rw [approximationNumber_eq_singularValues]
  exact TauCeti.singularValues_diagOp hn b hx_anti hx0 i

end ContinuousLinearMap

/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import DavisKahan.FiniteDimensional.DirectRotation

/-!
# Davis--Kahan 1970, Section 4: extremal properties of the direct rotation

Source-numbered names for the Section 4 results.  The mathematics is proved in
`DavisKahan/FiniteDimensional/DirectRotation/`; this file only supplies statements carrying
the paper's numbering, scope and hypotheses, so that the facade can cite them.

## Scope, stated honestly

These are the **finite-dimensional** forms, which is the scope Section 4 is written at.
Infinite-dimensional forms of Propositions 4.1 and 4.3 are proved as well, in
`DavisKahan/MathAhead/Section4/InfiniteProposition41.lean` and
`InfiniteProposition43.lean`.  Both were promoted out of `Experimental/` once their import
closures became admission-free, so `lake build` guards them; they are still **not** aliased
here, because the source facade is numbered at the paper's finite-dimensional scope.  The
`Experimental` exposure through `DavisKahan/Experimental/Frontier/Section4.lean` remains,
and that module still carries `sorry`s of its own.  Proposition 4.2 is already stated at
arbitrary Hilbert-space generality and lives in `Section4BasisAngleEnergy.lean`.

## Proposition 4.4 is excluded, and deliberately

The published Proposition 4.4 asserts the same extremality for the **full** displacement
`1 − W` rather than the restricted one.  This repository contains a compiled
counterexample: an explicit competitor in `ℝ⁴` beats the direct rotation in trace norm
(`shortRotation_fullDisplacement_refuted`, census row `DK-4.4-prop`).  Nothing in this file
should be read as covering it, and anything phrased on the full displacement must be
checked against that configuration.
-/

namespace TauCeti
namespace DavisKahan1970

/-! ## Proposition 4.1 -/

/-- **Davis--Kahan 1970, Proposition 4.1.**  Every singular value of the displacement
restricted to the source subspace is minimized by the direct rotation, over all isometries
carrying `U` onto `V`. -/
alias Proposition4_1 := DavisKahanTheory.singularValues_restrictedDisplacement_le

/-- The direct rotation's restricted-displacement singular values, identified: the
principal-plane chords, and zero past the last nontrivial angle.  This is the value the
minimum in `Proposition4_1` takes. -/
alias Proposition4_1_directRotationValues :=
  DavisKahanTheory.singularValues_restrictedDisplacement_directRotation

/-! ## Corollary 4.1 -/

/-- **Davis--Kahan 1970, Corollary 4.1.**  Singular-value domination passes to every
unitarily invariant norm of the restricted displacement. -/
alias Corollary4_1 := DavisKahanTheory.uiNorm_restrictedDisplacement_le

/-- Corollary 4.1 read as a minimality statement about the direct rotation. -/
alias Corollary4_1_minimizer :=
  DavisKahanTheory.directRotation_minimizes_restrictedDisplacement_uiNorm

/-! ## Proposition 4.3 -/

/-- **Davis--Kahan 1970, Proposition 4.3, Ky Fan root.**  The prefix sums of the singular
values of the squared displacement `(1 − W)⋆(1 − W)` are minimized by the direct rotation.

Ky Fan level is the honest scope: the *individual* singular values are **not** dominated.
Pointwise domination would imply Proposition 4.4, which this repository refutes.  See the
docstring of `DavisKahan/Experimental/Frontier/Section4.lean`'s Proposition 4.3 for the
refuting configuration. -/
alias Proposition4_3_kyFan := DavisKahanTheory.directRotation_displacementSquare_kyFan

/-- **Davis--Kahan 1970, Proposition 4.3.**  Every unitarily invariant norm of the squared
displacement is minimized by the direct rotation. -/
alias Proposition4_3 := DavisKahanTheory.directRotation_displacementSquare_uiNorm

/-- Proposition 4.3 read as a minimality statement about the direct rotation. -/
alias Proposition4_3_minimizer :=
  DavisKahanTheory.directRotation_minimizes_displacementSquare_uiNorm

end DavisKahan1970
end TauCeti

/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import DavisKahan.FiniteDimensional.DirectRotation
import DavisKahan.MathAhead.Section4.All

/-!
# Davis--Kahan 1970, Section 4: extremal properties of the direct rotation

Source-numbered names for the Section 4 results.  The mathematics is proved in
`DavisKahan/FiniteDimensional/DirectRotation/`; this file only supplies statements carrying
the paper's numbering, scope and hypotheses, so that the facade can cite them.

## Scope, stated honestly

**Corrected 2026-08-07.**  This docstring used to say that the finite-dimensional forms
"is the scope Section 4 is written at".  That is not what the paper says.  Section 4 opens

> We shall make the hypotheses of Theorem 3.1 and Corollary 3.1 (leaving to the reader the
> modifications entailed in the absence of compactness).

and then states its propositions over infinite orthonormal sequences `v₁, v₂, …` and
infinite sums `∑_{k=1}^∞`.  So the printed scope is an arbitrary (separable) Hilbert space
under Corollary 3.1's compactness hypothesis, with finite dimensionality only the special
case that standing assumption 1 of Section 1 always allows.  The finite-dimensional aliases
below are therefore *specializations*, not the source scope, and the infinite-dimensional
aliases in the next section are the ones that carry the printed generality.

Both infinite-dimensional modules were promoted out of `Experimental/` once their import
closures became admission-free, so `lake build` guards them.  Proposition 4.2 is already
stated at arbitrary Hilbert-space generality and lives in `Section4BasisAngleEnergy.lean`.
The `Experimental` exposure through `DavisKahan/Experimental/Frontier/Section4.lean`
remains, and that module still carries `sorry`s of its own.

One axis is still open at source scope: every declaration here is over
`InnerProductSpace ℂ`, while the paper's standing assumption 1 is "real or complex".  See
the `real-scalar-infinite-dimensional-scope` blocker and the `scope_gap` fields on rows
`DK-4.1-prop`, `DK-4.1-cor` and `DK-4.3-prop`.

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

/-! ## The printed infinite-dimensional scope

The aliases above are the finite-dimensional specializations.  These are the forms at the
generality Section 4 is actually written at; see the scope note in the module docstring. -/

/-- **Davis--Kahan 1970, Proposition 4.1, at the printed scope.**  In an arbitrary complex
Hilbert space, for every unitary `W` carrying `U` onto `V`, every approximation number of
the displacement restricted to `U` is minimized by the direct rotation.

This is the printed statement — "among all such `V`, the singular values `λ₁ ≥ λ₂ ≥ ⋯` of
`(1 − V)|_{PH}` are all minimized when `V = U`" — with approximation numbers standing in
for singular values, which is the correct reading past the compact case.  It needs neither
`[FiniteDimensional]` nor the compactness of `P Q̃ P`, so it is strictly more general than
the hypotheses Section 4 inherits from Corollary 3.1. -/
alias Proposition4_1_infiniteDimensional :=
  DavisKahan.Experimental.MathAhead.Section4.proposition4_1_source_approximationNumbers

/-- **Davis--Kahan 1970, Proposition 4.3, at the printed scope.**  In an arbitrary complex
Hilbert space, the Ky Fan prefix sums of `(1 − W)⋆(1 − W)` are minimized by the direct
rotation, over all unitaries `W` carrying `U` onto `V`.

Ky Fan level is the honest scope here for the same reason as in `Proposition4_3_kyFan`:
pointwise domination of the individual singular values would imply Proposition 4.4, which
this repository refutes. -/
alias Proposition4_3_infiniteDimensional :=
  DavisKahan.Experimental.MathAhead.Section4.proposition4_3_squaredDisplacement_kyFan_scratch

/-! ### Proposition 4.3 at the printed "every unitarily invariant norm" scope

The alias above stops at Ky Fan, which is where its proof stops.  The printed
clause is about every unitarily invariant norm, and in infinite dimensions the
carrier of that phrase is an arbitrary Ky-Fan-dominant symmetric operator ideal
family, exactly as for Corollary 4.1.  The promotion is
`KyFanDominantIdealFamily.majorization_mem_and_gauge_le`, whose hypothesis is
the Ky Fan domination this alias supplies.

**This is not pointwise domination and must never be replaced by it.**  Fan
dominance constrains the *prefix sums* of the approximation numbers; the
individual approximation numbers are not dominated, and asserting that they were
would contradict this repository's compiled refutation of Proposition 4.4. -/

section IdealGauge

open DavisKahan (IsUniformlyAcute)
open DavisKahan.Experimental (spectraDirectRotation)
open DavisKahan.Experimental.ExactSinTheta (KyFanDominantIdealFamily)

universe v

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- **Davis--Kahan 1970, Proposition 4.3, at the printed scope, for every
unitarily invariant norm.**

In an arbitrary complex Hilbert space, for every Ky-Fan-dominant symmetric ideal
family of operators, the squared full displacement `(1 − W)⋆(1 − W)` of the
direct rotation lies in the ideal and its gauge is least among all unitaries `W`
carrying `U` onto `V`.  Membership of the minimizer is **concluded**, not
assumed; only the competitor is assumed to lie in the ideal.

This is `Proposition4_3_infiniteDimensional` promoted through
`KyFanDominantIdealFamily.majorization_mem_and_gauge_le`.  The promotion consumes
Ky Fan prefix sums only: no pointwise approximation-number domination is claimed
here, and none is true. -/
theorem Proposition4_3_infiniteDimensional_idealGauge
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) (W : H →L[ℂ] H)
    (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * DavisKahan.projection U = DavisKahan.projection V * W)
    (hWmem : N.Mem ((1 - star W) * (1 - W))) :
    N.Mem ((1 - star (spectraDirectRotation U V hacute)) *
        (1 - spectraDirectRotation U V hacute)) ∧
      N.gauge ((1 - star (spectraDirectRotation U V hacute)) *
          (1 - spectraDirectRotation U V hacute)) ≤
        N.gauge ((1 - star W) * (1 - W)) :=
  N.majorization_mem_and_gauge_le hWmem
    (Proposition4_3_infiniteDimensional U V hacute W hWunitary hWmap)

end IdealGauge

end DavisKahan1970
end TauCeti

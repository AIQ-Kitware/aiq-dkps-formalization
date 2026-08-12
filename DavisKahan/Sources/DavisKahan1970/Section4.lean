/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import DavisKahan.FiniteDimensional.DirectRotation
import DavisKahan.Geometry.Polar.RestrictedDisplacementExtremal
import DavisKahan.Geometry.Polar.DisplacementSquareExtremal
import DavisKahan.Geometry.Angle.BasisAngleEnergy

/-!
# Davis--Kahan 1970, Section 4: extremal properties of the direct rotation

Source-numbered names for the Section 4 results.  Section 4 inherits the
matched-crossed-defect and compact-angle hypotheses of Theorem 3.1 and
Corollary 3.1.  The source statements use infinite angle sequences and
orthonormal bases; finite-dimensional aliases remain available as
specializations.

The arbitrary-dimensional complex API provides the approximation-number form
of Proposition 4.1 for both the canonical acute direct rotation and a chosen
matched-defect completion.  Proposition 4.2 uses the approximation-number
principal-sine sequence of `P_{Vᗮ}|_U`, so its extended-real sum includes the
case where the source right-hand side is infinite.  `Section4Real.lean` provides
the corresponding real Proposition 4.2 statement and the established real
Section 4 endpoints.

Proposition 4.4 is represented by its compiled counterexample, as required by
the repository's source-coverage convention for a false printed claim.
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

/-! ## Infinite-dimensional source forms

The aliases above are finite-dimensional specializations.  The declarations
below carry the arbitrary-dimensional source variables. -/

/-- **Davis--Kahan 1970, Proposition 4.1, acute arbitrary-dimensional form.**
For every unitary `W` carrying `U` onto `V`, every approximation number of the
restricted displacement is bounded below by the canonical acute direct
rotation.  The chosen-defect declaration below carries the full nonacute scope
of the paper. -/
alias Proposition4_1_infiniteDimensional :=
  DavisKahan.Section4.proposition4_1_source_approximationNumbers


/-- **Proposition 4.1 at the nonacute compact scope inherited from Corollary
3.1.**  A crossed-defect isometry selects the direct rotation when `π/2`
principal-angle blocks are present. -/
alias Proposition4_1_infiniteDimensional_nonacute :=
  DavisKahan.Section4.proposition4_1_nonacute_source_approximationNumbers

section Corollary4_1Infinite

open DavisKahan.ExactSinTheta (KyFanDominantIdealFamily)

universe v

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- **Davis--Kahan 1970, Corollary 4.1 at the matched-crossed-defect scope.**
Approximation-number minimality of a chosen direct rotation promotes to every
Ky-Fan-dominant unitarily invariant ideal gauge. -/
theorem Corollary4_1_infiniteDimensional_nonacute
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (J : DavisKahan.halmosSourceDefect U V ≃ₗᵢ[ℂ]
      DavisKahan.halmosTargetDefect U V)
    (W : H →L[ℂ] H) (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * DavisKahan.projection U = DavisKahan.projection V * W)
    (hWmem : N.Mem ((1 - W) ∘L DavisKahan.projection U)) :
    N.Mem ((1 - DavisKahan.nonacuteDirectRotation
          U V J) ∘L DavisKahan.projection U) ∧
      N.gauge ((1 - DavisKahan.nonacuteDirectRotation
          U V J) ∘L DavisKahan.projection U) ≤
        N.gauge ((1 - W) ∘L DavisKahan.projection U) :=
  DavisKahan.Section4.restrictedDisplacement_idealGauge_le N
    (DavisKahan.Section4.nonacute_restrictedDisplacementDominance
      U V J W hWunitary hWmap) hWmem

end Corollary4_1Infinite

/-- **Davis--Kahan 1970, Proposition 4.2, at the printed infinite-dimensional
scope.**  The principal sines are the approximation numbers of
`P_{Vᗮ}|_U`; the extended-real sum includes the case where the printed right
side is infinite. -/
alias Proposition4_2_infiniteDimensional :=
  DavisKahan.Section4.tsum_displacementAngleSineSq_ge_tsum_sq_sin_principalAngleSequence

/-- **Davis--Kahan 1970, Proposition 4.3, at the printed scope.**  In an arbitrary complex
Hilbert space, the Ky Fan prefix sums of `(1 − W)⋆(1 − W)` are minimized by the direct
rotation, over all unitaries `W` carrying `U` onto `V`.

Ky Fan level is the honest scope here for the same reason as in `Proposition4_3_kyFan`:
pointwise domination of the individual singular values would imply Proposition 4.4, which
this repository refutes. -/
alias Proposition4_3_infiniteDimensional :=
  DavisKahan.Section4.proposition4_3_squaredDisplacement_kyFan

/-! ### Proposition 4.3 and unitarily invariant gauges

The alias above stops at Ky Fan, which is where its proof stops.  The printed
clause is about every unitarily invariant norm, and in infinite dimensions the
carrier of that phrase is an arbitrary Ky-Fan-dominant symmetric operator ideal
family, exactly as for Corollary 4.1.  The promotion is
`KyFanDominantIdealFamily.majorization_mem_and_gauge_le`, whose hypothesis is
the Ky Fan domination this alias supplies.

Fan dominance constrains the prefix sums of the approximation numbers.  This is
the source quantity used by the unitarily invariant gauge statement and is
consistent with the compiled Proposition 4.4 counterexample. -/

section IdealGauge

open DavisKahan (IsUniformlyAcute)
open DavisKahan (spectraDirectRotation)
open DavisKahan.ExactSinTheta (KyFanDominantIdealFamily)

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

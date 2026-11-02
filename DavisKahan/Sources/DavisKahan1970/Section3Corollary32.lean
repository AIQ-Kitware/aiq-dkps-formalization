/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Claude Opus 5
-/

module

public import TauCeti.Analysis.InnerProductSpace.Projection.AngleOperator

public import DavisKahan.Geometry.Polar.Section3Elementary
public import DavisKahan.InfiniteDimensional.SinTheta.General

/-!
# Davis--Kahan 1970, Corollary 3.2

Interchanging the two subspaces leaves the angle operator unchanged and reverses
the canonical quarter-turn:

`sin Θ (V, U) = sin Θ (U, V)`  and  `W (V, U) = W (U, V)⋆`.

The quarter-turn half is grounded by `:=` on
`Geometry/Polar/Section3Elementary.lean`, which owns the reversal.  The angle
half is two lines of projection algebra and is proved here: the two projections
enter the angle operator only through their difference, and the absolute value
is insensitive to its sign.
-/

public section

open scoped InnerProductSpace ComplexOrder

namespace TauCeti
namespace DavisKahan1970

open TauCeti.DavisKahan

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
  [V.HasOrthogonalProjection]

/-- **Davis--Kahan 1970, Corollary 3.2, quarter-turn half.**

Interchanging the subspaces reverses the canonical quarter-turn. -/
theorem corollary3_2_reversal_form
    (hacute : IsUniformlyAcute U V) :
    spectraDirectRotation V U (IsUniformlyAcute.symm hacute) =
      star (spectraDirectRotation U V hacute) :=
  corollary3_2_reversal_completed U V hacute

/-- **Davis--Kahan 1970, Corollary 3.2, angle half.**

Interchanging the subspaces leaves the angle operator unchanged.  The two
projections enter the angle operator only through their difference, and the
absolute value is insensitive to its sign. -/
theorem corollary3_2_sinAngleOperator_symm :
    (Submodule.sinAngleOperator V U) = (Submodule.sinAngleOperator U V) :=
  Submodule.sinAngleOperator_comm U V

/-- **Davis--Kahan 1970, Corollary 3.2**, both halves in one statement: swapping
the pair leaves the angle operator unchanged and reverses the quarter-turn. -/
theorem corollary3_2_reversal
    (hacute : IsUniformlyAcute U V) :
    (Submodule.sinAngleOperator V U) = (Submodule.sinAngleOperator U V) ∧
      spectraDirectRotation V U (IsUniformlyAcute.symm hacute) =
        star (spectraDirectRotation U V hacute) :=
  ⟨corollary3_2_sinAngleOperator_symm U V, corollary3_2_reversal_form U V hacute⟩

end DavisKahan1970
end TauCeti

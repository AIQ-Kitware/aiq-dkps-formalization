/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/
import DavisKahan.Sources.DavisKahan1970.Section3Proposition35

/-!
# Dependency audit for Davis--Kahan 1970, Proposition 3.5

The paper states Proposition 3.5 for real or complex Hilbert spaces without a
finite-dimensional restriction.  This audit checks the arbitrary-dimensional
`RCLike` source surface and instantiates its commutation theorem over both real
and complex Hilbert spaces, so neither scalar field is covered merely by prose.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan1970
namespace Section3Audit

open DavisKahan.Experimental.MathAhead.HiddenFoundations

#check proposition3_5_angleOperator
#check proposition3_5_directRotation
#check proposition3_5_quarterTurn
#check proposition3_5_angleEigenspace
#check proposition3_5_directRotation_resolution
#check proposition3_5_commutations
#check proposition3_5_eigenvector_angle
#check proposition3_5_angleEigenspace_eq_fixedCosineSubspace
#check proposition3_5_angleEigenspace_uniqueMaximal

#print axioms proposition3_5_directRotation_resolution
#print axioms proposition3_5_commutations
#print axioms proposition3_5_eigenvector_angle
#print axioms proposition3_5_angleEigenspace_eq_fixedCosineSubspace
#print axioms proposition3_5_angleEigenspace_uniqueMaximal

section Real

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]
variable (U V : Submodule ℝ H) [U.HasOrthogonalProjection]
  [V.HasOrthogonalProjection]

example (hacute : TauCeti.IsAcute U V) :
    Commute (proposition3_5_angleOperator U V) (projection U) ∧
      Commute (proposition3_5_angleOperator U V) (projection V) ∧
      Commute (proposition3_5_angleOperator U V) (proposition3_5_quarterTurn U V) ∧
      Commute (proposition3_5_angleOperator U V) (proposition3_5_directRotation U V) :=
  proposition3_5_commutations U V hacute

end Real

section Complex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
  [V.HasOrthogonalProjection]

example (hacute : TauCeti.IsAcute U V) :
    Commute (proposition3_5_angleOperator U V) (projection U) ∧
      Commute (proposition3_5_angleOperator U V) (projection V) ∧
      Commute (proposition3_5_angleOperator U V) (proposition3_5_quarterTurn U V) ∧
      Commute (proposition3_5_angleOperator U V) (proposition3_5_directRotation U V) :=
  proposition3_5_commutations U V hacute

end Complex

end Section3Audit
end DavisKahan1970
end TauCeti

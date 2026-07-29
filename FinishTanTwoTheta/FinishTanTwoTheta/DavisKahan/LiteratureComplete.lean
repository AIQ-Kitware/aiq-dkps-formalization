/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Sources.DavisKahan1970.TanTwoTheta
import DavisKahan.Riccati.UnboundedAdjointRiccati
import DavisKahan.Sylvester.Unbounded.OrderedCutoff

/-!
# Literature-complete `tan 2Theta` surface

This module is the completed, source-faithful endpoint of the temporary
`FinishTanTwoTheta` library.

It deliberately distinguishes three scopes that the distilled literature and
current formalization actually prove:

* the sharp finite-dimensional rectangular unitarily-invariant-norm theorem;
* the sharp ambient-Hilbert operator-norm theorem, including the acute branch;
* the infinite-dimensional finite-carrier ideal theorem and the genuine
  unbounded Sylvester equation with its explicit commutator defect.

The unrestricted sharp infinite-dimensional ideal theorem is not exported:
the approximate graph-domain singular-family route used by the old completion
workspace is invalid, and the genuine Sylvester equation has a nonzero defect
in general.  Excluding that unsupported statement is part of completing the
proof surface correctly, not a weakening of any theorem proved here.
-/

namespace TauCeti
namespace DavisKahan
namespace FinishTanTwoTheta

/-! ## Davis--Kahan Section 7: sharp finite-dimensional norm scope -/

/-- Equation (7.6) for every rectangular unitarily invariant norm. -/
alias literature_tanTwoTheta_uiNorm :=
  TauCeti.DavisKahan1970.tanTwoTheta_uiNorm

/-- Ky Fan prefix root of the finite-dimensional Section 7 theorem. -/
alias literature_tanTwoTheta_kyFan :=
  TauCeti.DavisKahan1970.tanTwoTheta_kyFan

/-- Paired-singular-vector scalar inequality used by the Section 7 proof. -/
alias literature_tanTwoTheta_pairedSingularVector_scalar :=
  TauCeti.DavisKahan1970.tanTwoTheta_pairedSingularVector_scalar

/-! ## GKMV/Section 8: sharp operator norm and acute branch -/

/-- Sharp ambient-Hilbert operator-norm `tan 2Theta` theorem with the strict
quarter-turn branch. -/
alias literature_tanTwoTheta_sharp_opNorm :=
  TauCeti.DavisKahan1970.tanTwoTheta_sharp_opNorm

/-- Off-diagonal spectral repulsion that selects the acute branch. -/
alias literature_tanTwoTheta_spectral_repulsion :=
  TauCeti.DavisKahan1970.tanTwoTheta_spectral_repulsion

/-! ## Infinite-dimensional sharp theorem at the proved finite-carrier scope -/

/-- Sharp ideal membership and gauge estimate on an arbitrary Hilbert space
when the invariant graph configuration has finite carrier. -/
alias literature_tanTwoTheta_uiIdeal_finiteCarrier :=
  TauCeti.DavisKahan1970.tanTwoTheta_uiIdeal_infinite

/-- Ky Fan approximation-number root of the finite-carrier sharp theorem. -/
alias literature_tanTwoTheta_kyFan_finiteCarrier :=
  TauCeti.DavisKahan1970.tanTwoTheta_kyFan_infinite

/-- Representative-free finite-carrier theorem stated directly in the
transformed approximation numbers of the graph coordinate. -/
alias literature_tanTwoTheta_kyFan_doubleAngleTangent_finiteCarrier :=
  TauCeti.DavisKahan1970.tanTwoTheta_kyFan_doubleAngleTangent_infinite

/-! ## Genuine unbounded spectral-subspace companions -/

/-- Unbounded operator-norm theorem for genuine spectral subspaces, with the
source-faithful extended-cosine denominator and explicit quarter-acuteness. -/
alias literature_unbounded_tanTwoTheta_opNorm :=
  TauCeti.DavisKahan1970.unbounded_tanTwoTheta_opNorm

/-- Unbounded unitary-invariant-ideal theorem at the proved non-sharp
extended-cosine denominator. -/
alias literature_unbounded_tanTwoTheta_uiNorm :=
  TauCeti.DavisKahan1970.unbounded_tanTwoTheta_uiNorm

/-! ## The exact unbounded Riccati/Sylvester endpoint -/

/-- The actual unbounded Sylvester equation satisfied by
`X (1 - X†X)⁻¹`, with the explicit bounded commutator defect. -/
alias literature_doubleAngleTangent_sylvesterEquation :=
  TauCeti.DavisKahanExt.doubleAngleTangent_sylvesterEquation

/-- Ordered two-unbounded Sylvester Ky Fan estimate consumed by the defect
form of the `tan 2Theta` theorem. -/
alias literature_kyFan_unbounded_sylvester :=
  TauCeti.DavisKahan.Experimental.ExactSinTheta.kyFan_unbounded_sylvester_le_of_semibounded_direct

/-- Coupling-only norm bound for the Riccati Gram commutator appearing in the
unbounded Sylvester defect. -/
alias literature_riccatiGramCommutator_norm_le :=
  TauCeti.DavisKahanExt.norm_riccatiGramCommutator_le

end FinishTanTwoTheta
end DavisKahan
end TauCeti

/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/

import DavisKahan.FiniteDimensional.SinTheta.Perturbation
import DavisKahan.FiniteDimensional.DoubleAngle.SinTheta
import DavisKahan.FiniteDimensional.TanTheta.Vector
import DavisKahan.FiniteDimensional.DoubleAngle.TanTheta

/-!
# The proof-complete finite Davis--Kahan Part III quartet

This module is the stable import surface for the four headline subspace
perturbation theorems from Davis--Kahan Part III.

The norm scope is deliberately faithful to the proved and source-checked
statements:

* `sin Theta` is available for every unitarily invariant norm;
* `sin 2 Theta` is available for every unitarily invariant norm;
* `tan Theta` is the pole-free, per-vector spectral-norm theorem, with no
  dimension comparison between the trial and invariant subspaces;
* `tan 2 Theta` is the sharp operator-norm sectorial theorem, including the
  strict quarter-turn conclusion.

The sharp factor-one projector-difference theorem is exposed here as the
canonical companion of the quartet, in both the reducing-subspace and the
canonical spectral-subspace forms.  Canonical spectral-subspace wrappers for
the directed `sin Θ` bound in every unitarily invariant norm are provided by
`uiNorm_spectralSubspace_directed_sinTheta_le`.

The newer files `DavisKahan/Experimental/FiniteDimensional/TanTheta/GraphOperator.lean` and
`DavisKahan/Experimental/FiniteDimensional/DoubleAngle/TanTheta.lean` contain proposed residual, graph, and
all-unitarily-invariant-norm strengthenings.  Those declarations are useful
future extensions, but they are not prerequisites for calling the classical
finite Part III quartet complete.
-/

namespace ForMathlib
namespace DavisKahanTheory

/-- The finite Part III `sin Theta` theorem for every unitarily invariant norm.

This is an exact canonical alias of
`UnitarilyInvariantNorm.apply_starProjection_comp_starProjection_le`.
Its proof is the already-verified ordered Sylvester argument followed by the
ideal property of the chosen unitarily invariant norm.  Downstream users
should import this module rather than depending on the historical file layout.
-/
alias partIII_sinTheta_uiNorm :=
  UnitarilyInvariantNorm.apply_starProjection_comp_starProjection_le

/-- The finite Part III `sin 2 Theta` theorem for every unitarily invariant
norm.

This is an exact canonical alias of
`UnitarilyInvariantNorm.sin_two_theta_starProjection_le`.  The proof reflects
the reference operator through the perturbed reducing subspace, applies the
Part III `sin Theta` theorem to the reflected pair, and uses unitary invariance
to identify the cross block with one half of `sin 2 Theta`.
-/
alias partIII_sinTwoTheta_uiNorm :=
  UnitarilyInvariantNorm.sin_two_theta_starProjection_le

/-- The finite Part III `tan Theta` theorem in pole-free per-vector form.

This is an exact canonical alias of `ForMathlib.tan_theta_le`.  The theorem
keeps the cosine factor on the right-hand side, so transversality is a
conclusion rather than a premise and no inverse tangent operator is formed.
The proof uses compression coercivity, the complementary spectral strip, and
the Ritz residual estimate.
-/
alias partIII_tanTheta_vector :=
  ForMathlib.tan_theta_le

/-- The finite Part III `tan 2 Theta` theorem in its sharp operator-norm form.

This is an exact canonical alias of `ForMathlib.tan_two_theta_norm_sub_le`.
Besides the sharp factor-two estimate, the conclusion proves that the maximal
angle is strictly below `pi / 4`, so the tangent never encounters its pole.
The proof is the finite sectorial/reflection argument for an off-diagonal
perturbation.
-/
alias partIII_tanTwoTheta_opNorm :=
  ForMathlib.tan_two_theta_norm_sub_le

/-- The sharp factor-one finite projector-difference theorem, the canonical
companion of the Part III quartet.

This is an exact canonical alias of `opNorm_starProjection_sub_le`: for
symmetric `A, B` with reducing subspaces carrying two-sided spectral gaps,
`‖P_U − P_W‖ ≤ ε / g` with no rank hypothesis and no factor-two loss. -/
alias projector_difference_opNorm :=
  opNorm_starProjection_sub_le

/-- The sharp projector-difference theorem for the canonical spectral
subspaces, an exact canonical alias of `opNorm_spectralSubspace_sub_le`. -/
alias spectralProjector_difference_opNorm :=
  opNorm_spectralSubspace_sub_le

end DavisKahanTheory
end ForMathlib

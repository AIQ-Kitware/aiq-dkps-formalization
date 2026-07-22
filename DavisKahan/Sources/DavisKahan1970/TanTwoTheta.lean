/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
import DavisKahan.FiniteDimensional.DoubleAngle.TanTheta
import DavisKahan.TanTwoTheta.UnboundedIdeal
import DavisKahan.TanTwoTheta.Unbounded

/-!
# Literal Davis--Kahan 1970 Section 7 tangent-double-angle surface

Source anchor: Section 7, equation (7.6) and the following argument, together
with the Section 2 statement `DK-tan2` and the Section 8 acute-branch
conclusion of Theorem 8.1.

## Audited source scope

The source assumes the perturbation is fully off-diagonal with respect to the
unperturbed splitting (`P H P = 0` and `P^⊥ H P^⊥ = 0`) and that the two
diagonal spectral blocks are separated by `δ`; the conclusion is
`δ · ‖tan 2Θ‖ ≤ 2 ‖H‖` together with the strict quarter-turn branch
`Θ < π/4`.  The source text develops the argument through paired singular
vectors, claiming every unitary-invariant norm.

## What is compiled, at which scope

* `tanTwoTheta_sharp_opNorm` — the sharp subspace-level theorem at operator
  norm, on an **arbitrary inner-product space over any `RCLike` field** (no
  finite-dimensionality, no completeness): form gap `[a, b]`-split on the
  `T`-invariant pair, mirrored bounds for the perturbed pair, off-diagonal
  perturbation of norm `ε`.  The conclusion is pole-free and carries the
  Section 8 acute branch explicitly: with `t = ‖P_U - P_V‖ = sin θ_max`,
  `t² < 1/2` and `(b - a) sin 2θ_max ≤ 2 ε cos 2θ_max` — together
  `tan 2θ_max ≤ 2ε/(b - a)`, with the sharp constant.
* `tanTwoTheta_spectral_repulsion` — an off-diagonal perturbation admits no
  eigenvalue in the open form gap; this is the source's mechanism keeping the
  selected branch acute.
* unbounded operator-norm and ideal-gauge companions with genuine spectral
  subspaces, under an explicit quarter-acuteness hypothesis and with the
  non-sharp extended-cosine denominator `1 - 2 g²`.

## What remains open (recorded, not claimed)

1. The **arbitrary unitary-invariant norm** form
   `δ · N(tan 2Θ) ≤ 2 N(H)` is not certified at any scope.  A numerical Ky
   Fan sweep (40000 randomized finite configurations, all prefix sums, true
   spectral gap) found no violation and located equality only at the sharp
   `2×2` model, so the source claim is plausible; certifying it requires the
   source's paired-singular-vector argument for equation (7.6), which is not
   yet formalized.  It must not be advertised until compiled.
2. The sharp Riccati route
   (`quarterAcuteAngularCoordinate_sharp_bound_of_orderedInternalGap` and its
   family under `Experimental/InfiniteDimensional/TanTwoTheta/`) currently
   depends on the Section 8 continuation modules and the
   `GraphSubspace`/`Ideals.Symmetric`/`Sylvester.Resolvent` modules, which do
   not compile at present; that repair belongs to the Section 8 ownership
   area and is deliberately not attempted here.
-/

namespace ForMathlib
namespace DavisKahan1970

/-! ## The sharp subspace theorem with the acute branch -/

/-- **Davis--Kahan 1970, `tan 2Θ` theorem, sharp subspace form at operator
norm, with the Section 8 acute branch.**  Ambient scope: any inner-product
space over any `RCLike` field.  Conclusion: `sin² θ_max < 1/2` and
`(b - a) sin 2θ_max ≤ 2 ε cos 2θ_max`, i.e. `tan 2θ_max ≤ 2ε/(b - a)` with
the strict quarter-turn branch. -/
alias tanTwoTheta_sharp_opNorm := ForMathlib.tan_two_theta_norm_sub_le

/-- **Spectral repulsion for off-diagonal perturbations**: no eigenvalue
enters the open form gap.  This is the source's reason the selected branch
stays acute. -/
alias tanTwoTheta_spectral_repulsion :=
  ForMathlib.eigenvalue_notMem_gap_of_diagonal_form

/-! ## Unbounded genuine-spectral-subspace companions

`A` is an unbounded self-adjoint closed operator, `H` a bounded self-adjoint
perturbation, and both subspaces are genuine spectral subspaces.  These
companions divide the sharp `sin 2Θ` estimate by the extended double-angle
cosine, so their constant carries the non-sharp denominator `1 - 2 g²` with
`g` the directed gap; quarter-acuteness is an explicit hypothesis rather than
a derived branch conclusion. -/

/-- Unbounded operator-norm `tan 2Θ` estimate with the extended-cosine
denominator, under explicit quarter-acuteness. -/
alias unbounded_tanTwoTheta_opNorm :=
  DavisKahan.Experimental.SpectraBridge.tanTwoTheta_addBounded_of_spectrum_gap

/-- Set-localized interval/exterior form of the unbounded operator-norm
estimate. -/
alias unbounded_tanTwoTheta_intervalExterior_opNorm :=
  DavisKahan.Experimental.SpectraBridge.tanTwoTheta_addBounded_of_intervalExterior

/-- The ideal-theoretic tangent companion of the reflected overlap block. -/
alias tanTwoThetaBlock :=
  DavisKahan.Experimental.SpectraBridge.tanTwoThetaIdealBlock

/-- Rectangular ideal-gauge membership and estimate for the tangent
companion block. -/
alias tanTwoThetaBlock_mem_and_gauge_le :=
  DavisKahan.Experimental.SpectraBridge.tanTwoThetaIdealBlock_mem_and_gauge_le

/-- Unbounded `tan 2Θ` estimate at rectangular ideal-gauge scope. -/
alias unbounded_tanTwoTheta_gauge :=
  DavisKahan.Experimental.SpectraBridge.tanTwoTheta_addBounded_gauge_of_spectrum_gap

/-- Unbounded `tan 2Θ` estimate for every source unitary-invariant ideal
family. -/
alias unbounded_tanTwoTheta_uiNorm :=
  DavisKahan.Experimental.SpectraBridge.tanTwoTheta_addBounded_unitaryInvariant_of_spectrum_gap

/-- Set-localized interval/exterior form at unitary-invariant ideal scope. -/
alias unbounded_tanTwoTheta_intervalExterior_uiNorm :=
  DavisKahan.Experimental.SpectraBridge.tanTwoTheta_addBounded_unitaryInvariant_of_intervalExterior

end DavisKahan1970
end ForMathlib

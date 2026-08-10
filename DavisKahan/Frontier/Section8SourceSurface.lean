/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import DavisKahan.Frontier.Section8SourceDictionary
import DavisKahan.Frontier.Section8SourceTheorem82
import DavisKahan.Frontier.Section8SourceTheorem82Real

/-!
# Davis--Kahan 1970 Section 8: the production source surface

The final, dependency-safe facade for Section 8.  Every printed claim of the
section is reachable from here under a source-numbered name in

    `TauCeti.DavisKahan1970.Section8`.

## Why this module and not `Sources/DavisKahan1970/Section8/SourceSurface.lean`

That file is the *low-level* facade: it names the results that live upstream of
the analytic Frontier layer, and `DavisKahan/Frontier/Section8.lean` imports it.
Section 8's analytic content -- the canonical gap circle, the connectedness
bootstrap of Theorem 8.2, the Krein completion, the sandwich majorization --
lives downstream of it, so it cannot import Frontier without creating an import
cycle.  This module is that downstream leaf.  Both are reachable from
`DavisKahan.All`, this one through `DavisKahan.Frontier.All`.

Nothing was relocated to build this: the low-level facade keeps its contents and
its stale status prose has been corrected in place.

## The printed section, claim by claim

**Theorem 8.1, the characterization and the branch.**

* `theorem8_1_source` -- existence of the canonical branch `Q`, from the printed
  hypotheses alone: `A` self-adjoint, `P` reduces `A`, the `P` block below `α`,
  the `Pᗮ` block above `α + δ`, and `H` self-adjoint and fully off-diagonal.
  Delivers full spectral repulsion, both sharp form bounds, both spectral
  orientations, and the *strict* quarter-angle bound.
* `theorem8_1_source_characterization` -- the printed `iff` between the closed
  condition `Θ ≤ π/4` and `Λ₀ ≤ α`, `Λ₁ ≥ α + δ`.
* `theorem8_1_source_uniqueness` -- "there always exists a reducing projector
  `Q` with these properties" is sharpened: it is unique.

**Theorem 8.1(i).**  `theorem8_1_upperCompressionRepulsion_source` and
`theorem8_1_lowerCompressionRepulsion_source`, the printed
`A₁ - α ≤ C₁(Λ₁ - α)C₁` on the `Pᗮ` block and its mirror
`(α + δ) - A₀ ≤ C₀((α + δ) - Λ₀)C₀` on the `P` block.

**Theorem 8.1(ii).**  `theorem8_1_upperApproximationRepulsion_source` and
`theorem8_1_lowerApproximationRepulsion_source` in the dimension-free
approximation-number form, and
`theorem8_1_upperApproximationRepulsion_angle_source` /
`theorem8_1_lowerApproximationRepulsion_angle_source` with the printed factor
written as a principal cosine.  The printed "and natural infinite-dimensional
extensions" is delivered: the Weyl step used here is dimension-free, so the
approximation-number forms carry no finite-dimensionality hypothesis at all.

**Theorem 8.1(iii).**  `theorem8_1_upperSymmetricGaugeRepulsion_angle_source`
and `theorem8_1_lowerSymmetricGaugeRepulsion_angle_source`, quantified over
**every** symmetric gauge, with the printed right-hand side
`(λ_i - α) cos²θ_i`.  The underlying weak majorizations
(`theorem8_1_upperWeightedWeakMajorization_source` and its lower companion) are
stronger than any single gauge inequality and are exported too.  The paper's
increasing index order is available as the `..._rev_source` wrappers.

**Theorem 8.2.**  `theorem8_2_source` is the whole printed theorem: both
`sin 2Θ` estimates and the strict quarter angle, under either printed smallness
alternative and the Section 1 standing convention (1.5).  The two alternatives
are separately available, and so is the strongest dimension-free form:

* `theorem8_2_branch_source_directed` -- `directedGap P Q < √2/2` from the
  explicit printed hypotheses **alone**, with no dimension convention.  This is
  *not* superseded by `theorem8_2_source`; see `Section8SourceTheorem82.lean`
  for why the symmetric reading needs (1.5) and why the cardinal form of (1.5)
  does not suffice.

## The source dictionary

Everything relating the ambient operators to the printed eigenvalues and angles
is compiled, not prose; see `Section8SourceDictionary.lean`.  Its three
identifications are re-exported here under source-facing names.
-/

namespace TauCeti
namespace DavisKahan1970
namespace Section8

/-! ### Theorem 8.1(i), both blocks -/

/-- **Theorem 8.1(i), upper block**, source-literal: `A₁ - α ≤ C₁(Λ₁ - α)C₁` as
quadratic forms on the `Pᗮ` block, at the canonical branch. -/
alias theorem8_1_upperCompressionRepulsion_source :=
  DavisKahan.Experimental.Frontier.Section8.theorem8_1_upperCompressionRepulsion_source

/-- **Theorem 8.1(i), lower block**, the printed "with a similar relation for
`A₀`": `(α + δ) - A₀ ≤ C₀((α + δ) - Λ₀)C₀` on the `P` block. -/
alias theorem8_1_lowerCompressionRepulsion_source :=
  DavisKahan.Experimental.Frontier.Section8.theorem8_1_lowerCompressionRepulsion_source

/-! ### Theorem 8.2

`theorem8_2_branch_source_directed` is the strongest statement obtainable from
the explicit printed hypotheses; the `maximalAngle` forms add the Section 1
standing convention (1.5) and deliver the printed `Θ < π/4`.  The distinction is
deliberate and must not be collapsed. -/

/-- **Theorem 8.2, perturbation alternative, dimension-free.** -/
alias theorem8_2_perturbationHalfGap_source :=
  DavisKahan.Experimental.Frontier.Section8.theorem8_2_perturbationHalfGap_source

/-- **Theorem 8.2, residual alternative, dimension-free.**  Krein's completion
supplies a perturbation of the exact residual norm. -/
alias theorem8_2_residualHalfGap_source :=
  DavisKahan.Experimental.Frontier.Section8.theorem8_2_residualHalfGap_source

/-- **Theorem 8.2's printed disjunction, dimension-free.**  Either smallness
alternative gives `directedGap P Q < √2/2`.  This is the strongest conclusion
available from the explicit printed hypotheses alone. -/
alias theorem8_2_branch_source_directed :=
  DavisKahan.Experimental.Frontier.Section8.theorem8_2_branch_source

/-- Equation (1.5) in its finite form: equal rank identifies the symmetric and
directed projector gaps, so `‖sin Θ‖` may be computed from either. -/
alias subspaceGap_eq_directedGap_of_finrank_eq :=
  DavisKahan.Experimental.Frontier.Section8.subspaceGap_eq_directedGap_of_finrank_eq

/-- The same identification of the two gaps under Section 3's standing
assumption (3.5) instead of a dimension count: no finite dimensionality and no
equal `finrank`, only a linear isometry between the two crossed defects. -/
alias subspaceGap_eq_directedGap_of_crossedDefects :=
  DavisKahan.Experimental.Frontier.Section8.subspaceGap_eq_directedGap_of_crossedDefects

/-- **Theorem 8.2's printed conclusion `Θ < π/4` from the directed bound, in
any dimension**, under Section 3's standing assumption (3.5). -/
alias maximalAngle_lt_pi_div_four_of_crossedDefects :=
  DavisKahan.Experimental.Frontier.Section8.maximalAngle_lt_pi_div_four_of_crossedDefects

/-- **Theorem 8.2, perturbation alternative, printed conclusion `Θ < π/4`.** -/
alias theorem8_2_perturbationHalfGap_source_maximalAngle_lt :=
  DavisKahan.Experimental.Frontier.Section8.theorem8_2_perturbationHalfGap_source_maximalAngle_lt

/-- **Theorem 8.2, residual alternative, printed conclusion `Θ < π/4`.** -/
alias theorem8_2_residualHalfGap_source_maximalAngle_lt :=
  DavisKahan.Experimental.Frontier.Section8.theorem8_2_residualHalfGap_source_maximalAngle_lt

/-- **Theorem 8.2's printed disjunction, printed conclusion `Θ < π/4`.** -/
alias theorem8_2_branch_source_maximalAngle_lt :=
  DavisKahan.Experimental.Frontier.Section8.theorem8_2_branch_source_maximalAngle_lt

/-- The `sin 2Θ` estimate Theorem 8.2 inherits, perturbation form
`δ‖sin 2Θ‖ ≤ 2‖H‖`, at Theorem 8.2's own hypotheses. -/
alias theorem8_2_sinTwoTheta_perturbation_source :=
  DavisKahan.Experimental.Frontier.Section8.theorem8_2_sinTwoTheta_perturbation_source

/-- The `sin 2Θ` estimate Theorem 8.2 inherits, residual form, with `R` the
printed residual (1.8): `δ‖sin 2Θ‖ ≤ 2‖R‖` at the **ambient** `sin 2Θ` of the
pair, `DavisKahanExt.sinTwoAngleOperator Q P`.

The printed inequality is written at the *directed* `Θ₀`, and this docstring
used to say so.  It was the label that was wrong, not the statement: at the
operator norm the ambient reading is legitimate, because the two off-diagonal
blocks of the reflection defect have the same operator norm
(`norm_offdiag_add_eq`), and it is the stronger of the two readings.

The **directed** `δ N(sin 2Θ₀) ≤ 2 N(R)` at a *general* unitarily invariant norm
is a different statement and is the one remaining substantive axis of this
Section 8.2 surface.  No route through `sinTwoTheta_wholeSpace_paperUINorm`
reaches the printed constant `2` there -- a symmetric gauge sees the singular
values of a block plus its adjoint as those of the block doubled -- so recovering
it needs the Halmos generic decomposition.  The measurement is recorded at the
head of section 2b of `Section8SourceTheorem82.lean`. -/
alias theorem8_2_sinTwoTheta_residual_source :=
  DavisKahan.Experimental.Frontier.Section8.theorem8_2_sinTwoTheta_residual_source

/-- **Davis--Kahan 1970, Theorem 8.2, exactly as printed.**  Both `sin 2Θ`
estimates and `Θ < π/4`, from either smallness alternative, under the Section 1
standing convention (1.5). -/
alias theorem8_2_source :=
  DavisKahan.Experimental.Frontier.Section8.theorem8_2_source

/-- **Krein's self-adjoint completion with the exact restriction norm**, the one
external theorem the printed proof of the residual alternative cites. -/
alias theorem8_2_krein_completion_source :=
  DavisKahan.Experimental.Frontier.Krein.exists_selfAdjoint_completion_eq_norm_restriction

/-! ### Theorem 8.2 at the printed norm scope

The printed `sin 2Theta` theorem concludes for *every* unitarily invariant norm,
so that is the scope at which Theorem 8.2 inherits it.  The operator-norm forms
above are the `N = operator norm` reading. -/

/-- The `sin 2Theta` estimate Theorem 8.2 inherits, perturbation form
`delta * N(sin 2Theta) <= 2 * N(H)`, for **every** norm in the paper's own class
of unitarily invariant norms, at Theorem 8.2's own hypotheses. -/
alias theorem8_2_sinTwoTheta_perturbation_source_paperUINorm :=
  DavisKahan.Experimental.Frontier.Section8.theorem8_2_sinTwoTheta_perturbation_source_paperUINorm

/-! ### Theorem 8.2 over a real Hilbert space

Standing assumption 1 of the source admits a real or complex Hilbert space.
Theorem 8.2 supplies both subspaces as data, so its real form is an exact
complexification transport and adds no hypothesis; see
`DavisKahan/Frontier/Section8SourceTheorem82Real.lean`.  `theorem8_2_source_real`
is the whole printed theorem over `R`, and the two inherited `sin 2Theta`
estimates are available over `R` at the operator norm, the perturbation one also
at every source unitarily invariant norm -- exactly the scope available over
`C`. -/

/-- **Theorem 8.2, perturbation alternative, over a REAL Hilbert space.** -/
alias theorem8_2_perturbationHalfGap_source_real :=
  DavisKahan.Experimental.Frontier.Section8.theorem8_2_perturbationHalfGap_source_real

/-- **Theorem 8.2, residual alternative, over a REAL Hilbert space.** -/
alias theorem8_2_residualHalfGap_source_real :=
  DavisKahan.Experimental.Frontier.Section8.theorem8_2_residualHalfGap_source_real

/-- **Theorem 8.2's printed disjunction over a REAL Hilbert space**, with the
dimension-free directed conclusion. -/
alias theorem8_2_branch_source_directed_real :=
  DavisKahan.Experimental.Frontier.Section8.theorem8_2_branch_source_directed_real

/-- **Theorem 8.2's printed `Theta < pi/4` over a REAL Hilbert space**, under the
finite form of the standing convention (1.5). -/
alias theorem8_2_perturbationHalfGap_source_real_maximalAngle_lt :=
  DavisKahan.Experimental.Frontier.Section8.theorem8_2_perturbationHalfGap_source_real_maximalAngle_lt

/-- **Theorem 8.2's printed `Theta < pi/4` over a REAL Hilbert space, in any
dimension**, under Section 3's standing assumption (3.5). -/
alias theorem8_2_branch_source_real_maximalAngle_lt_of_crossedDefects :=
  DavisKahan.Experimental.Frontier.Section8.theorem8_2_branch_source_real_maximalAngle_lt_of_crossedDefects

/-- **Theorem 8.2's printed disjunction, printed `Theta < pi/4`, over a REAL
Hilbert space**, under the finite form of the standing convention (1.5). -/
alias theorem8_2_branch_source_real_maximalAngle_lt :=
  DavisKahan.Experimental.Frontier.Section8.theorem8_2_branch_source_real_maximalAngle_lt

/-- The `sin 2Theta` estimate Theorem 8.2 inherits over a REAL Hilbert space,
perturbation form `delta ||sin 2Theta|| <= 2 ||H||`. -/
alias theorem8_2_sinTwoTheta_perturbation_source_real :=
  DavisKahan.Experimental.Frontier.Section8.theorem8_2_sinTwoTheta_perturbation_source_real

/-- The `sin 2Theta` estimate Theorem 8.2 inherits over a REAL Hilbert space,
residual form, with `R` the printed residual (1.8).  As over `C`, the conclusion
is at the ambient `sinTwoAngleOperator Q P`, not the directed `Theta_0`; see the
complex alias above for what that does and does not say. -/
alias theorem8_2_sinTwoTheta_residual_source_real :=
  DavisKahan.Experimental.Frontier.Section8.theorem8_2_sinTwoTheta_residual_source_real

/-- The `sin 2Theta` estimate Theorem 8.2 inherits over a REAL Hilbert space,
perturbation form, for **every** norm in the paper's own class of unitarily
invariant norms. -/
alias theorem8_2_sinTwoTheta_perturbation_source_real_paperUINorm :=
  DavisKahan.Experimental.Frontier.Section8.theorem8_2_sinTwoTheta_perturbation_source_real_paperUINorm

/-- The directed `sin 2Theta_0` estimate Theorem 8.2 inherits over a REAL
Hilbert space, residual form, for **every** norm in the paper's own class of
unitarily invariant norms, with the printed factor two. -/
alias theorem8_2_sinTwoTheta_residual_source_real_paperUINorm :=
  DavisKahan.Experimental.Frontier.Section8.theorem8_2_sinTwoTheta_residual_source_real_paperUINorm

/-- **Davis--Kahan 1970, Theorem 8.2 over a REAL Hilbert space, exactly as
printed.**  Both `sin 2Theta` estimates and `Theta < pi/4`, from either smallness
alternative, under the Section 1 standing convention (1.5). -/
alias theorem8_2_source_real :=
  DavisKahan.Experimental.Frontier.Section8.theorem8_2_source_real

end Section8
end DavisKahan1970
end TauCeti

# Davis--Kahan 1970 source coverage

This directory is the publication-facing layer for Chandler Davis and
W. M. Kahan, *The Rotation of Eigenvectors by a Perturbation. III*, SIAM
Journal on Numerical Analysis 7 (1970), 1--46.

`PartIII.lean` exposes only proof-complete finite results. It is deliberately a
thin alias layer over the canonical mathematical modules; proof machinery
stays under `DavisKahan/FiniteDimensional`.

## Proof-complete source-facing results

| Source role | Canonical declaration |
|---|---|
| Ordered Sylvester estimate | `partIII_sylvester_ordered_uiNorm` |
| Interval/exterior Sylvester estimate | `partIII_sylvester_interval_uiNorm` |
| Residual `sin Theta` | `partIII_sinTheta_residual_uiNorm` |
| Generalized trial-map `sin Theta` | `partIII_generalizedSinTheta_uiNorm` |
| Perturbation `sin Theta` | `partIII_sinTheta_uiNorm`, `partIII_sinTheta_angleOperator_uiNorm` |
| Equal-rank Ritz-residual `tan Theta` | `partIII_tanTheta_ritzResidual_uiNorm` |
| Strict-lower-rank Ritz-residual `tan Theta` | `partIII_generalizedTanTheta_ritzResidual_uiNorm` |
| Pole-free tangent plus transversality | `partIII_tanTheta_ritzResidual_uiNorm_and_isTransverse` |
| Perturbation `sin 2 Theta` | `partIII_sinTwoTheta_uiNorm`, `partIII_sinTwoTheta_angleOperator_uiNorm` |
| Sharp operator-norm `tan 2 Theta` and acute branch | `partIII_tanTwoTheta_opNorm` |
| Projector-difference companions | `projector_difference_opNorm`, `spectralProjector_difference_opNorm` |
| Canonical direct rotation construction and projection intertwining | `directRotation`, `partIII_directRotation_map_eq`, `partIII_directRotation_intertwines_projection` |

The tangent direction is from the Ritz or trial subspace toward the exact
invariant subspace. The public tangent statements do not assume
transversality.

## Work still required for complete paper coverage

The repository's local TeX notes are independent mathematical distillations,
not a distributable transcription of the original article. Before a result is
advertised with an exact theorem or proposition number, its hypotheses,
orientation, norm scope, and conclusion must be checked against the original
source.

The following paper components are not yet represented by a proof-complete
source module:

- the remaining two-subspace geometry and the direct-rotation symmetry,
  trigonometric, uniqueness, and extremal results of Sections 3--4;
- the exact 1970 non-ordered Sylvester theorem, kept distinct from the later
  Bhatia--Davis--McIntosh `pi / 2` theorem;
- any source tangent or double-angle variants not implied by the stable aliases
  above;
- the unbounded-operator appendix;
- the canonical spectral-continuation, branch-selection, uniqueness, and
  spectral-repulsion results of Section 8;
- the Section 9 numerical model and the planar equality/optimality statements;
- any auxiliary numbered lemmas or propositions not subsumed by the source
  aliases above.

Experimental declarations are not evidence that these items are complete.
They must first be source-checked, proved, moved to the stable tree, documented,
and subjected to a fresh Lean build and trusted-dependency audit.

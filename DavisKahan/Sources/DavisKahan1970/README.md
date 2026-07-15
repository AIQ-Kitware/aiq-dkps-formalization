# Davis--Kahan 1970 source coverage

This directory is the publication-facing layer for Chandler Davis and
W. M. Kahan, *The Rotation of Eigenvectors by a Perturbation. III*, SIAM
Journal on Numerical Analysis 7 (1970), 1--46.

## Source scope and completion warning

The modernized local transcription states that the ambient space is a
separable Hilbert space, that all four headline theorems apply in infinite and
finite dimensions and for arbitrary unitary-invariant norms, and that the
single-angle theory extends to unbounded self-adjoint operators through
explicit domain and bounded-residual conditions. The final source facade must
therefore treat bounded statements as specializations rather than the
unqualified target.

Therefore this directory is not complete merely because `PartIII.lean` builds.
The present facade is a proof-complete **finite specialization** of a substantial
portion of the paper. It must be described with that qualifier.

`PartIII.lean` exposes only proof-complete finite results. It is deliberately a
thin scoped facade; proof machinery stays under `DavisKahan/FiniteDimensional`.
`GeneralSinTheta.lean` exposes the experimental maximally general theorem shape
and must not be described as proof-complete until its dependency audit is clean.

## Proof-complete finite source-facing specializations

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

A modernized transcription is maintained locally outside the distributable
source archive. The committed TeX notes are independent mathematical
distillations audited against that transcription. Before a result is
advertised with an exact theorem or proposition number, its ambient Hilbert
space, bounded or unbounded status, domain assumptions, hypotheses, direction,
norm scope, and conclusion must be checked against the transcription.

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


## Completion standard

A complete source package requires more than finite analogues of the four
headline inequalities. It requires source-checked Hilbert-space theorem
surfaces, the unitary-invariant norm scope with correct domains of finiteness,
the direct-rotation theory, the Section 8 continuation/selection package, the
unbounded passages, and the remaining numbered and sharpness results. See [`docs/planning/davis-kahan-full-paper-goal.md`](../../../docs/planning/davis-kahan-full-paper-goal.md).

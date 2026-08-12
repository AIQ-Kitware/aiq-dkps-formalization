# Finite-dimensional Davis--Kahan Part III audit

> **Historical formalization snapshot.** This records the finite-dimensional Part III surface at the stated baseline commit. It is not a current completeness statement; use the maintained Davis--Kahan census and source specification for current status.

Baseline: `7463ca25c64a46c48411a2769b47714889974a97`.

## Precise claim

The repository has a **proof-complete stable finite-dimensional Part III
specialization surface** at:

`DavisKahan/Sources/DavisKahan1970/PartIII.lean`.

Most of the stable finite theory is scalar-generic over `[RCLike 𝕜]`, so the
same declarations cover real and complex finite-dimensional Hilbert spaces.
This surface is not a claim that every numbered result, example, or extremal
statement in the 1970 paper is represented.

## Stable source-facing results

### Direct-rotation foundation

- `partIII_directRotation_map_eq`: the canonical finite rotation maps the first
  subspace onto the second.
- `partIII_directRotation_intertwines_projection`: it intertwines the two
  orthogonal projections.

These are the basic mapping/intertwining results, not the full extremal theory.

### Sylvester estimates

- `partIII_sylvester_ordered_uiNorm`;
- `partIII_sylvester_interval_uiNorm`.

Both are sharp constant-one estimates for arbitrary rectangular unitarily
invariant norms.  The stable finite Sylvester tree also contains pairwise
spectral-distance results and named operator/Frobenius/Ky Fan specializations.

### Single-angle sine theorems

- `partIII_sinTheta_residual_uiNorm`;
- `partIII_generalizedSinTheta_uiNorm` for a non-isometric trial map with a
  lower Gram bound and an equisingular representative;
- `partIII_sinTheta_uiNorm` for the perturbation theorem;
- `partIII_sinTheta_angleOperator_uiNorm` for the full-space angle operator.

The finite implementation additionally exposes operator-norm, Frobenius, and
Ky Fan corollaries in `FiniteDimensional/SinTheta/`.

### Tangent theorems

- `partIII_tanTheta_ritzResidual_uiNorm` for equal rank;
- `partIII_generalizedTanTheta_ritzResidual_uiNorm` for strict lower rank;
- `partIII_tanTheta_ritzResidual_uiNorm_and_isTransverse`;
- `partIII_tanTheta_vector`, the older pole-free per-vector endpoint.

The source-facing arbitrary-UI-norm theorem is the Ritz-residual form; the
per-vector result is retained as a simpler compatibility endpoint.

### Double-angle theorems

- `partIII_sinTwoTheta_uiNorm`;
- `partIII_sinTwoTheta_angleOperator_uiNorm`;
- `partIII_tanTwoTheta_opNorm`, including the conclusion that the maximal angle
  lies strictly below `pi / 4`.

The stable finite tree also contains operator, Frobenius, and Ky Fan
specializations for `sin 2 Theta`.  The stable `tan 2 Theta` source theorem is
currently an operator-norm result, not an arbitrary-UI-norm package.

### Projector companions

- `projector_difference_opNorm`;
- `spectralProjector_difference_opNorm`.

These are sharp factor-one projector-difference estimates under the stated
two-sided gap hypotheses.

## Stable supporting mathematics

The stable `DavisKahan/FiniteDimensional/All.lean` aggregate includes:

- finite spectral subspaces, gaps, angle geometry, and block operators;
- Ritz, residual, and trial-map interfaces;
- finite Sylvester equations and reciprocal-multiplier proofs;
- single-angle, tangent, and double-angle theorem families;
- the basic direct-rotation construction.

## Explicit exclusions

The following should not be folded into the claim above without a separate
successful extraction or proof audit:

- direct-rotation reversal, square, uniqueness, and all extremal/minimality
  results currently aliased from `Experimental/PartIII.lean`;
- planar optimality and simultaneous-equality models in the older finite
  sharpness module;
- the full bounded Borel spectral-calculus facade;
- continuation and spectral-repulsion packages;
- every unbounded appendix result;
- a general arbitrary-UI-norm `tan 2 Theta` theorem;
- every numbered theorem and example in the complete 1970 paper.

## Recommended concise description

> A proof-complete finite-dimensional Davis--Kahan Part III specialization,
> covering sharp Sylvester estimates, generalized and ordinary sine theorems,
> Ritz-residual tangent theorems, double-angle bounds, and projector-difference
> estimates over real and complex finite-dimensional Hilbert spaces.

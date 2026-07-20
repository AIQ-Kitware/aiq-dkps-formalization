# Roadmap: spectral subspace perturbation, operator angles, and Sylvester equations

## Status of this draft

This is a discussion draft for `TauCetiRoadmap`, not a migration checklist.
The prose specifies mathematics intrinsically.  Existing DKPS files and
identifiers appear only in the provenance and implementation notes.

The existing repository already completes the source-general Section 6 sine-theta
surface, including the universal-norm and pairwise Hilbert--Schmidt endpoints.
The roadmap is therefore an integration and library-development plan, not a claim
that Tau Ceti must rediscover those proofs from scratch.

## Overview

Perturbation theory for self-adjoint operators compares invariant spectral
subspaces before and after a perturbation.  Its central estimates are naturally
expressed through:

- orthogonal projections and directed operator angles;
- Sylvester equations between spectrally separated blocks;
- approximation numbers and unitarily invariant operator norms;
- graph subspaces and Riccati equations;
- closed, possibly unbounded, self-adjoint operators.

The goal is to build this as reusable functional analysis, not as an isolated
formalization of one paper.  Davis--Kahan Part III is the principal worked
source and acceptance suite.

## Scope boundary

This roadmap owns:

- subspace-angle and projection geometry needed for spectral perturbation;
- rectangular approximation-number and symmetric-ideal infrastructure not
  already available upstream;
- bounded and domain-aware closed Sylvester equations;
- sine, tangent, and double-angle perturbation estimates;
- source correspondence for the relevant Davis--Kahan results.

It does not own a parallel general theory of strongly continuous semigroups,
Stone's theorem, or unbounded generators.  Where those are needed, this roadmap
should consume or contribute narrowly scoped prerequisites to the existing
`OneParameterSemigroups` roadmap.  It also should not preserve a private
Spectra-shaped API when Mathlib or Tau Ceti has a canonical formulation.

## Generality bar

- **Scalar fields.** State algebraic finite-dimensional results over
  `[RCLike 𝕜]` when possible.  State complex spectral-calculus results over
  `ℂ`, with explicit real descent through complexification where appropriate.
- **Rectangular operators.** Operator-ideal and residual results should allow
  different domain and codomain Hilbert spaces rather than silently assuming
  endomorphisms.
- **Universes.** Domain and codomain universes should be independent unless a
  real mathematical construction requires otherwise.
- **Unbounded operators.** Use domain-aware closed operators and explicit
  domain transport.  Do not replace an unbounded theorem with a bounded
  specialization.
- **Norms.** State results for coherent unitarily invariant norm families when
  the proof supports them.  Operator, Frobenius, Schatten, and Ky Fan forms are
  consequences or named specializations.
- **Spectral gaps.** Distinguish ordered separation, interval/exterior
  separation, and arbitrary pairwise spectral distance.  Do not silently
  strengthen one into another.
- **Angles.** Keep directed and symmetric angles distinct.  Export both bundled
  operators and concrete projection identities needed downstream.

## Existing foundations to consume

Before implementation, audit the current Mathlib and Tau Ceti APIs for:

- `ContinuousLinearMap`, adjoints, positive operators, and continuous
  functional calculus;
- `LinearPMap`, closed graphs, dense domains, and operator adjoints;
- Hilbert bases, orthogonal projections, tensor products, and `Lp` products;
- finite-dimensional singular values and unitarily invariant norms;
- spectra, resolvents, projection-valued measures, and spectral restrictions;
- existing semigroup and unbounded-generator work under
  `OneParameterSemigroups`.

Any imported or closely adapted external formalization must be coordinated,
licensed, and credited at declaration or module level.

## Part A -- Closed operators and reducing spectral subspaces

Develop a canonical domain-aware closed-operator layer sufficient for
perturbation theory:

- densely defined closed operators and their `LinearPMap` views;
- same-domain and domain-transport predicates;
- bounded extensions and bounded full-domain embeddings;
- reducing subspaces and restrictions to a reducing summand;
- preservation of domains by orthogonal projections;
- self-adjoint spectral restrictions and localization of their spectra;
- real/complexification compatibility.

**Acceptance:** bounded operators embed without changing the action; reducing
restrictions agree with the ambient operator on the restricted domain; real
spectral restrictions complexify to the expected complex restrictions.

## Part B -- Approximation numbers and rectangular symmetric ideals

Develop approximation singular values for rectangular continuous linear maps:

- definition by best rank-bounded approximation;
- monotonicity, homogeneity, perturbation, adjoint invariance, and ideal
  inequalities;
- equality with finite-dimensional singular values;
- invariance under operator modulus and isometric coordinate changes;
- orthogonal block sums;
- coherent rectangular symmetric ideal families with left and right ideal
  inequalities;
- real/complex compatibility.

**Acceptance:** recover operator norm at index zero, finite-dimensional singular
values, and the expected behavior under adjoint, block sums, and contractions.

## Part C -- Hilbert--Schmidt and square-summable singular-value theory

Connect the equivalent models of the square norm:

- approximation-singular-value energy;
- basis-column square energy and basis independence;
- Hilbert-space tensor realization;
- adjoint symmetry;
- finite-dimensional Frobenius norm;
- finite-rank decompositions and membership in symmetric ideals.

**Acceptance:** prove the equivalence of the singular-value, column, tensor, and
Frobenius descriptions in their common scopes, including rectangular maps.

## Part D -- Sylvester equations

Develop the equation `A X - X B = C` in increasing generality:

- bounded finite-dimensional equations and reciprocal spectral multipliers;
- bounded Hilbert-space uniqueness and norm estimates;
- domain-aware closed Sylvester equations;
- ordered and interval/exterior spectral separation;
- arbitrary pairwise spectral distance;
- operator-norm and symmetric-ideal estimates;
- Hilbert--Schmidt tensor proofs at pairwise separation;
- real descent.

**Acceptance:** obtain sharp constant-one estimates under the hypotheses that
support them, and distinguish existence, uniqueness, and a priori estimates.

## Part E -- Operator angles and graph subspaces

Develop:

- directed sine and cosine operators from compressed projections;
- full projection-difference sine;
- operator Pythagoras and commutation identities;
- principal-angle compatibility in finite dimensions;
- arcsine and cosine definitions of the directed angle and their equivalence;
- graph subspaces, projection formulas, gap formulas, and angular operators;
- real/complex compatibility.

**Acceptance:** identify the operator norm of the sine with the corresponding
subspace gap and recover the finite-dimensional principal singular values.

## Part F -- Finite-dimensional Davis--Kahan Part III

Provide a stable source-facing finite specialization containing:

- ordered and interval/exterior Sylvester estimates for rectangular
  unitarily invariant norms;
- generalized trial-map and ordinary perturbation `sin Theta` theorems;
- equal-rank and lower-rank Ritz-residual `tan Theta` theorems;
- `sin 2 Theta` in unitarily invariant norms;
- sharp operator-norm `tan 2 Theta` with the quarter-turn conclusion;
- projector-difference companions;
- direct-rotation mapping and intertwining foundations.

Further direct-rotation extremality, spectral repulsion, continuation, and
sharpness results should be separate milestones only after their statements
and dependencies are fully reviewed.

## Part G -- Closed-operator sine-theta theory

Develop source-general complex and real theorems for closed self-adjoint
operators:

- bounded-residual and lower-frame formulations;
- interval/exterior and pairwise spectral-gap forms;
- common-domain and common-core variants;
- extension of residual identities from a graph core to the full domain;
- arbitrary supported unitarily invariant norms;
- finite-rank operator-norm consequences.

**Acceptance:** the bounded and finite-dimensional theorems are explicit
specializations, not replacements for the domain-aware result.

## Part H -- Double-angle, tangent, and Riccati theory

Develop reusable bounded and unbounded forms of:

- reflection-defect identities and `sin 2 Theta` estimates;
- tangent estimates on the acute branch;
- off-diagonal `tan 2 Theta` estimates;
- graph-reduction/Riccati equivalence;
- existence, bounds, and uniqueness for contractive Riccati solutions;
- unbounded graph and Riccati transport where justified.

## Part I -- Source correspondence, equality, and validation

Provide a source-facing Davis--Kahan layer that records:

- the correspondence between paper statements and reusable declarations;
- real and complex forms;
- the printed counterexample and sharpness statements;
- equality models of arbitrary finite multiplicity;
- explicit statements of what is not claimed.

Acceptance should include small matrix models, finite-rank examples, and
cross-checks between projection, singular-value, column-energy, and tensor
formulations.

## Suggested placement

Final placement should follow Tau Ceti topic ownership, approximately:

- `TauCeti/Analysis/Operator/Closed/...`
- `TauCeti/Analysis/Operator/SpectralSubspace/...`
- `TauCeti/Analysis/OperatorIdeal/ApproximationNumber/...`
- `TauCeti/Analysis/OperatorIdeal/HilbertSchmidt/...`
- `TauCeti/Analysis/Operator/Sylvester/...`
- `TauCeti/Analysis/InnerProductSpace/OperatorAngle/...`
- `TauCeti/Analysis/Operator/Perturbation/...`

Paper-specific aliases and correspondence material should live in a clearly
source-facing layer and should not dictate the generic namespaces.

## Provenance and coordination

The existing implementation is human-directed and mostly AI-authored.  It
contains closely adapted and depended-on material from Spectra at upstream
revision `8dbaaf6728d1342ae16acf79fd7eef7c59b37e63`, plus a recorded compatibility
patch for a later Lean/Mathlib pin.  Integration must preserve Apache-2.0
licensing and identify copied, adapted, generalized, and newly proved material.

Before code integration:

1. coordinate with Tau Ceti maintainers on overlap with existing roadmaps;
2. coordinate with the Spectra author or discuss the integration plan publicly;
3. register intentions only after roadmap targets and PR boundaries are stable;
4. search Mathlib and Tau Ceti for newly landed overlapping APIs.

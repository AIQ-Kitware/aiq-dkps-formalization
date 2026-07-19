# Canonical and alternative `sin Θ` developments

This directory is organized around the full Davis--Kahan 1970 single-angle
result. The canonical target is **not** the bounded theorem. It is the
source-faithful, domain-aware result for self-adjoint closed operators that may
be unbounded, with a bounded residual block and an applicable unitarily
invariant ideal gauge.

The canonical complex dependency chain is:

1. `Core/Unbounded.lean`: densely defined closed operators, the real
   resolvent/spectrum surface, and full-domain embeddings of bounded operators;
2. `SpectraBridge/RealSpectrumBridge.lean`: identification of the manuscript
   real spectrum with the vendored Spectra spectrum over `ℂ`;
3. `Sylvester/Genuine*`: direct Spectra cutoffs, filled truncations, both
   ordered two-unbounded engines, and the genuine all-gap theorem;
4. `Sylvester/LegacyGapCompletion.lean`: conversion of the historical
   interval/exterior predicate and direct dispatch of its ordered form-bound
   constructors;
5. `SinTheta/Unbounded.lean` and `SinTheta/LegacyGapCompletion.lean`: the
   residual block identity and transport from the clean complex Sylvester
   theorem to the historical sine-theta statement;
6. `FrameFactorization.lean`: complex lower-frame polar selection;
7. `Canonical.lean`, `Specializations.lean`, and
   `Sources/DavisKahan1970/GeneralSinTheta.lean`: source-shaped generalized,
   isometric, and bounded endpoints.

The real route shares the scalar-generic residual and angle algebra, then uses:

1. `Core/ClosedOperatorComplexification.lean` for domains, graph closure,
   self-adjointness, form bounds, resolvents, gaps, and Sylvester equations;
2. `Ideals/ComplexificationApproximation.lean` for exact approximation-number
   and finite Ky Fan invariance;
3. `Sylvester/RealUnbounded.lean` for finite-Ky-Fan descent and real Fan
   dominance;
4. `Core/ComplexificationFunctionalCalculus.lean` and
   `RealFrameFactorization.lean` for descent of the positive Gram powers;
5. `Core/ReducingRestriction.lean` for scalar-generic restrictions of closed
   operators to reducing subspaces;
6. `SpectraBridge/RealSpectralRestriction.lean` for descent of the complex
   spectral PVM, real spectral ranges, and their self-adjoint restrictions;
7. `NaturalReal.lean` for natural-input real isometric and generalized
   spectral-subspace endpoints;
8. `FrameFactorizationGeneric.lean`, `RealGeneralized.lean`,
   `RealCanonical.lean`, and `RealSpecializations.lean` for the real
   lower-frame and source-shaped endpoints.

`Core/UnboundedSpectral.lean` and the legacy ordered theorem remain historical
infrastructure. They are not intended theorem dependencies of either repaired
source route.

## Status of bounded and finite proofs

`Bounded.lean` is useful and should remain. It supplies an independent proof
route with weaker infrastructure requirements and is valuable for regression,
finite-rank transfer, and comparison with the general proof. It is not the
canonical completion boundary.

Likewise, the finite-dimensional results are genuine theorems and should not be
deleted. As the source-facing API becomes general, independent bounded and
finite proofs should be exported under `DavisKahan/Alternative` or under
explicitly qualified specialization names. Multiple proof paths are desirable
when their logical strength and scope are visible in the module structure.

## Gap configurations

The canonical theorem accepts `UnboundedSylvesterGap`, whose constructors
cover:

- interval/exterior separation;
- a lower-semibounded left block above an upper-semibounded right block;
- the reversed ordered orientation.

The ordered constructors permit both diagonal blocks to be genuinely
unbounded. The interval/exterior branch follows the source's bounded-spectral-
block relaxation. These cases must not be collapsed into point-spectrum
predicates.

## Norm scope

The source-facing norm parameter is `UnitaryInvariantIdealFamily`, currently an
alias for the stronger finite-Ky-Fan-dominant rectangular family required by
the cutoff proof. Operator norm is one instance. Hilbert--Schmidt, trace,
Schatten, Ky Fan, and compact-operator instances are separate obligations.
Proving only operator norm does not complete the canonical theorem.

## Soundness boundaries

The unbounded theorem must retain all of the following information:

- explicit operator domains;
- domain transport for the cross block;
- equality of the Sylvester equation on the source domain;
- self-adjointness of both diagonal blocks;
- source-faithful spectral separation or semibounds;
- bounded extension and ideal membership of the residual;
- a complete orthogonal exact-space decomposition before calling the block the
  full directed sine.

Do not replace these with a bounded operator plus comments about a future
extension. A bounded theorem should be obtained from the general API by the
full-domain constructor, or retained as a clearly named alternative proof.

## Spectra-backed bounded-perturbation specialization

The independent Spectra adapter now has two focused modules:

- `SpectraBridge/SpectralRestriction.lean` identifies the canonical Spectra
  projection with the orthogonal projection onto its range, packages the
  isometric range inclusion, proves domain preservation, and proves that the
  self-adjoint operator commutes with the projection on its domain.
- `SpectraBridge/SpectralRestrictionOperator.lean` restricts the generated
  unitary flow to each measurable spectral range, takes its Stone generator,
  and packages that generator as a self-adjoint closed operator.  The subtype
  inclusion maps its domain into the ambient domain and intertwines the two
  operators.
- `SpectraBridge/BoundedPerturbationSinTheta.lean` identifies the local bounded
  sum with Spectra's Kato--Rellich perturbation, derives self-adjointness of the
  sum, packages the perturbation residual as `V X`, and instantiates the
  genuine-spectrum operator-norm sine estimate with the two canonical spectral
  range inclusions.

- `SpectraBridge/SpectralRestrictionLocalization.lean` identifies the scalar
  spectral measure of the restricted Stone group with the ambient measure
  restricted to the selecting PVM set.  It derives interval form bounds and
  exterior resolvent exclusion for the restricted generators.

The canonical directed bounded-perturbation endpoint now accepts only the
measurable set conditions `B ⊆ [β, α]` and
`T ∩ (β - δ, α + δ) = ∅`; all self-adjoint restriction, Kato--Rellich,
intertwining, residual, and localization obligations are discharged internally.
- `SpectraBridge/SpectralProjectionSinTheta.lean` identifies the raw
  inclusion-adjoint overlap with the usual directed projection gap, proves the
  reverse directed estimate by applying the same unbounded engine to `A + V`
  and `-V`, and combines both directions with the sharp two-projection norm
  identity. Its source-facing endpoint is the conventional operator-norm
  estimate for the difference of the two canonical spectral projections,
  stated with genuine spectra of the four selected Stone restrictions.

## Current compiler-first frontier

The implementation leaves above are intentionally decomposed so compiler work
can proceed in dependency order.  The high-risk seams are now:

- elaborating the closed graph and adjoint-domain proofs for unbounded real
  complexification;
- reconciling the exact `LinearPMap` self-adjointness and resolvent APIs;
- compiling rank preservation and the min--max proof of exact approximation
  numbers under real complexification;
- checking the finite Ky Fan family coercions in the real Sylvester descent;
- compiling the conjugation-fixed real functional-calculus descent, especially
  negative real powers on an invertible positive Gram operator;
- reflecting the complex Gram identities back through injective
  complexification;
- compiling the conjugation-invariant spectral PVM descent and the generic
  reducing-subspace restriction, especially the adjoint-domain equivalence;
- checking the real spectral projection domain/intertwining descent and the
  natural-input exact decomposition;
- checking definitional equalities between selected real polar data and the
  source-facing real sine operators;
- running `FullUnboundedAudit.lean` and accepting completion only after every
  complex and real capstone has the expected trusted dependency list.

The generic `IsometricSinThetaProblem.result` remains the historical theorem
over an arbitrary `RCLike` implementation.  The source manuscript surface now
selects `result_complex`, and `result_real` is the parallel real endpoint.
This avoids pretending that the complex spectral foundation automatically
covers an arbitrary third implementation of the `RCLike` interface.

A candidate natural-input real spectral-subspace route is developed separately from
the source-shaped problem records.  The reusable core theorem restricts any
self-adjoint closed operator to an orthogonally complemented reducing subspace.
The Spectra bridge is designed to descend the canonical complex spectral PVM
through the real structure, prove that the resulting real projections reduce
the original operator, and instantiate the generic restriction.  `NaturalReal.lean`
then constructs every complementary-domain and intertwining fact internally for
both the isometric and lower-frame theorems.  This layer remains pending full
compiler verification together with the upstream real complexification route.

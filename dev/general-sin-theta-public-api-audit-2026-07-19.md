# General sine-theta public API audit

Date: 2026-07-19

## Canonical policy

The unqualified manuscript names use complex scalars, unbounded self-adjoint
operators, explicit domain compatibility, bounded residual extensions, all
three 1970 gap configurations, and arbitrary finite-Ky-Fan-dominant
unitary-invariant ideal families.

Real results use explicit `_real` names. Natural-input spectral-subspace results
use `_spectralSubspace`. Bounded forms use `_boundedSpecialization` or a
`bounded_` theorem name. Historical bookkeeping records remain available but
are not the preferred user entry point.

## Compiler-accepted endpoint matrix

| scalar | input level | trial map | gap surface | canonical endpoint |
|---|---|---|---|---|
| complex | source record | lower frame | legacy manuscript all-gap | `generalizedSinTheta` |
| complex | source record | isometry | legacy manuscript all-gap | `sinTheta` |
| real | source record | lower frame | real manuscript all-gap | `generalizedSinTheta_real` |
| real | source record | isometry | real manuscript all-gap | `sinTheta_real` |
| complex | measurable spectral set | isometry | genuine Spectra all-gap | implementation theorem accepted; source alias pending in the extension facade |
| complex | measurable spectral set | lower frame | genuine Spectra all-gap | extension theorem pending compiler acceptance |
| real | measurable spectral set | isometry | real all-gap | `sinTheta_real_spectralSubspace` |
| real | measurable spectral set | lower frame | real all-gap | `generalizedSinTheta_real_spectralSubspace` |
| complex | bounded source record | lower frame | closed-operator all-gap | `generalizedSinTheta_boundedSpecialization` |
| real | bounded source record | lower frame | closed-operator all-gap | `generalizedSinTheta_boundedSpecialization_real` |

## Preferred layering

1. Scalar-generic reducing-subspace construction.
2. Complex and real canonical spectral-subspace packages.
3. Natural reducing-subspace theorem records shared by real and complex
   Hilbert spaces.
4. Scalar-specific result methods that select the trusted complex or real
   analytic engine.
5. Spectral-set constructors of the natural reducing records.
6. Bounded specializations obtained with `ClosedOperator.ofBounded`.
7. Manuscript aliases.

## Compatibility declarations

Keep the following, but document them as internal or historical:

- `UnboundedSinThetaData`;
- `GeneralSinThetaProblem` and `RealGeneralSinThetaProblem`;
- `IsometricSinThetaProblem.result` over an arbitrary `RCLike` implementation;
- legacy spectrum and gap predicates needed by source-shaped statements;
- finite interval/exterior records.

Do not point new user-facing aliases at the scalar-generic historical result
unless its trusted dependency audit is independently clean for that scalar.

## Names to add

- `sinTheta_spectralSubspace` as the complex natural-input alias;
- `generalizedSinTheta_spectralSubspace` after the complex lower-frame natural
  wrapper is present;
- reducing-subspace endpoints for expert callers who already possess a
  canonical reducing subspace but not a spectral-set representation;
- bounded natural-input spectral-subspace endpoints for both scalars.

## Names not to add

Avoid unqualified names for:

- finite-dimensional-only statements;
- operator-norm-only statements;
- interval/exterior-only statements;
- theorem wrappers that still require `UnboundedSinThetaData`;
- arbitrary `RCLike` statements implemented only through complex spectral
  theory.

## Deprecation candidates after the new API is accepted

No declaration should be deleted during proof completion. After downstream
migration, consider deprecating direct source aliases to:

- manually assembled complementary restriction records;
- duplicated real and complex bounded records when a shared natural record can
  express both;
- convenience aliases that differ only by an obsolete spectrum predicate.

## Verification rule

A name is canonical only after:

1. its defining module builds from current source;
2. its printed trusted dependencies match the accepted foundation list;
3. its module is reachable from the intended library root;
4. at least one compile-only usage example constructs its inputs without
   accessing implementation fields that the public theorem claims to hide.


## Integration policy for this overlay

The verified `GeneralSinTheta.lean` facade is intentionally unchanged.  New aliases
are isolated in `GeneralSinThetaExtensions.lean`.  Fold them into the main facade
only after the extension root builds and its trusted-dependency audit is clean.

# Tau Ceti PR 1 package — rectangular approximation numbers

> **Status: DRAFT — API narrative synchronized; current validation pending.**
>
> The July 24 export/build log predates the real-valued approximation-number
> conversion, the Courant--Fischer redesign, and the unified operator-modulus
> API. It is historical evidence only. Do not submit this PR or copy its PASS
> labels forward until the current validation sequence in
> `pr1-consistency-restoration-2026-07-27.md` has completed.

## Proposed title

**Add rectangular approximation numbers for bounded operators**

## Submission coordinates

These values must be refreshed immediately before creating the Tau Ceti branch:

- **Tau Ceti base:** freshly fetched `origin/main`, not the old detached
  submodule pin;
- **Davis--Kahan source revision:** the value recorded by
  `scripts/refresh_tauceti_pr1_consistency.py --write` after all PR-1 signature
  lanes have landed;
- **branch:** `approximation-numbers` or the branch required by current Tau Ceti
  coordination policy;
- **roadmap marker:** replace the provisional marker below with the exact
  accepted target identifier before submission.

<!--tauceti-target:v1 {"focus":"spectral-subspace-perturbation","id":"SpectralSubspacePerturbation/PartB/approximation-numbers"}-->

## Draft PR body

### Summary

This PR adds a rectangular approximation-number foundation for bounded linear
operators. The canonical quantity is

```lean
ContinuousLinearMap.approximationNumber T n : ℝ
```

the operator-norm distance from `T` to maps of rank at most `n`. The API uses
zero-based indexing, so the zeroth approximation number is the operator norm.
The cluster includes elementary order and ideal inequalities, Hilbert-space
adjoint invariance, finite-dimensional identification with singular values, the
current finite-dimensional Courant--Fischer support, and the general
Hilbert-space operator modulus needed by later operator-ideal work.

No Davis--Kahan perturbation theorem is included.

### Roadmap target

Part B, approximation-number foundation. This is the first dependency-closed
library PR supporting the later rectangular ideal and spectral-subspace
perturbation layers.

The exact `Basic.lean` declaration-name list is intentionally not frozen in this
draft while the separately claimed §5.1 signature-polish lane is active. The
final PR body must be regenerated from the resulting tree and extraction
manifest after that lane is released.

### Scope

The export closure is computed from the actual `ForTauCeti` import graph by
`scripts/refresh_tauceti_pr1_consistency.py`; the manifest must not carry only
the historical six headline modules. In the corrected 2026-07-27 base the
closure contains the headline modules plus `Cardinal.Lift`, `BasisSpan`, and
`SingularValues`. If Section 5.1 moves rank plumbing to `RankCompLe.lean`, that
module is included automatically once `Basic.lean` imports it.

The headline modules are:

- `TauCeti/SetTheory/Cardinal/Lift.lean`
  - the cardinal-lift helper required by the cross-universe approximation-number
    proof;
- `TauCeti/LinearAlgebra/Dimension/RankCompLe.lean`, when present after the
  separately owned Section 5.1 lane;
- `TauCeti/Analysis/OperatorIdeal/ApproximationNumber/Basic.lean`
  - the real-valued approximation-number definition;
  - zero-based operator-norm endpoint;
  - antitonicity and nonnegativity;
  - addition, scalar, and composition inequalities;
  - only approximation-number declarations after generic rank plumbing has
    been moved to its own dependency-appropriate module by the §5.1 lane.
- `TauCeti/Analysis/OperatorIdeal/ApproximationNumber/Adjoint.lean`
  - Hilbert-space adjoint invariance.
- `TauCeti/Analysis/InnerProductSpace/BasisSpan.lean`
  - the basis-index span API used by Courant--Fischer;
- `TauCeti/Analysis/InnerProductSpace/CourantFischer.lean`
  - the current finite-dimensional min--max and eigenvalue-comparison support,
    centered on basis-span subspaces rather than the retired public
    `specSubspace` surface.
- `TauCeti/Analysis/InnerProductSpace/SingularValues.lean`
  - the singular-value support imported by the finite-dimensional and min--max
    modules;
- `TauCeti/Analysis/OperatorIdeal/ApproximationNumber/FiniteDimensional.lean`
  - comparison with and equality to finite-dimensional singular values.
- `TauCeti/Analysis/OperatorIdeal/ApproximationNumber/MinMax.lean`
  - lower-modulus bounds from rank, finite-dimensional, and linearly independent
    test families;
- `TauCeti/Analysis/InnerProductSpace/OperatorModulus.lean`
  - the unified rectangular definition
    `ContinuousLinearMap.modulus T = (T⋆ T)^(1/2)`;
  - positivity, self-adjointness, uniqueness of the nonnegative square root;
  - `modulus_mul_self`;
  - pointwise and operator-norm identities;
  - one-sided composition norm laws and commuting-modulus support.

All final files must use Tau Ceti module syntax, public imports only where part
of the exported interface, exact provenance, no warning suppressions, and the
current Tau Ceti file-size policy.

### Deliberate exclusions

This PR does not include:

- any Davis--Kahan sine, tangent, or spectral-subspace perturbation theorem;
- rectangular symmetric ideal families or paper-specific unitary-invariant norm
  structures;
- Hilbert--Schmidt, trace-class, or Schatten families;
- Spectra, PVM, or arbitrary-Hilbert-space spectral-localization machinery;
- exact orthogonal block-sum merge formulas whose current proof is
  Spectra-coupled;
- real-complexification machinery unrelated to this cluster;
- paper-facing approximation-singular-sequence records or historical wrappers;
- the Spectra-dependent approximation-number invariance theorem for the modulus,
  unless a separate dependency-clean proof has landed and been explicitly added
  to the accepted roadmap target.

### API decisions

- **Codomain:** `ℝ`, not `ℝ≥0`. Nonnegativity is a theorem. This matches the
  finite-dimensional singular-value API and removes repeated coercion layers in
  downstream Davis--Kahan code.
- **Indexing:** zero-based. The §5.1 lane owns the final roadmap wording and any
  concluding declaration rename required by that decision.
- **Namespace:** operator methods extend `ContinuousLinearMap` so dot notation is
  available. Generic spectral-subspace helpers remain in their natural Tau Ceti
  namespaces.
- **Universes:** source and target spaces retain independent universes wherever
  possible. Cross-universe rank plumbing is not hidden in the operator-ideal
  file; the §5.1 lane moves the reusable rank fact to its own module.
- **Operator modulus:** there is one rectangular
  `ContinuousLinearMap.modulus`, not separate square `operatorAbs` and
  rectangular `rectangularOperatorModulus` public APIs.
- **File split:** modules are separated by mathematical responsibility and
  dependency closure, not by historical Davis--Kahan paths.

### Provenance

The code was developed in the Davis--Kahan/DKPS formalization repository,
Copyright 2026 Kitware, Inc., Apache 2.0. Each exported file must retain its own
exact source modules, source revision, authors, and whether the result was
copied, adapted, unified, generalized, or re-proved.

The current operator-modulus module unifies work formerly located in:

- `ForMathlib/Analysis/InnerProductSpace/OperatorAbsoluteValue.lean`; and
- `DavisKahan/OperatorIdeal/ApproximationNumbers/OperatorModulus.lean`.

The approximation-number foundation was adapted from the Mathlib PR documented
in the module provenance. Spectra is not an import of the exported cluster;
where Spectra influenced deferred theorem selection, that influence remains
recorded rather than silently erased.

### Validation

**Pending.** The current tree must be exported and validated after all PR-1
signature lanes are complete.

Required Davis--Kahan-side checks include:

```text
refresh_tauceti_pr1_consistency.py --check
check_dependency_layers.py
export_for_tauceti.py --cluster approximation-number --write
export_for_tauceti.py --cluster approximation-number --check
ForTauCeti build
Challenge build and declaration-name drift gate after renames
relevant source-census and downstream consumer builds
```

Required Tau Ceti-side checks include the repository's current warning-as-error
build, axiom audit, module-system audit, and lint environment. Record exact
commands and results in a new dated build log.

### Downstream validation

Also pending. A landing simulation must temporarily replace this cluster's
`ForTauCeti.*` imports with the exported `TauCeti.*` modules and rebuild the
actual Davis--Kahan consumers. The simulation must use the real-valued API and
`TauCeti.Analysis.InnerProductSpace.OperatorModulus`; a July 24 simulation of
older files is not sufficient.

---

## Safe push command

Do not push or open a PR without explicit instruction. Re-read the current
`external/TauCeti/COORDINATION.md`, fetch `origin/main`, record its exact head,
create a fresh branch from that head, and use the coordination-prescribed
force-with-lease form. Do not reuse the July 24 observed base SHA as an expected
current value.

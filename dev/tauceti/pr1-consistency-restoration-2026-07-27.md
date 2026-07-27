# Tau Ceti PR 1 consistency restoration — 2026-07-27

## Lane boundary

This lane repairs the integration package around the approximation-number PR. It
owns documentation, export metadata, current-revision bookkeeping, and
validation truthfulness. It does **not** own approximation-number theorem
signatures or proofs.

The concurrent signature-polish lane owns:

- `ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Basic.lean`;
- the new cross-universe rank helper module;
- declaration-name call sites affected by its renames;
- `source_declarations` name entries in
  `dev/tauceti/extraction-manifest.json`; and
- `dev/tauceti-signature-polish-todo.md` §5.1.

This consistency lane preserves those `source_declarations` lists byte-for-byte.
It also does not touch §5.2 Adjoint, §5.3 FiniteDimensional, §5.4 MinMax,
`comparator/*.json`, any Challenge module, or the Tau Ceti submodule pointer.

## Divergence found

The PR package still described the July 24 extraction while the code had moved
on in three foundational ways:

1. `ContinuousLinearMap.approximationNumber` is now `ℝ`-valued, not
   `ℝ≥0`-valued.
2. The square `operatorAbs` and rectangular operator-modulus APIs were unified
   as `ContinuousLinearMap.modulus` in
   `ForTauCeti.Analysis.InnerProductSpace.OperatorModulus`.
3. The Courant--Fischer layer was redesigned; the old `specSubspace` public
   surface is no longer the current API.
4. The historical six-file export closure is no longer dependency-closed:
   current imports also require `Cardinal.Lift`, `BasisSpan`, and
   `SingularValues`, and the Section 5.1 lane may add `RankCompLe`.

Consequently:

- the extraction manifest named a deleted staging module;
- the exporter failed before reaching the current cluster;
- the PR body advertised the wrong codomain, path, and public modulus API; and
- the July 24 build log was being cited as evidence for code written later.

The July 24 results remain useful historical evidence that the extraction
workflow once worked. They are not validation of the current API.

## Durable repair

`scripts/refresh_tauceti_pr1_consistency.py` provides an idempotent split-safe
repair.

While signature work is active, claim this lane without touching the manifest:

```bash
python3 scripts/refresh_tauceti_pr1_consistency.py --claim
```

After the §5.1 lane has landed its name changes, refresh the non-name metadata:

```bash
python3 scripts/refresh_tauceti_pr1_consistency.py --write
python3 scripts/refresh_tauceti_pr1_consistency.py --check
```

The refresh performs only these manifest changes:

- update the observed Davis--Kahan and Tau Ceti revisions;
- replace the deleted
  `ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.OperatorModulus`
  path with `ForTauCeti.Analysis.InnerProductSpace.OperatorModulus`;
- compute the complete dependency-first `ForTauCeti` module closure from the
  current import graph, including newly split support modules and an eventual
  `RankCompLe` import without hard-coding that concurrent lane's result;
- update the final Tau Ceti destination accordingly;
- record the unified `ContinuousLinearMap` namespace and provenance; and
- mark the cluster as requiring current validation.

It asserts that every `source_declarations` list is unchanged.

## Current validation sequence

Once all approximation-number signature lanes are released, perform the current
validation from the final working tree, not from the July 24 log.

### Davis--Kahan workspace

```bash
python3 scripts/refresh_tauceti_pr1_consistency.py --write
python3 scripts/refresh_tauceti_pr1_consistency.py --check
python3 scripts/check_dependency_layers.py
python3 -m pytest \
    scripts/tests/test_refresh_tauceti_pr1_consistency.py \
    scripts/tests/test_export_for_tauceti.py \
    scripts/tests/test_check_dependency_layers.py
lake build ForTauCeti
lake build Challenge
```

Run the relevant declaration-name drift and source-census gates after the §5.1
renames have settled.

### Throwaway Tau Ceti export

Start from a clean throwaway branch at freshly fetched Tau Ceti `origin/main`.
Do not commit the submodule pointer in the Davis--Kahan repository.

```bash
python3 scripts/export_for_tauceti.py \
    --cluster approximation-number --write
python3 scripts/export_for_tauceti.py \
    --cluster approximation-number --check
```

Then, from `external/TauCeti`, run the current repository-prescribed strict
checks, including warning-as-error build, axiom audit, module-system audit, and
lint environment. Record exact commits and exact commands in a new dated build
log.

### Landing simulation

Before calling the PR package ready, temporarily replace the cluster's
`ForTauCeti.*` imports with the exported `TauCeti.*` modules and rebuild the
actual Davis--Kahan consumers. This simulation must use the current real-valued
API and the unified modulus module.

## Readiness rule

The PR body must remain marked **validation pending** until a new log records the
current tree. Do not copy the July 24 PASS labels forward. After a fresh green
run, replace the pending section with exact results and include the new log's
Davis--Kahan commit, Tau Ceti base commit, export branch commit, and toolchain.

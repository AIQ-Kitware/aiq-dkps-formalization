# `dev/tauceti/` — Tau Ceti migration working set

The execution documents for the **primary track** in `AGENTS.md`: polishing
paper-independent foundations into `ForTauCeti`, retiring the `vendor/Spectra`
dependency, and converging three parallel operator-theory stacks into one.

These are documentation only. None of them changes a Lean module, aggregate,
audit, or build target.

## Start here

If you are picking up migration work cold, read in this order:

1. **`convergence-matrix.md`** — the primary planning artifact. One row per
   declaration, classified exact-duplicate / wrapper-duplicate /
   parallel-formulation / missing-reusable-result / paper-specific, with a
   canonical destination. Read it before declaring any layering question
   undecidable; it is the record of what the repository has actually decided.
2. **`spectra-removal-plan.md`** — the execution contract for retiring Spectra,
   with its ledger **`spectra-to-tauceti-port-ledger.md`**. The surface is 61
   declarations, generated and drift-gated. Do not re-measure it by counting
   import lines.
3. **`u1-linearpmap-migration.md`** — the U1 contract: replacing the bundled
   `ClosedOperator` foundation with Mathlib `LinearPMap` plus property
   predicates. The representation decision is closed, not design-stage.
4. **`../LANES.md`** — who holds what right now. Claim before your first edit.

## The rest of the working set

**Planning and classification**

- `extraction-cluster-classification.md` — dependency-closed clusters, in the
  order they can move.
- `mathematical-declaration-inventory.md` — reusable content grouped by
  portability and specialization level.
- `formathlib-to-fortauceti-migration.md` — how a `ForMathlib` module is
  actually moved and its consumers repointed.
- `spectra-provenance-map.md` — upstream, compatibility, dependency, and
  attribution treatment of Spectra-derived material.

**Audits and inventories**

- `finite-dimensional-part-iii-audit.md` — exactly what the stable finite source
  facade supports, with exclusions.
- `part-iii-production-extraction-queue.md` — proved aliases still behind coarse
  `Experimental` modules.
- `experimental-sorry-triage.md` — every open obligation in
  `DavisKahan/Experimental/**`, with the owner's standing decision that they are
  KEEP until a specific one is confirmed superseded by a sorry-free twin.

**Submission packaging**

- `submission-ladder.md` — **read before planning any Tau Ceti PR.** Measures that the
  PR1 draft's dependency-closed slice is 37 modules spanning six topics, and gives the
  six-rung ladder the import graph already supports (2--12 modules per PR).

- `tauceti-pr1-approximation-numbers.md` — the PR1 package.
- `pr1-consistency-restoration-2026-07-27.md` — its consistency record,
  maintained by `scripts/refresh_tauceti_pr1_consistency.py`.
- `migration-baseline-2026-07-24.md` — the toolchain/pin baseline the migration
  measures against; `lakefile.toml` refers to it.
- `migration-build-log-2026-07-24.md` — build evidence for the staged moves.

## `ForMathlib` is being retired

`ForMathlib` is **wound down into `ForTauCeti`**, not maintained as a parallel
Mathlib staging area (jon's decision, 2026-07-29). Modules migrate as their
import closures allow, following the CourantFischer playbook recorded in
`convergence-matrix.md`: move the closed component, repoint consumers, delete
the old file.

Module docstrings that still read `Extraction class: authored in place, for
upstreaming to Mathlib rather than to Tau Ceti` are **stale, and are not a bar
to migration.** Reading them as policy cost a previous session two lane
reversals. The firewall in `scripts/check_dependency_layers.py` is the real
constraint: `ForTauCeti` may import only Mathlib / TauCeti / ForTauCeti, so a
`ForMathlib` file migrates only once no remaining `ForMathlib` file imports it.

## Active representation migration

U1 is executable. The canonical unbounded-operator representation is Mathlib
`LinearPMap`; the local `ClosedOperator` bundle is temporary compatibility
infrastructure. Preserve green builds through adapters while migrating
consumers — a green build is an invariant to hold during the migration, not a
reason to avoid it. See `u1-linearpmap-migration.md` and `../LANES.md`.

# Davis--Kahan completion first; Tau Ceti and Spectra migration second

**Current DKPS baseline:** `dfd9d37ebc86`  
**Tau Ceti reference:** `external/TauCeti` at `92c79e5e0a618f8c5c2b9909be1ce50f6891dde7`  
**Spectra reference/vendor:** `8dbaaf6728d1342ae16acf79fd7eef7c59b37e63`

This document fixes the milestone order and dependency policy for the remainder
of the project. It supersedes any earlier instruction to restructure the
repository around Tau Ceti before the Davis--Kahan paper is complete.

## Executive decision

There are two distinct milestones.

### Milestone 1: complete the 1970 paper as a standalone DavisKahan package

The current target architecture is:

```text
Mathlib
   ↑
vendor/Spectra
   ↑
DavisKahan
```

The project should use this architecture to finish the paper. The existing
package, theorem frontier, source census, and vendored dependency are assets,
not temporary clutter that must be removed before completion.

### Milestone 2: migrate reusable foundations into Tau Ceti

Only after the paper completion gate is met should the normal architecture be
migrated toward:

```text
Mathlib
   ↑
Tau Ceti
   ↑
DavisKahan
```

`DavisKahan` remains a package in this final architecture. Tau Ceti receives
reusable foundations; paper statements, source correspondence, corrected
claims, and paper-specific assembly remain downstream.

The final post-migration build must not depend on Spectra. Mathematics adapted
from Spectra must be deeply integrated into Tau Ceti or replaced by Tau Ceti or
Mathlib results, with durable attribution. That is a major second-milestone
campaign and must not derail the first milestone.

## Milestone 1 completion gate

The paper milestone is met only when all of the following are true.

1. Every theorem, proposition, lemma, corollary, definition, and construction
   in the maintained 1970 source census has a compiled formal endpoint.
2. Source-facing endpoints are recursively grounded. A wrapper whose proof
   depends on an unfinished frontier declaration does not count as complete.
3. The ambient scope is source-faithful: separable Hilbert space, unbounded
   self-adjoint passages where the paper requires them, and the paper's
   unitary-invariant norm scope.
4. The direct-rotation, spectral-selection, continuation, sharpness/equality,
   and Section 9 analytic components are included rather than silently omitted.
5. Proposition 4.4 is represented by a machine-checked counterexample and an
   audited corrected replacement when appropriate. Any additional false source
   statement receives the same treatment.
6. No proof escape remains in the completion surface, and the trusted
   dependency audit is clean.
7. A clean build from a fresh checkout succeeds, followed by the frontier,
   source-census, and axiom audits.
8. The completion report distinguishes proved source claims, refuted source
   claims, and corrected replacement theorems.

A finite-dimensional, bounded-only, or operator-norm-only result is not a
substitute for the corresponding source theorem unless the source theorem is
itself limited to that scope.

## Intermediate dependency policy

### `vendor/Spectra` is allowed and expected

During Milestone 1, `vendor/Spectra` is the production dependency used by the
normal build. It is acceptable to rely on it to close paper obligations.
Removing it early would force the team to solve two difficult problems at once:
finishing the mathematics and redesigning its foundational library.

The current Spectra maintenance arrangement is adequate for this phase:

- `external/Spectra` is the pristine source/provenance checkout;
- `vendor/Spectra` is the build input;
- compatibility changes are tracked reproducibly;
- the source commit and license are known;
- the repository already has a broad compiled proof tree above it.

The main risk is not immediate vendor breakage. It is losing provenance or
creating still more accidental coupling. Therefore new use is allowed but must
be disciplined.

### Rules for new Spectra-dependent work

1. Import the narrowest module that supplies the needed theorem or structure.
2. Search Mathlib, the current DavisKahan tree, Tau Ceti, and Spectra before
   creating a duplicate foundation.
3. If a general theorem naturally extends an existing Spectra API, it may be
   added to the managed vendor patch during Milestone 1.
4. If the theorem is ours but merely stated over a Spectra object, prefer
   `ForMathlib/` or `DavisKahan/Experimental/MathAhead/` rather than modifying
   the donor file.
5. Record declaration-level provenance whenever source text, theorem selection,
   proof architecture, or API design is substantially adapted from Spectra.
6. Do not broaden Spectra imports for speculative future use. Each new import
   must support a concrete source obligation.
7. Preserve the pristine reference checkout. Never make project edits under
   `external/Spectra`.

### Tau Ceti during Milestone 1

`external/TauCeti` is a design and overlap reference, not a production
requirement. Agents should inspect it to avoid incompatible or duplicative API
design, but should not:

- add Tau Ceti to the ordinary Lake dependency graph;
- reorganize the project around a `TauCetiCandidates` root library;
- perform a bulk namespace migration;
- port a large Spectra subsystem solely for architectural cleanliness;
- block a Davis--Kahan theorem on upstream review or Tau Ceti integration.

A tiny dependency-closed Tau Ceti slice may be vendored only if it demonstrably
saves a major development required to complete the paper. That decision must be
made separately and must include a pin, dependency closure, provenance, and a
rollback path.

## Where new mathematics should land before paper completion

Use the current import graph.

- Paper-facing statements and assembly: `DavisKahan/Experimental/Frontier/` and
  the eventual canonical source modules.
- Reusable local foundations that are upstream of the frontier:
  `ForMathlib/` or a cycle-safe `DavisKahan/Experimental/` foundation module.
- Mathematics ahead of an existing frontier endpoint:
  `DavisKahan/Experimental/MathAhead/`, followed by promotion.
- Noncompiled sketches: `DavisKahan/Experimental/Scratch/`, with a promotion
  manifest. Do not mistake a compiled scratch file for source completion.
- Spectra compatibility changes that genuinely belong with the donor API:
  the managed `vendor/Spectra` patch, with provenance and a focused commit.

Generic code should still be written so it can later move upstream:

- avoid paper numbering in generic theorem names;
- do not expose source-census records in generic APIs;
- separate generic operator facts from Davis--Kahan applications;
- prefer Mathlib conventions when the existing local API does not force
  otherwise;
- note the likely Tau Ceti destination in the provenance ledger.

This is future portability, not current restructuring.

## Immediate next Opus campaign

Opus should resume mathematical work in the existing package. Its primary
campaign is the already-reserved nonacute direct-rotation and polar foundation
needed for Section 3.

The exact operating plan is:

```text
docs/planning/opus-next-paper-completion-campaign.md
```

The ready-to-use agent prompt is:

```text
dev/opus-next-agent-prompt.md
```

The campaign should close real paper obligations, not merely write an audit or
prototype a future Tau Ceti API.

## Coordination with Edward's Fable track

`dev/LANES.md` is authoritative. Opus must inspect it at session start and
avoid declarations claimed by Edward's resumed agent. The nonacute polar lane
is reserved for Jon's next Opus session. If the ledger has changed, Opus must
claim an unoccupied equivalent campaign before editing.

Do not treat model identity as lane identity: claims belong to the human owner.

## Spectra provenance policy

The eventual removal of Spectra makes provenance more important, not less.
Every extracted cluster needs a durable record containing:

- original repository and exact commit;
- original paths and declaration names;
- original author and license information;
- local declaration names and destination modules;
- whether the result was copied, ported, generalized, specialized, or
  substantially redesigned;
- semantic differences from the donor statement;
- downstream DavisKahan users;
- eventual Tau Ceti target and upstream status.

Keep original file headers when a file remains substantially derived from a
Spectra file. For heavily reorganized work, include an `Adapted from` module
note and declaration-level ledger entries. A proof rewritten from scratch may
still owe attribution when the theorem selection or proof architecture came
from Spectra.

## Milestone 2 migration program

After the paper is complete, migrate one dependency-closed cluster at a time.

1. Select a Spectra cluster used by the completed paper.
2. Compute the exact declarations and dependency closure actually needed.
3. Replace dependencies already available in Mathlib or Tau Ceti.
4. Redesign the missing mathematics in Tau Ceti idiom.
5. Preserve provenance and audit semantic drift.
6. Merge the reusable result into Tau Ceti.
7. Add a temporary DavisKahan adapter.
8. Switch downstream proofs and rerun the recursive grounding audit.
9. Remove the corresponding Spectra imports and compatibility patch entries.
10. Repeat until the normal build contains no Spectra dependency or namespace
    reference.

Likely clusters include:

- bounded polar decomposition and partial isometries;
- unbounded self-adjoint operators and resolvents;
- PVM and bounded Borel functional calculus;
- Stone, Cayley, and semigroup bridges;
- compact self-adjoint spectral theory;
- rectangular operator ideals.

The order should follow the completed DavisKahan dependency graph rather than a
speculative library taxonomy.

## Hard prohibitions before Milestone 1

Unless the user explicitly changes the milestone order, do not:

- delete or replace `vendor/Spectra` wholesale;
- make the ordinary build require Tau Ceti;
- spend a campaign on namespace-only migration;
- move the paper frontier into Tau Ceti;
- claim the paper complete from textual presence or a bounded specialization;
- restore a refuted source statement as a theorem;
- let an upstream contribution block a compiled local proof;
- perform a large architectural rewrite without a theorem-closure payoff.

## Current success metric

For now, measure progress by source endpoints recursively grounded, false source
claims formally resolved, and hard mathematical leaves closed in the
`DavisKahan` package.

Do not measure progress by the number of Spectra files copied, Tau Ceti modules
created, or namespaces renamed.

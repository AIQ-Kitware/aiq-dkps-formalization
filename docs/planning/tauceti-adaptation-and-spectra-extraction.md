# Dual-track: Tau Ceti extraction (primary) and Davis--Kahan source fidelity (maintenance)

**Current DKPS baseline:** `dfd9d37ebc86`  
**Tau Ceti reference:** `external/TauCeti` at `92c79e5e0a618f8c5c2b9909be1ce50f6891dde7`  
**Spectra reference/vendor:** `8dbaaf6728d1342ae16acf79fd7eef7c59b37e63`

**Revised 2026-07-24.** This document previously imposed a strict *complete the
paper first, migrate second* order. That gate is **retired** because it no
longer describes the repository: `TauCeti` is already a local dependency,
`ForTauCeti` is a default build target, sixteen reusable modules are already
staged there, and production code is already reorganized for extraction. The
reusable foundations and the principal Davis--Kahan machinery needed to justify
an upstream spectral-perturbation library are in hand, and the source census is
clean; the remaining 1970 source obligations are not prerequisites for beginning
Tau Ceti integration.

## Executive decision — dual-track

The project runs two tracks in parallel, not two sequential milestones.

### Primary track: Tau Ceti extraction

Polish and upstream stable, paper-independent foundations into `ForTauCeti` (the
staging library whose declarations already carry their final `TauCeti.*`
namespaces), in small dependency-closed clusters. Mathlib is **not** the
near-term destination for this contribution — `ForTauCeti` (→ Tau Ceti) is the
polished home. This is the current default work.

```text
Mathlib      TauCeti
   ↑            ↑
vendor/Spectra  ForTauCeti
   ↑            ↑
DavisKahan  ←────┘
```

`DavisKahan` remains a package and may consume `ForTauCeti`. Tau Ceti receives
reusable foundations; paper statements, source correspondence, corrected claims,
and paper-specific assembly stay downstream. The final build removes Spectra,
with mathematics adapted from Spectra deeply integrated or replaced, and durable
attribution.

### Maintenance track: Davis--Kahan source fidelity

Keep the source census, counterexamples, paper wrappers, and remaining analytic
obligations honest and compiling. **Do not expand this track merely to satisfy
an obsolete completion gate.** A remaining paper obligation blocks upstream work
only when it (a) reveals an error in an API being proposed upstream, (b) requires
a foundational result that belongs in Tau Ceti, (c) exposes a source-fidelity
problem comparable to the Theorem 6.3 transcription error, or (d) prevents
`DavisKahan` from consuming the upstream replacement. Migration does not wait for
Section 9 examples, every extremal statement, or every unbounded arbitrary-ideal
endpoint.

## Maintenance-track definition of done for the paper

The following is the *definition of done for the paper as a maintenance
deliverable* — no longer a gate that blocks upstreaming. The paper is complete
when all of the following are true.

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

### Tau Ceti staging (current)

`TauCeti` is now a local dependency and `ForTauCeti` is a default build target;
`external/TauCeti` remains the read-only pin/provenance reference. Reusable
foundations are staged into `ForTauCeti` (final `TauCeti.*` namespaces), not
committed to the `external/TauCeti` submodule pointer, which stays fixed until a
roadmap-accepted PR lands. `scripts/export_for_tauceti.py` reproduces the
`TauCeti/` copy on demand at submission time. Still avoid a speculative bulk
namespace migration unconnected to an accepted roadmap target: migrate
dependency-closed clusters that map to a roadmap area.

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

## Hard prohibitions (both tracks)

Do not:

- delete or replace `vendor/Spectra` wholesale before its consumers migrate;
- commit the `external/TauCeti` submodule pointer, or otherwise assume admission
  — all Tau Ceti prep is staged **in this repository**, structured as if
  accepted (see "In-repo Tau Ceti-readiness" below);
- perform a speculative bulk namespace migration unconnected to a roadmap area;
- claim the paper complete from textual presence or a bounded specialization;
- restore a refuted source statement as a theorem;
- author a Tau Ceti code PR against an area with no accepted roadmap target.

## In-repo Tau Ceti-readiness

We do the full prep to be Tau-Ceti-ready **here**, and structure everything as if
the contribution will be accepted — without assuming it will. Concretely:

- **Roadmaps** are drafted in `ForTauCetiRoadmap/` in this repo (mirroring the
  sibling `TauCetiRoadmap` layout: one folder per area, `README.md` definitive,
  `Suggested.lean` for prototype signatures). No external roadmap PR is assumed.
- **Code** is staged in `ForTauCeti/` with final `TauCeti.*` namespaces;
  `scripts/export_for_tauceti.py` reproduces the `TauCeti/` copy on demand.
- **Submission packaging** (the A1--A3 split, acceptance-gate checklists, the
  two-roadmap proposal) lives under `dev/tauceti/`.

When a real Tau Ceti submission is authorized, this material is lifted out
verbatim; until then nothing here depends on external acceptance.

## Convergence phase (Track A / Track B)

Extraction is not "copy `ForMathlib` → `ForTauCeti` → submit." Three
independently evolved operator-theory stacks — DKPS local abstractions, Tau Ceti
canonical abstractions, Spectra donor abstractions — must collapse into one
Tau Ceti-native stack before most PRs, without losing the new Davis--Kahan
mathematics or Spectra provenance. The instrument is the **convergence matrix**
([`dev/tauceti/convergence-matrix.md`](../../dev/tauceti/convergence-matrix.md)):
one row per declaration, classified (exact-duplicate / wrapper-duplicate /
parallel-formulation / missing-reusable-result / paper-specific) with a canonical
destination.

Two tracks run in parallel:

- **Track A (now):** approximation numbers — internal deduplication (Wave 1) then
  the roadmap below. Independent of the unbounded/semigroup/PDE architecture, so
  it does not block on Track B.
- **Track B (now):** the convergence audit and refactor waves — closed operators
  onto `LinearPMap` (Wave 2), semigroups/resolvents (Wave 3), forms/Fredholm/PDE
  (Wave 4), and the Spectra decomposition clusters A--E (Wave 5, incl. the
  PVM/spectral-calculus donor layer). Gates the later PRs.

Overall ordering: `0` inventory/equivalence map → `1` internal dedup → `2`
refactor onto Tau Ceti structures → `3` port missing Spectra foundations → `4`
rewrite DavisKahan consumers → `5` delete old APIs → `6` polish and submit the
residual new mathematics.

## Roadmap sequence (drafted in `ForTauCetiRoadmap/`)

Do not open with a single roadmap for the whole Davis--Kahan paper — that bundles
too many unsettled APIs. Use a focused sequence, each depending on the prior.

1. **Approximation Numbers and Symmetric Operator Ideals** (first): approximation
   numbers for rectangular continuous linear maps; order/scalar/addition/
   composition laws; adjoint invariance; finite-dimensional singular-value
   agreement; min--max characterizations; rectangular operator modulus; symmetric
   ideal families and Ky Fan dominance; orthogonal block sums; Hilbert--Schmidt
   and related ideal examples.
2. **Spectral Subspaces, Sylvester Equations, and Davis--Kahan Perturbation
   Bounds** (later): depends on (1); coordinates its closed-operator layer with
   Tau Ceti's existing one-parameter-semigroup roadmap.

Each roadmap cites the DavisKahan repository only in a provenance/existing-work
section; it specifies the mathematics intrinsically and does not prescribe our
file layout or preserve local wrappers.

## Acceptance gates for any staged Tau Ceti cluster

"Moved to `ForTauCeti` and green" is not "ready." A cluster is ready only when:

- **Roadmap gate** — a drafted `ForTauCetiRoadmap/` target names it; intended
  generality and namespace conventions are settled.
- **Mathematical gate** — no paper-specific assumptions/numbering; independently
  useful; carries the natural basic API, not only the one downstream lemma; every
  excluded theorem has a precise dependency reason, not "later."
- **API gate** — Mathlib/Tau Ceti naming; no duplication of existing Tau Ceti
  structures; no compatibility wrapper presented as canonical; source/target
  universe and scalar generality decided.
- **File gate** — under Tau Ceti's 1000-line new-file limit (1500 hard ceiling);
  minimal imports, public only where part of the exported interface; no
  `set_option`/linter suppression/heartbeat override; module system + durable
  provenance.
- **Verification gate** — from a fresh branch against the pinned Tau Ceti:
  `lake exe cache get && lake build && lake exe axioms && lake exe module-system`
  and the environment lint pass, whole repo green.
- **Downstream gate** — DavisKahan consumers rebuild against the ForTauCeti
  version with no proof change beyond import/namespace migration; frontier,
  source-census, dependency-layer, trusted-dependency audits clean.
- **Cleanup gate** — after a cluster is submission-shaped, no duplicate
  definition of the same declaration remains importable from both `ForMathlib`
  and `ForTauCeti`; the extraction manifest and provenance ledger are updated.

## Submission split (approximation-number cluster) — A0 → A4

The declaration-level adversarial-review audit
([`dev/tauceti-signature-polish-todo.md`](../../dev/tauceti-signature-polish-todo.md))
is the signature-polish instrument. Its central rule: **settle representation
before names — no blanket rename pass**, because renaming a parallel abstraction
only makes the duplication harder to remove. Its PR slicing:

- **A0 — roadmap + representation decisions** (index convention, `ℝ≥0`-vs-`ℝ`
  codomain, `ContinuousLinearMap`-vs-`TauCeti` namespace, canonical modulus name
  and `operatorAbs` deletion, the actual Courant–Fischer equality, one
  Hilbert–Schmidt object, body-hiding). Captured in
  [`ForTauCetiRoadmap/ApproximationNumbers`](../../ForTauCetiRoadmap/ApproximationNumbers/README.md).
- **A1 — `Basic` only**, after conventions settled.
- **A2 — adjoint invariance + finite-dimensional singular-value identification**
  (`Adjoint`, `FiniteDimensional`).
- **A3 — min–max lower bound + Courant–Fischer support**, ending in the actual
  min–max theorem (`MinMax`, `CourantFischer` — the latter split into a generic
  `spanIndices` basis layer and the spectral min–max layer).
- **A4 — one canonical rectangular modulus**, deleting the parallel `operatorAbs`
  API downstream.

`U1` (LinearPMap unbounded-operator convergence) and `S1+` (dependency-closed
Spectra ports) are later roadmaps. A PR must not mix a P0 convergence refactor
with downstream theorem additions. The **pre-PR declaration checklist** (audit
§14) is the per-declaration gate that complements the cluster acceptance gates.
Before any real submission, recheck upstream duplication (current Tau Ceti,
pinned Mathlib, open Mathlib/Tau Ceti PRs, Zulip) — in particular the Mathlib
approximation-number work this was adapted from.

## Current success metric

Measure progress on the primary track by dependency-closed clusters staged in
`ForTauCeti` with a drafted roadmap target and all acceptance gates green, and on
the maintenance track by source endpoints recursively grounded and false source
claims formally resolved.

Do not measure progress by the number of Spectra files copied, Tau Ceti modules
created, or namespaces renamed.

# Tau Ceti adaptation and Spectra extraction plan

**Baseline:** DKPS commit `650b0e3271b8`  
**Tau Ceti reference:** `external/TauCeti` at `92c79e5e0a618f8c5c2b9909be1ce50f6891dde7`  
**Spectra reference/vendor:** `8dbaaf6728d1342ae16acf79fd7eef7c59b37e63`

This document is the operating plan for adapting the Davis--Kahan formalization
to reusable Tau Ceti infrastructure while extracting the Spectra mathematics
that should eventually be contributed with full attribution.

It is written for a strong compiler-capable agent. Do not treat it as
permission for a single bulk namespace migration. The objective is to reduce
foundational duplication without destabilizing the proved paper development.

## Executive decision

1. **Keep both upstream reference submodules.** `external/TauCeti` and
   `external/Spectra` are read-only provenance and comparison checkouts.
2. **Keep the current vendored Spectra build temporarily.** It is the working
   foundation for major parts of the formalization and should not be removed
   until replacement imports compile and the recursive proof audit remains
   green.
3. **Test Tau Ceti as an optional path dependency now.** Do this on an
   integration branch and compile a small import smoke test before changing
   production imports.
4. **Extract by coherent mathematical cluster, not by copying isolated files.**
   Each extraction must have a dependency-closed design, a Tau Ceti target,
   and a provenance record.
5. **Make the permanent dependency direction one-way:**

   ```text
   Mathlib
      ↑
   Tau Ceti reusable mathematics
      ↑
   DKPS adapters / compatibility layer
      ↑
   Davis--Kahan paper formalization
   ```

   Spectra remains a temporary source and dependency during the transition,
   not a permanent parallel foundation.

## Is Spectra maintenance currently a big problem?

Not operationally catastrophic, but it is meaningful architectural debt.

The current maintenance arrangement is disciplined:

- `vendor/Spectra` is documented as a pristine upstream snapshot;
- `external/Spectra` is pinned to the same upstream commit;
- DKPS compatibility edits are recorded in one reproducible patch;
- scripts verify the snapshot, reference checkout, and patch state;
- the pinned Spectra commit is also the current public upstream head as of this
  plan.

The compatibility patch touches **16 files**, with **172 insertions and 104
removals**. That is manageable. The larger problem is coupling:

- DKPS has **57 direct Spectra import edges**;
- those imports name **43 unique Spectra modules**;
- DKPS source refers to approximately **165 distinct `Spectra.*` names**;
- Spectra's own Mathlib pin is much older than the DKPS root pin;
- several imported modules pull in broad physics-facing dependency chains for
  comparatively small operator-theoretic facts.

Therefore:

> Spectra is not currently consuming constant maintenance time, but each future
> Mathlib bump or foundational redesign has a large blast radius. Extraction is
> strategically necessary even if the existing vendor mechanism remains stable.

Do not confuse repository size with the problem. The vendored snapshot is only
about 8.5 MB. The problem is API and dependency-graph ownership.

## What Tau Ceti can save now

Tau Ceti already provides relevant reusable conventions and infrastructure:

- unbounded operators represented using Mathlib `LinearPMap`;
- semigroup generators and generator-domain machinery;
- Lax--Milgram existence/uniqueness wrappers;
- PDE energy-form infrastructure and coercivity-oriented APIs;
- a library culture designed for reusable foundational mathematics.

This can save or redirect work on:

- the generic form-to-operator construction needed by the free-beam example;
- common `LinearPMap` conventions and closed-operator adapters;
- semigroup and generator plumbing;
- coercive-form solution operators;
- placement and API design for extracted Spectra operator theory.

Tau Ceti does **not currently eliminate** the main free-beam analysis. We still
need, somewhere:

- interval `H²` construction or an equivalent weak-derivative form domain;
- endpoint traces;
- compact embedding into `L²`;
- identification of the associated fourth-order operator domain;
- free boundary conditions and self-adjointness;
- compact resolvent and spectral identification.

Adapting now is worthwhile because it prevents those results from being built
in a DKPS-only abstraction, not because Tau Ceti already contains the entire
beam solution.

## Current pin situation

All three projects use Lean 4.32 in the current checkouts. Their Mathlib pins
are different:

| Project | Mathlib commit |
|---|---|
| DKPS | `3dffaf2f18b47d11948f6390838ea6f2ae662aaf` |
| Tau Ceti | `81a5d257c8e410db227a6665ed08f64fea08e997` |
| Spectra | `40f05009d036d2e4b488e8a01f559a6036ec2484` |

The Tau Ceti pin is only tens of commits behind the current DKPS pin, so a root
pin override is plausible. It is not certified until the smoke build succeeds.

## Target repository architecture

### Upstream references

```text
external/TauCeti/   # pristine pinned comparison checkout
external/Spectra/   # pristine pinned provenance checkout
```

Neither should contain project-specific edits.

### Temporary production dependency

```text
vendor/Spectra/     # pristine snapshot plus reproducibly managed patch state
```

Do not create a permanent `vendor/TauCeti` immediately. First attempt to use
Tau Ceti directly as a pinned path package. A vendored Tau Ceti snapshot is a
fallback for reproducibility or compatibility patches, not the first design.

### New local layers

The final names may be adjusted after the smoke test, but preserve this
separation:

```text
TauCetiCandidates/                 # reusable candidate mathematics, no DKPS imports
DavisKahan/Interop/TauCeti/        # adapters from Tau Ceti/Mathlib APIs to DKPS APIs
DavisKahan/Interop/Spectra/        # temporary compatibility and extraction boundary
DavisKahan/...                     # paper-specific mathematics
```

`TauCetiCandidates` should be a separate Lean library or an equivalently strict
namespace/import boundary. A candidate file must not import `DavisKahan`.

## Spectra extraction principles

### Preserve provenance

Every extracted or adapted file must record:

- upstream repository;
- exact source commit;
- original source path or paths;
- original copyright and author header;
- Apache-2.0 license notice;
- a concise summary of changes;
- the DKPS and eventual Tau Ceti destination paths.

Retain original file-level headers when a file is substantially derived from a
Spectra file. For a theorem assembled from several files, include an explicit
`Adapted from` block in the module documentation and an entry in the extraction
ledger.

Do not rewrite a Spectra theorem from memory and then omit attribution because
its Lean syntax changed substantially. Mathematical and proof-architecture
provenance still matters.

### Extract dependency-closed clusters

Do not copy a leaf module while silently importing half of Spectra. For each
cluster:

1. identify the exact declarations DKPS uses;
2. compute their local Spectra dependency closure;
3. compare each dependency with Mathlib and Tau Ceti;
4. replace existing equivalents first;
5. extract only the irreducible missing mathematics;
6. design the public API in Tau Ceti idiom;
7. add a DKPS adapter;
8. migrate consumers;
9. remove the old Spectra import only after the replacement compiles.

### Prefer API preservation at the adapter boundary

During migration, adapters may expose names close to current DKPS expectations.
The reusable Tau Ceti candidate should not preserve an unsuitable Spectra API
merely to minimize local edits.

## Extraction clusters and priorities

The generated inventory is:

```text
dev/upstream-extraction/spectra-usage-inventory-650b0e3.json
```

It lists every direct import edge, namespace reference, and an initially blank
module-disposition ledger.

### Priority 1: unbounded operator and resolvent core

Relevant imports include:

- `Spectra.Operator.SelfAdjoint`;
- `Spectra.Operator.KatoRellich`;
- `Spectra.Resolvent.*`;
- `Spectra.SpectralTheory.ResolventForm`.

Goals:

- align public unbounded-operator statements with Mathlib `LinearPMap`;
- compare Tau Ceti's existing generator and operator conventions;
- isolate Spectra-specific wrappers from genuinely missing theorems;
- avoid exposing the local `DavisKahanExt.ClosedOperator` as the reusable API.

This cluster is central to both the general spectral theory and the free-beam
realization.

### Priority 2: PVM, spectral theorem, and bounded Borel calculus

Relevant imports include:

- `Spectra.ProjValMeasure.Basic`;
- `Spectra.SpectralTheory.Measure.*`;
- `Spectra.SpectralTheory.ResolventForm`;
- `Spectra.SpectralTheory.Calculus.*`;
- `Spectra.StoneBridge.CalculusBridge`.

This is the most important and potentially largest extraction. Do not begin by
porting the entire Spectra spectral hierarchy. First enumerate the exact public
facts DKPS requires:

- existence and uniqueness of the spectral PVM;
- spectral projections and complements;
- bounded Borel functional calculus;
- indicator-function projections;
- intertwining/reduction results;
- spectrum and resolvent identities used by DKPS.

Decide whether Tau Ceti should receive one coherent roadmap or several staged
roadmaps.

### Priority 3: semigroup, Stone, and Cayley infrastructure

Relevant imports include:

- `Spectra.YosidaHille.*`;
- `Spectra.CayleyTransform.BorelCalculus`;
- Stone-group/calculus bridges.

Tau Ceti already has semigroup-generator infrastructure. Compare before
extracting. Likely outcomes:

- reuse Tau Ceti definitions;
- port only self-adjoint/Stone specialization theorems;
- provide compatibility lemmas for DKPS's existing Spectra-shaped uses.

### Priority 4: Hilbert--Schmidt operators

Relevant imports include:

- `Spectra.Spaces.Tensor.HilbertSchmidt`;
- spectral-gap and generator bridge modules;
- selected trace-class basics.

This cluster already overlaps with compiled DKPS scratch work. Reconcile the two
implementations before upstreaming either. Preserve the Spectra attribution in
any combined result; the current Spectra Hilbert--Schmidt module itself records
Jon Crall and OpenAI GPT-5.6 Thinking as authors.

Target outcomes:

- one coordinate-free rectangular Hilbert--Schmidt space;
- real and complex versions or a justified scalar abstraction;
- completeness and operator-norm domination;
- ideal composition;
- Bochner integration;
- the spectral-gap Sylvester specialization as a downstream theorem.

### Priority 5: polar decomposition and partial isometries

Relevant imports include:

- `Spectra.QuantumMechanics.Channels.PolarDecomp`;
- `...TraceClass.PartialIsometry`.

Extract the operator-theory content without the quantum-channel namespace.
This is directly relevant to the remaining nonacute Section 3 campaign.

### Priority 6: specialized physics dependencies

Born-rule and modular-theory modules are currently imported by some DKPS files.
Do not port them wholesale merely because they occur in an import closure.
Extract the minimal generic measure, PVM, or functional-calculus facts and
replace the physics-facing import where practical.

## Phased implementation plan

### Phase 0: freeze and verify the current baseline

Before integration work:

```bash
python3 scripts/verify_vendored_spectra.py
python3 scripts/verify_spectra_reference.py
python3 scripts/spectra_compatibility_patch.py verify
lake build
python3 scripts/check_davis_kahan_frontier.py --write-report
```

Record failures rather than repairing unrelated mathematics in the adaptation
branch.

### Phase 1: Tau Ceti smoke integration

On a dedicated branch:

1. add Tau Ceti as a path requirement before the authoritative root Mathlib
   requirement;
2. leave Tau Ceti out of the default targets;
3. create a small smoke module importing only specific modules;
4. compile against the DKPS root pin;
5. record every compatibility issue;
6. do not migrate production imports yet.

Suggested smoke imports:

```lean
import TauCeti.Analysis.InnerProductSpace.LaxMilgram
import TauCeti.Analysis.PDE.EnergyForm.Basic
import TauCeti.Analysis.Semigroups.Generator.Basic

#check TauCeti.IsCoercive.solutionOfFunctional
#check TauCeti.Semigroups.StronglyContinuousSemigroup.generator
```

Success criterion: the imports compile under the DKPS root toolchain and
Mathlib pin with no edits inside `external/TauCeti`.

If edits are needed, classify them:

- fixed upstream already;
- small DKPS pin compatibility patch;
- true API conflict;
- incompatible transitive dependency.

### Phase 2: complete the disposition ledger

For each of the 43 directly imported Spectra modules, set one decision:

- `retain-temporarily`;
- `replace-with-mathlib`;
- `replace-with-tauceti`;
- `extract-to-tauceti`;
- `keep-dkps-local`;
- `remove-unused`.

For `extract-to-tauceti`, provide the candidate destination and dependency
closure. No module remains `unclassified` at the end of this phase.

### Phase 3: choose one pilot cluster

The recommended pilot is **semigroup/Stone/Cayley**, because Tau Ceti already
has adjacent infrastructure and the cluster is smaller than the full PVM
hierarchy.

Alternative pilot: **Hilbert--Schmidt**, if its scratch implementation has
already compiled cleanly and can be reconciled with the Spectra version.

Do not choose the whole spectral theorem as the first pilot.

Pilot definition of done:

- candidate files compile independently of `DavisKahan`;
- provenance is complete;
- Tau Ceti-style APIs are documented;
- DKPS adapter compiles;
- at least one existing Spectra import is removed;
- default DKPS build and proof audit do not regress.

### Phase 4: upstream contribution workflow

For each coherent contribution:

1. register/confirm the Tau Ceti roadmap or intention;
2. port to Tau Ceti's current Mathlib master pin;
3. retain Spectra attribution and Apache notice;
4. open a narrowly scoped Tau Ceti contribution;
5. keep the DKPS adapter against the local candidate until upstream lands;
6. switch the adapter to upstream Tau Ceti after merge;
7. delete the duplicate local candidate only after downstream migration.

### Phase 5: retire Spectra incrementally

Track the count of direct Spectra import edges. The migration is complete when:

- the count is zero in production DKPS modules;
- no default target requires `vendor/Spectra`;
- every extracted theorem has provenance and a stable home;
- the default build and recursive frontier audit pass;
- the Spectra vendor and compatibility patch can be removed in one final,
  reviewable commit.

Do not remove `external/Spectra` immediately. It remains valuable provenance
for at least one release or audit cycle after the build dependency disappears.

## Major restructuring policy

A major restructuring is expected, but it must be staged.

Allowed early:

- adding an optional Tau Ceti package requirement;
- adding candidate and adapter libraries;
- moving Spectra-facing glue behind `DavisKahan/Interop/Spectra`;
- adding provenance ledgers and smoke tests.

Deferred until APIs stabilize:

- replacing the local closed-operator type globally;
- mass-renaming spectral projections or functional-calculus declarations;
- deleting the Spectra vendor;
- rewriting all source-theorem imports in one commit;
- merging foundational and paper-specific namespaces.

Each structural commit should either preserve theorem statements or explicitly
record statement changes. Do not mix a large API migration with new
mathematics unless unavoidable.

## Instructions for Opus

Start by reading:

```text
docs/planning/tauceti-adaptation-and-spectra-extraction.md
dev/upstream-extraction/spectra-usage-inventory-650b0e3.json
vendor/Spectra.UPSTREAM.md
vendor/patches/Spectra/README.md
dev/LANES.md
```

First assignment:

1. verify the current Spectra vendor state;
2. create a Tau Ceti path-dependency smoke-test commit;
3. compile the three suggested Tau Ceti modules;
4. write `dev/tauceti-compatibility-report.md` containing exact errors and
   recommended fixes;
5. fill the disposition ledger for the semigroup/Stone/Cayley cluster;
6. propose one pilot extraction with exact source files, declarations,
   dependencies, target modules, and attribution blocks;
7. do **not** begin the extraction until the report is reviewed.

Required reporting:

- exact commits and pins;
- exact commands run;
- default-build effect;
- files modified;
- upstream files consulted;
- declarations proposed for reuse or extraction;
- attribution plan;
- collision check against active agent lanes;
- rollback instructions.

## Success metrics

Track these numbers after every adaptation campaign:

- direct Spectra import edges;
- unique Spectra modules imported;
- compatibility-patch files and changed lines;
- Tau Ceti imports used by DKPS adapters;
- extracted modules accepted upstream;
- duplicate local candidate modules remaining;
- default build status;
- recursively grounded frontier endpoints.

The immediate goal is not to make the Spectra import count zero. The immediate
goal is to turn an implicit dependency into an explicit, attributed, staged
migration whose first pilot proves the architecture works.

# ForTauCeti — the reusable-mathematics package

> **EXECUTIVE DECISION — jon, 2026-07-29. This section replaces the "temporary
> staging layer" framing this file used to open with, and it changes what the
> work is.**
>
> **`ForTauCeti` is the product, not a holding pen.** The goal is an *elegant
> package* here: coherent API, one canonical spelling per concept, provenance
> on every module. That package is what **polished roadmaps are generated
> from**, and the roadmaps are then satisfied by **mechanical ports**.
>
> Two consequences, both the opposite of what this file said before:
>
> * **Deleting `ForTauCeti` is not on the roadmap.** There is no terminal state
>   in which it is empty. Do not write a lane that ends in its deletion, and do
>   not re-add a "delete the staging files" step to the lifecycle below.
> * **`external/TauCeti` is a read-only provenance reference** (`AGENTS.md`).
>   Stage here; do not write into the submodule. `export_for_tauceti.py --write`
>   belongs to an actual submission, not to ordinary work — run `--check`
>   freely, and expect `--write` to leave untracked, silently-staling copies in
>   the submodule if you run it otherwise. That has happened twice.

`ForTauCeti` holds reusable, paper-agnostic mathematics extracted from the
Davis--Kahan development. The layering is:

```text
Mathlib
   ↓
TauCeti           (external/TauCeti, read-only provenance reference)
   ↓
ForTauCeti        (this library — the package, organised into
                   dependency-closed clusters)
   ↓
DavisKahan        (paper-facing perturbation theory)
```

**The clusters are the roadmap units.** `dev/tauceti/extraction-manifest.json`
declares all 156 modules across 18 dependency-closed clusters, each computed as
an import closure and each passing the import firewall — so any one of them can
be read, reviewed, or ported as a self-contained unit. A module that is not in
the manifest is invisible to that machinery; keep it at 156/156.

## Relationship to `ForMathlib`

**`ForMathlib` is being retired into `ForTauCeti`** (jon's decision,
2026-07-29). It is not a parallel staging area to be maintained alongside this
one. Modules migrate here as their import closures allow, following the
CourantFischer playbook recorded in `dev/tauceti/convergence-matrix.md`: move
the closed component, repoint consumers, delete the old file. Mathlib is not the
near-term target for this contribution; Tau Ceti is.

**The end state is settled: `ForMathlib` goes away entirely** (jon,
2026-07-29). Whatever the elegant package needs moves here; anything left over
is not retained as a Mathlib-bound remainder. `ForTauCeti` is *the* mathematics
library this repository builds, and **every paper proof is built on it** —
`DavisKahan`, `Acharyya2024`, `Acharyya2025`, `Helm2025`, `DkpsQuench2026`,
`FinishTanTwoTheta`, `FinishYuWangSamworth`. There is no second staging area and
no "genuinely Mathlib-shaped" exemption. Earlier text describing the four
survivors as a deliberate Mathlib-bound remainder is superseded by this
paragraph.

**Done, 2026-07-29 (`jon (yardrat)`, lane FM-RETIRE):** the four moved, the
library, its root module and its directory were deleted, and `ForMathlib` no
longer exists in the tree. The paragraph below is kept as the specification the
lane was executed against; the downstream pins it warns about were all repointed
(`comparator/pending-{berge,rank-factorization,rank-psd-realization}.json` and
the three `Challenge/**/Leaderboard.lean` files now read `TauCeti.*`), and the
declarations were renamed out of `ForMathlib` into `TauCeti` — see
`ForTauCeti/Topology/Berge.lean` for why that was the right call when a parallel
version of the same lane had decided otherwise.

Four modules remain (799 lines), and they are **not** blocked by the import
firewall — the internal edges are only `PosDef → RankFactorization` and
`Berge → ApproxMinimizer`, so they move as two independent pairs. What makes the
lane non-trivial is downstream: five declaration names are pinned as *data* in
`comparator/pending-{berge,rank-factorization,rank-psd-realization}.json`, and
three `Challenge/MathlibPending/**/Leaderboard.lean` files name them in
`#print axioms`. `Challenge` is outside `defaultTargets`, so a green default
build proves nothing about them — see the comparator challenge rule in
`AGENTS.md`. The measured lane is posted in `dev/LANES.md`.

**A module docstring reading `Extraction class: authored in place, for
upstreaming to Mathlib rather than to Tau Ceti` is stale, and is not a bar to
migrating that module.** Those lines predate the dual-track policy in
`AGENTS.md` and have not been treated as blocking for comparable modules all
week. Reading this section's *previous* wording as live policy cost one session
two reversed lanes; that is why the wording is now explicit.

### File headers name Tau Ceti, and there is no re-authoring step (2026-07-29)

Two header conventions, both settled by lane HDR-DEST after an audit found 39
files stating the wrong destination:

- **A header says `Staged for Tau Ceti, roadmap topic Tnn`**, not *staged for
  Mathlib*. Where a header previously named a `Mathlib/...` file, that path is
  kept but explicitly marked as where the material *would have gone on the
  closed Mathlib track* — it is history and orientation, not a destination. Real
  Mathlib history is untouched: `Analysis/InnerProductSpace/Basic.lean` was
  genuinely submitted as PR #40567 and reshaped on @wwylele's review, and its
  header still says so.
- **The instruction `To be re-authored per Mathlib's AI-contribution policy at
  PR time` is deleted, not redirected**, in all 35 files that carried it. Tau
  Ceti has no such requirement to redirect it to: it describes itself as a
  library *"implemented and maintained by AI contributors, subject to
  adversarial review"* (`external/TauCeti/README.md`), and attribution is one of
  its review rubrics rather than a bar to entry. The `Formalized by …` line stays
  for exactly that reason.

If you are adding a module, write the first form and omit the second.

The real constraint is the import firewall below, not a docstring. Because
`ForTauCeti` may not import `ForMathlib`, a `ForMathlib` module becomes
migratable only once no remaining `ForMathlib` file imports it — so components
move whole, in dependency order, and the last `ForMathlib → ForTauCeti` edge
must never exist even transiently.

### Why there is no `@[grind]` in this library (2026-07-30)

Tau Ceti's `api-design` rubric asks for `@[grind]` on the lemmas that should drive
`grind`, and flags a characteristic lemma that should carry one and does not. This
library has **178 `@[simp]` and zero `@[grind]`**, so lane `RUB-GRIND` ran the
experiment rather than leaving the reviewer's question unanswered.

**`grind` does not drive this library's characteristic lemmas, for two structural
reasons.** Probed on approximation-number goals with the relevant lemmas passed
explicitly:

- **Bundled order predicates are opaque to it.** `approximationNumber_antitone` is
  stated as `Antitone T.approximationNumber`. `grind` asserts that as a fact and
  then cannot instantiate it: given `m ≤ n` it lists `Antitone …` among its true
  propositions and still fails to derive `aₙ ≤ aₘ`. The same shape recurs in the
  `IsLUB` family.
- **`Cardinal`-valued side conditions defeat matching.**
  `approximationNumber_le_norm_sub` is a plain implication, which is the shape
  `grind` likes, but its hypothesis is `R.rank ≤ (n : Cardinal)`; `grind`
  normalises that to `Module.rank 𝕜 (Subtype (Membership.mem (↑R).range)) ≤ ↑n`
  and no longer matches the lemma.

Goals needing a *single* lemma and no side condition do close (`0 ≤ aₙ(T)`,
`aₙ(0) = 0`). That is not worth an attribute.

**What would change the answer**, and either is a reasonable future lane: giving
the order-predicate lemmas plain-implication companions, or moving the rank side
conditions to the `ℕ`-valued `finrank` form the finite-dimensional API already
uses. Until then, annotating would advertise automation that does not fire.

## Hard rules

### 1. Import firewall

A `ForTauCeti` module may import **only**:

```text
Mathlib.*
TauCeti.*
ForTauCeti.*
```

It may **not** import any of:

```text
DavisKahan.*
ForMathlib.*
Spectra.*
Acharyya2024.*   Acharyya2025.*   DkpsQuench2026.*   Helm2025.*
Challenge.*
```

Consequence: a PR-ready `ForTauCeti` cluster is **independently copyable** into
Tau Ceti with only a module-path/import rewrite. This is enforced by
`scripts/check_dependency_layers.py`. Do not hide a forbidden import behind an
aggregate module.

### 2. Final namespaces from day one

Declarations here already live in their **intended final** namespaces. Do **not**
wrap them in a `ForTauCeti` namespace. The module *path* is temporarily
`ForTauCeti...`, but declaration *names* are already the names they will carry in
Tau Ceti, so that integration is a file move, not a mass rename.

**Everything goes under `namespace TauCeti`, including material that extends a Mathlib
type's namespace.** A declaration about `A : E →L[𝕜] E` is written

```lean
namespace TauCeti
namespace ContinuousLinearMap
open TauCeti          -- needed even here; see below
def LowerFormBoundOn (A : E →L[𝕜] E) … 
end ContinuousLinearMap
end TauCeti
```

giving `TauCeti.ContinuousLinearMap.LowerFormBoundOn`. This matches the destination
library: see `external/TauCeti`, `Analysis/Fredholm/Basic.lean` (`namespace TauCeti` at 51,
`namespace ContinuousLinearMap` at 202) and `LinearAlgebra/TotallyReal.lean` (`namespace
TauCeti` at 21, `namespace Submodule` at 99). Tau Ceti never extends a root Mathlib
namespace.

**Why, and it is not stylistic.** This repository cannot upstream to Mathlib — Mathlib does
not accept AI-authored contributions, which is the reason Tau Ceti exists. So a name taken
in a root Mathlib namespace is a bet that Mathlib will never want it, and a bet that can
never be settled by coordination: if Mathlib later adds `ContinuousLinearMap.foo`, our
`ContinuousLinearMap.foo` becomes ambiguous at every use site and *we* must rename.
`TauCeti.ContinuousLinearMap.foo` cannot collide with anything Mathlib does, ever.

**Dot notation still works, through `open TauCeti`.** An earlier version of this rule
claimed that nesting "would break every dot-notation proof". That is half right and the
half that is wrong matters. Measured:

| context | `A.LowerFormBoundOn` resolves? |
|---|---|
| inside `namespace TauCeti` | **no** |
| with `open TauCeti` | **yes** |
| neither | no |

Field projection consults `open`s, not the enclosing namespace — so a file that merely sits
inside `namespace TauCeti` is *not* covered, which is the trap. Every file using dot notation
on these declarations needs `open TauCeti`, **including the file that declares them**.

**Write all new material this way.** The rest of this section is the outstanding migration.

## TODO: migrate ~40 files off root Mathlib namespaces

`Analysis/InnerProductSpace/QuadraticFormBounds.lean` is converted as a validated pilot;
it needed `open TauCeti` in four consumers (`SpectralOrder/Real`, `SpectralOrder/Complex`,
`BoundedOperator/SinTheta`, `BoundedOperator/Projector`). **Roughly 39 files and ~390
declarations remain.**

A scripted bulk pass was attempted and reverted. It does not converge, because the files
are not structurally uniform. Do this **per file, verified individually**, the way the pilot
was done. The four failure classes, all with known remedies:

1. **Trailing bare `end`.** A file ending with `end` (closing a `section` or `noncomputable
   section`) needs `end TauCeti` at EOF, *after* it — not after the last named `end`.
   Getting this backwards breaks ~10 files one way and ~2 the other.
2. **Root-level declarations before the namespace block.** `PartialIsometry.lean` defines
   `IsPartialIsometry` at root and *then* opens `namespace IsPartialIsometry`. Wrap the whole
   file body, from after the last `import`, or the definition is left behind. Note `open
   IsPartialIsometry` fails there — it is a definition, not a namespace.
3. **Bare-name resolution.** Inside root `namespace LinearMap`, a proof may write `rank` for
   `LinearMap.rank`; inside `TauCeti.LinearMap` it cannot. Add `open LinearMap` — but only
   where that namespace genuinely exists, and only where the build asks for it.
4. **Ambiguity.** An `open` can make a name ambiguous rather than resolve it (`map_sub`
   against `_root_.map_sub`). Fix by dropping the unnecessary `open` or qualifying with
   `_root_.`. **Do not add `open`s speculatively** — every ambiguity seen so far was caused by
   an `open` that the file did not need.

**Seven of the ~40 already contain a `namespace TauCeti` block** and need their two blocks
merged rather than a wrap; they are the ones to leave for last, along with
`CourantFischer`, `HilbertSchmidt/Energy`, `LinearPMap/SubmoduleAdjoint`, `Polar/Isometry`,
`Polar/PartialIsometry`, `Sylvester/Operator` and `LinearAlgebra/Dimension/RankComp`.

**Consumers outside `ForTauCeti` were never reached** — `DavisKahan`, `FinishYuWangSamworth`,
`FinishTanTwoTheta`, `Challenge` and the paper libraries all import this one and will need
their own `open TauCeti` pass. Build every library, not just `defaultTargets`.

Nothing here changes any mathematics: every failure observed was name resolution, and the
apparent proof breakage (`unsolved goals`, `Type mismatch`) was cascade from unresolved names
in the same file. A green build across all eleven libraries is proof of correctness.

### 3. Mirror the final destination tree

Module paths mirror the eventual Tau Ceti destination so the mapping is
mechanical:

```text
ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Basic.lean
  → external/TauCeti/TauCeti/Analysis/OperatorIdeal/ApproximationNumber/Basic.lean
```

The one exception is a shared helper whose Tau Ceti home is a different subtree
than the cluster that consumes it (e.g. `ForTauCeti/Analysis/InnerProductSpace/CourantFischer.lean`
→ `TauCeti/Analysis/InnerProductSpace/CourantFischer.lean`); the extraction
manifest (`dev/tauceti/extraction-manifest.json`) records the exact map.

### 4. Tau Ceti module style immediately

Every staging file already uses the Tau Ceti / Lean module system:

```lean
/- <original copyright header, preserved verbatim> -/
module

public import Mathlib...

/-!
# ...
## Provenance
...
-/

public section

namespace ...
...
end ...
```

* Use `public import` for every import (implementation-only imports may stay
  private, but the approximation-number cluster's public interface needs its
  imports public).
* **`public section`, not `@[expose] public section`. Keep definition bodies
  hidden by default.** Reach for `@[expose]` only on the individual declaration
  whose body a consumer must genuinely unfold or compute with, and say in the
  docstring why. **If the reason is that a downstream proof wants `rfl` or
  `change`, that is not a reason to expose — it is a missing lemma.** Write the
  characteristic lemma instead (`foo_def`, `foo_apply`, `mem_foo_iff`), and note
  that `:= (rfl)` rather than `:= rfl` avoids making downstream lemmas depend on
  defeq in the first place.

  **Decided by jon, 2026-07-30, adopting the Tau Ceti convention over ours.**
  This reverses the previous rule, which mandated `@[expose] public section` on
  every module and justified it as *"several proofs use `rfl`/`change` that
  require definition bodies to be exposed."* `TauCetiReview/rubrics/api-design.md`
  names that exact reasoning as the defect it rejects: *"Do not expose bodies to
  compensate for missing lemmas … ask for the missing lemma instead."* Exposing
  a body makes the implementation part of the public contract, so a later change
  that preserves every stated lemma can still break a consumer. **70 of 167
  existing files still carry the old pattern**; lane `FTC-EXPOSE-MEASURE` and
  its follow-ons convert them. New files follow the rule above from today.
* Do **not** use `set_option` to silence limits or linters.
* Files must be **warning-clean** (Tau Ceti builds with `warningAsError`) and
  below the 1000-line new-file limit.

### 5. Provenance

Every staged module includes a `## Provenance` section recording: original
repository, exact source commit, original module path(s), original declaration
names, original authors/copyright, license, extraction class (copied / adapted /
generalized / specialized / re-proved), whether Spectra influenced the selection
or proof, and any semantic change from the Davis–Kahan version. Kitware and
third-party attribution is **preserved**, never erased.

## `ForTauCeti` is the deliverable — do not "finish" by deleting it

**Read this before the lifecycle steps below.** Agents have repeatedly tried to
complete this work by merging code directly into `TauCeti` and deleting
`ForTauCeti` (jon, 2026-07-29). That is not the goal and it destroys the
actual product.

The goal is to make `ForTauCeti` **an elegant, self-consistent package**, and
then use that package to generate two things:

1. **polished roadmaps** — drafted in
   [`../submodules/TauCetiRoadmap/`](../submodules/TauCetiRoadmap/README.md); and
2. **mechanical ports** that satisfy those roadmaps.

The `TauCeti/` copy is an **output**, produced on demand by
`scripts/export_for_tauceti.py` — it is generated, never hand-applied. This is
why `AGENTS.md` says not to commit the `external/TauCeti` submodule pointer yet.

So: improvements go **into** `ForTauCeti`. A task that sounds like "move
`ForTauCeti` into `TauCeti`" is asking for an *export*. Never empty or delete
`ForTauCeti/` as a way of declaring the migration done.

### This package is a rehearsal — treat it as real

**jon, 2026-07-30.** `ForTauCeti` is a mock of the Tau Ceti PR contents. It exists so
that **when we make the effort to do the real submission, it goes smoothly.**

So work on them as though they were the real repositories — no hedging, no
provisional marking, no waiting on upstream. **The acceptance test is a
demonstration:** we show this repository to Tau Ceti and they say *"yes, that's
ready — submit these roadmaps as PRs, then push up the code and merge it."*
Anything that would make a reviewer hesitate at that moment is a defect and
needs a lane.

**No lane is ever blocked on upstream acceptance.** How the clusters go upstream
is a genuine open question, but it is never a prerequisite for work here.

### The readiness standard — the platonic ideal roadmap

When a Tau Ceti roadmap is **accepted**, we use `ForTauCeti` to open a PR
against Tau Ceti. The work before that point is not "wait for acceptance"; it is
to get `ForTauCeti` to the state where it **satisfies the platonic ideal Tau
Ceti roadmap** — so that whatever roadmap is actually accepted, we are already
confident we have everything needed to satisfy it (jon, 2026-07-29).

That is a deliberately higher bar than "our own roadmap draft is met." Writing
the roadmap ourselves and then meeting it proves nothing about what a Tau Ceti
reviewer will ask for. The target is the roadmap a reviewer *would* write.

Readiness therefore includes, and is not complete without:

- **paper references** — every result traceable to its source, with the
  provenance block §5 requires;
- **Tau Ceti adversarial review** — the statement attacked before submission,
  not after: wrong generality, a hypothesis that trivializes the conclusion, a
  name that overclaims, a result Mathlib or Tau Ceti already has;
- **elegance at Mathlib quality** — the API shape, naming, proof locality,
  docstring coverage, import minimality, and warning-cleanliness that survive an
  unsympathetic reviewer.

Concretely: a cluster is ready when nothing in it would be sent back. Until
then, polishing `ForTauCeti` *is* the submission work — not a prelude to it.

## What the Tau Ceti merge machinery actually requires

**Read out of `TauCetiReview/runner/verdict.py` and `runner/merge.py`, not
inferred.** Both facts constrain how the port is *built*, so they belong here
rather than being discovered at PR time.

**1. All ten rubrics must be green on one single commit.** `state_of` marks an
`approve` **green only when `approved_sha == head_sha`**; on any other head it
becomes **`stale`**, and a never-run rubric counts as blocking too. `decide_merge`
then requires every blocking rubric green on `HEAD`, *"fresh, not stale"*.

Approvals therefore **do not accumulate** across a fix-and-push cycle: pushing a
fix for rubric 7 invalidates the approvals already earned from rubrics 1–6.
There is no submit-early-and-grind-it-down path. Whatever commit we intend to
merge has to satisfy all ten *simultaneously* — which is the argument for
finishing every lane before the PR opens, and for not opening it while a lane is
mid-flight.

**2. The diff must be confined to the library subtree.** `decide_merge` demands
`code_only`: every changed path under `MERGE_PREFIX` (`TauCeti/`) or in the root
allowlist, which is exactly

```
TauCeti.lean, lake-manifest.json, lean-toolchain
```

Anything else returns *"PR touches paths outside TauCeti/ … needs human merge"*.
This repository interleaves the library with `dev/`, `scripts/`, `docs/`,
`Challenge/`, `DavisKahan/` and the roadmap tree, and **none of it may ride
along** — so the mechanical port must emit a `TauCeti/`-confined diff. A Lake
pin change additionally needs a green bump-guard, so the port should not move
`lean-toolchain` or the manifest casually.

**One topic per PR.** `rubrics/scope.md` blocks a PR that is more than one
topic, so the clusters go up individually, not as a single submission.

**A note on `scope`, which cannot be satisfied from inside this repo.** The real
reviewer reads `TauCetiProject/TauCetiRoadmap`.
That is a fact about the real run and is recorded in
[`dev/audit/TAUCETI-RUBRIC-REVIEW.md`](../dev/audit/TAUCETI-RUBRIC-REVIEW.md).
It is **not** a defect in present work: per jon (2026-07-30) we rehearse against
our own roadmap, and no lane is ever blocked on upstream acceptance.

## Lifecycle (per cluster)

**Precondition — this sequence applies only *after* a cluster has actually been
accepted upstream by Tau Ceti.** No cluster has been accepted yet: every row in
*Current contents* below reads `staged-*`, and the governance gate in
`AGENTS.md` (accepted roadmap target, one topic per PR, green build, standard
axiom allowlist) has not yet been cleared by anything. Until an acceptance
exists, **step 3 is not work that is available to do**, and an agent that runs
it is deleting the package rather than shipping it.

When a cluster is accepted into Tau Ceti:

1. update the `external/TauCeti` submodule pin to the merge commit;
2. replace this repo's `ForTauCeti.*` imports of the cluster with `TauCeti.*`;
3. ~~delete the corresponding `ForTauCeti/...` staging files~~ — **struck by
   executive decision (jon, 2026-07-29): the staging files stay.** Do not
   delete them, and do not re-add this step;
4. remove compatibility aliases that no longer have downstream users;
5. rerun the Davis–Kahan grounding, layering, and build audits.

**On `external/TauCeti`.** It is a **read-only provenance reference**, as
`AGENTS.md` says. Work is staged in `ForTauCeti` and nothing is written into
the submodule outside an actual submission. `scripts/export_for_tauceti.py
--write` reproduces the `TauCeti/` copy *at submission time* — running it
otherwise leaves untracked copies in the submodule working tree that go stale
against staging, which has already happened twice and is what made
`--check` fail for `principal-angles`. **Use `--check` freely; treat `--write`
as part of a submission, not part of a build.**

Use `scripts/export_for_tauceti.py --cluster <name> --check|--write` to perform
the deterministic staging→Tau Ceti copy (manifest-driven, import-rewriting,
forbidden-import-refusing).

## Current contents

| Cluster | Modules | Status |
| --- | --- | --- |
| `approximation-number` | 22 | staged-needs-current-validation |
| `cstar-gap-inverse` | 1 | staged-unreviewed |
| `fourier-haagerup-zsido` | 8 | staged-unreviewed |
| `hoffman-wielandt` | 4 | staged-unreviewed |
| `linear-pmap-sylvester` | 2 | staged-unreviewed |
| `matrix-spectral` | 7 | staged-unreviewed |
| `measure-theory-helpers` | 4 | staged-unreviewed |
| `operator-polar-decomposition` | 15 | staged-unreviewed |
| `orthogonal-series` | 1 | staged-unreviewed |
| `principal-angles` | 6 | staged-unreviewed |
| `probability-concentration` | 11 | staged-unreviewed |
| `unitarily-invariant-norm` | 28 | staged-unreviewed |

All **83** staged modules on disk are declared (the column sums to 109 because
clusters overlap on shared prerequisites). A cluster's module list is the
**import closure** of its roots, so exporting one yields a self-contained Tau Ceti
subtree; clusters therefore overlap on shared prerequisites, which is intended.

### Upstream gate

`lean_lib ForTauCeti` mirrors the `leanOptions` of Tau Ceti's own `lean_lib`
(`external/TauCeti/lakefile.toml`): `mathlibStandardSet`, a 1500-line ceiling, and
`warningAsError`. That is deliberate. Before 2026-07-28 this library carried no
`leanOptions` at all, so "`lake build ForTauCeti` is warning-free" was measured against
a strictly weaker linter set than the one that gates the PR — the census under upstream's
options was **78**, against 0 under ours. Do not remove these options to make a build
pass; a warning here is a warning Tau Ceti's CI would reject.

Current state against that gate: **0 warnings**, every module under the 1000-line
new-file guard, every module carrying an Apache-2.0 header and a `## Provenance`
section, and `scripts/export_for_tauceti.py --check` green for all clusters.

See `dev/tauceti/extraction-manifest.json` for the per-module record and
`dev/tauceti/extraction-cluster-classification.md` for the full Tier 1–3 queue.

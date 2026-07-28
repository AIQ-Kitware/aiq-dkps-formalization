# ForTauCeti — temporary Tau Ceti extraction staging layer

`ForTauCeti` is a **temporary** Lean library. It holds reusable, paper-agnostic
mathematics whose accepted Tau Ceti roadmap target and public API are settled,
but whose code has not yet merged into the Tau Ceti repository
(`external/TauCeti`). It is the middle layer of the staged extraction
architecture:

```text
Mathlib
   ↓
TauCeti           (external/TauCeti, the permanent generic library)
   ↓
ForTauCeti        (this library — temporary staging, PR-ready clusters)
   ↓
DavisKahan        (paper-facing perturbation theory)
```

Its successful terminal state is **empty or deleted**: every cluster here is
destined to move into `external/TauCeti/TauCeti/...`, after which its staging
files are removed and its `ForTauCeti.*` importers are repointed at `TauCeti.*`.

`ForTauCeti` is **not** the intended permanent public library, and no one should
mistake it for one. The permanent public home is Tau Ceti.

## Relationship to `ForMathlib`

`ForMathlib` is a *separate* staging area for declarations genuinely intended for
Mathlib. It is not automatically upstream of Tau Ceti and is not a generic
dumping ground. A declaration lives in `ForTauCeti` when its accepted home is the
Tau Ceti library; it lives in `ForMathlib` when its accepted home is Mathlib
itself.

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

Two namespace forms appear, both final:

* **Extensions of canonical Mathlib namespaces** — e.g.
  `ContinuousLinearMap.approximationNumber`, `Cardinal.le_natCast_of_lift_le`.
  These stay in the Mathlib namespace so that dot notation resolves and the name
  matches the eventual Mathlib upstreaming target. (Lean field projection binds
  `T.approximationNumber` only to a literal `ContinuousLinearMap.approximationNumber`
  and does not consult an enclosing `TauCeti` namespace, so wrapping these in
  `namespace TauCeti` would break every dot-notation proof. This is flagged for
  Tau Ceti maintainer review.)
* **New generic declarations** — placed under `namespace TauCeti` (e.g.
  `TauCeti.specSubspace`), the Tau Ceti house convention.

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

@[expose] public section

namespace ...
...
end ...
```

* Use `public import` for every import (implementation-only imports may stay
  private, but the approximation-number cluster's public interface needs its
  imports public).
* `@[expose] public section` (not plain `public section`) — several proofs use
  `rfl`/`change` that require definition bodies to be exposed.
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

## Lifecycle (per cluster)

When a cluster is accepted into Tau Ceti:

1. update the `external/TauCeti` submodule pin to the merge commit;
2. replace this repo's `ForTauCeti.*` imports of the cluster with `TauCeti.*`;
3. delete the corresponding `ForTauCeti/...` staging files;
4. remove compatibility aliases that no longer have downstream users;
5. rerun the Davis–Kahan grounding, layering, and build audits.

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

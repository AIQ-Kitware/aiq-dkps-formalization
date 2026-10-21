# ForTauCeti - reusable mathematics for Tau Ceti

`ForTauCeti` is the shrinking donor for reusable mathematics not yet accepted
upstream in Tau Ceti or Mathlib. It is not a parallel implementation of
accepted APIs. Paper-facing and census declarations stay downstream where their
source correspondence requires them.

Current repository policy is owned by [`../AGENTS.md`](../AGENTS.md). This README
keeps only the durable package contract. Mutable module counts, roadmap coverage,
readiness findings, and submission status belong to the manifest and checkers,
not to prose snapshots.

## Architecture

```text
Mathlib ─→ TauCeti ─────────────→ DavisKahan and paper libraries
              ↓                         ↑
         ForTauCeti donors ─────────────┘
```

- `ForTauCeti` may depend on Mathlib, Tau Ceti, and itself.
- Paper libraries may consume Tau Ceti directly and may consume `ForTauCeti`
  only for mathematics not yet accepted upstream.
- `ForMathlib` is retired; historical documents may still mention its old paths
  and declaration names.
- Spectra is retired as a maintained dependency. Attribution remains in source
  headers, `retired/Spectra.UPSTREAM.md`, and the historical engineering records.
- Tau Ceti is a pinned Lake dependency, materialised under `.lake/packages`, at
  the same toolchain and Mathlib revision as this repository. An editable
  checkout is an optional explicit input (`--tauceti-root` / `TAUCETI_ROOT`).
  Coordination repositories under `submodules/` are not build dependencies.
  Inspect the pinned upstream source before retaining local foundations; remove
  local duplicates and migrate consumers when an accepted API already exists.

The import firewall is enforced by `dev/policy/import-layers.yaml`.

## Namespace and API ownership

Declarations use their intended final names from the start. The module path
is temporarily rooted at `ForTauCeti/`, but the declaration namespace is not
`ForTauCeti`. Tau Ceti-owned constructions generally live under `TauCeti`;
lemmas extending Mathlib's scalar APIs (such as `Real.sqrt`) use the canonical
Mathlib namespace when required by Tau Ceti's naming rules. For example:

```lean
namespace TauCeti
namespace ContinuousLinearMap

-- declarations

end ContinuousLinearMap
end TauCeti
```

Use `open TauCeti` where dot notation or unqualified lookup requires it. Avoid
unrelated declarations in root Mathlib namespaces.

The maintained architecture has one canonical owner for each reusable concept.
When duplicate local APIs are found, compare their actual types and consumers,
choose the reusable owner here, migrate consumers in dependency order, and remove
the displaced definition or temporary adapter.

## Module style

New or substantially revised modules should use the Tau Ceti / Lean module style:

```lean
module

public import Mathlib...

/-!
# ...

## Provenance
...
-/

public section

namespace TauCeti
...
end TauCeti
```

Keep definition bodies hidden by default. Use per-declaration `@[expose]` only
when a consumer genuinely must unfold that definition, and document why. If a
consumer wants implementation details merely to make `rfl` or `change` work,
prefer a characteristic API lemma such as `foo_def`, `foo_apply`, or
`mem_foo_iff`.

Do not silence warnings or resource limits with local options merely to make a
module pass. The package is intended to be warning-clean under the Tau Ceti build
policy.

## Provenance

Every staged module should explain where its mathematics and Lean implementation
came from. Record the original repository/source, relevant source commit or paper,
original module/declaration names when useful, authorship/copyright and license,
extraction class (copied, adapted, generalized, specialized, or re-proved), and
any material semantic change.

Paper-specific theorem names and source transcriptions do not need to be moved
here merely because they are proved. Keep wrappers downstream when their purpose
is source fidelity rather than reusable API design.

## Manifest and readiness state

`dev/tauceti/extraction-manifest.json` is the source of truth for the current
module/cluster inventory. Generated and checkable artifacts own mutable status:

```bash
aiq-lean imports check dev/policy/import-layers.yaml
aiq-lean ratchet check dev/policy/ratchet.yaml
python3 scripts/check_tauceti_roadmap_topics.py
python3 scripts/check_tauceti_readiness.py
python3 scripts/derive_tauceti_submission_ladder.py --check
```

Do not copy the tools' current counts into this README. If a checker is no longer
load-bearing, follow `AGENTS.md`: prefer removing obsolete tooling to creating a
second status system around it.

## Upstream API use

Use Tau Ceti declarations directly after acceptance. Do not copy accepted code
back into this donor directory or preserve forwarding aliases as the final
design. Keep only genuinely unmerged results here, with exact provenance and
their current consumers.

## What is historical

Long migration plans under `dev/tauceti/` can explain earlier ForMathlib, Spectra,
namespace, or submission decisions, but they are not current execution contracts.
Use the source tree, `AGENTS.md`, this package contract, and the maintained
manifest/checkers when an old record disagrees with the present repository.

## Finite-dimensional unitarily invariant seminorms

`TauCeti.UnitarilyInvariantSeminorm 𝕜 E F` from the pinned Tau Ceti dependency
is the canonical rectangular API. `ForTauCeti` no longer defines a parallel
`Basic` structure; DKPS consumers use Tau Ceti's structure and its accepted
Ky Fan, Frobenius, nuclear, and operator-norm constructors directly.

The remaining files under
`Analysis/InnerProductSpace/UnitarilyInvariantSeminorm/` are donor extensions
and migration adapters still used downstream. They are not a second owner for
the accepted structure or constructors, and adapters are removed as their
paper consumers move to the upstream API. In particular, the paper-facing
finite symmetric-gauge presentation remains in `DavisKahan`, where its
source correspondence belongs.

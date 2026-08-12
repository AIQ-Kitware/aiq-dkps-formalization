# `docs/` - project-facing planning and reference

Scope and reference material for the AIQ DKPS formalization. Current repository
policy lives in [`../AGENTS.md`](../AGENTS.md); engineering memory lives in
[`../dev/`](../dev/README.md).

## Current authorities

The repository deliberately keeps live status out of long prose plans. Use the
smallest authority that answers the question:

| Read | For |
|---|---|
| [`../AGENTS.md`](../AGENTS.md) | Current workflow, dependency and ownership policy |
| [`../ForTauCeti/README.md`](../ForTauCeti/README.md) | Reusable-library architecture and Tau Ceti staging rules |
| [`../DavisKahan/Sources/DavisKahan1970/README.md`](../DavisKahan/Sources/DavisKahan1970/README.md) | Publication-facing Davis--Kahan overview |
| [`../dev/davis-kahan-1970-full-source-census.md`](../dev/davis-kahan-1970-full-source-census.md) | Generated theorem-by-theorem source census |
| [`../dev/davis-kahan-1970-frontier-status.md`](../dev/davis-kahan-1970-frontier-status.md) | Current Davis--Kahan dependency frontier |
| [`planning/davis-kahan-general-sin-theta-roadmap.md`](planning/davis-kahan-general-sin-theta-roadmap.md) | Completed Section 6 single-angle target and its stable source map |

The retired lane workflow is not a source of current status.

## Directory map

```text
docs/
  planning/     # Durable scope/design notes still cited by the implementation
    historical/ # Small set of historical notes retained for stable citations
  challenge/    # Comparator challenge reference
  migrations/   # Library reorganization crosswalks
  ots/          # OpenTimestamps proofs for release manifests
```

## Planning-document policy

A planning document should contain durable scope or design information. Mutable
completion counts belong in generated/checked ledgers instead of prose.

Historical campaign plans, handoffs, and retired Mathlib-readiness queues are
not kept in the working documentation merely as tombstones; Git history preserves
them. A historical file remains only when a source file, provenance manifest, or
other maintained artifact still depends on its stable path. The current reusable
destination is `ForTauCeti` for eventual Tau Ceti integration, subject to
`AGENTS.md`.

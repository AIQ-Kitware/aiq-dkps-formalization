# External development checkouts

This directory is reserved for **local, untracked editable checkouts** of external
Lean projects. Tracked coordination/reference repositories live under
[`../submodules/`](../submodules/) instead.

The important dependency rule is not "no submodules": it is that **the DKPS build
must not depend on a submodule being initialized**. Anything required by `lake build`
is a normal pinned Lake dependency or a tracked source file in this repository.
Optional audits and export tools may consume an explicitly supplied external checkout.

## Tau Ceti -- the build input is a pinned Git dependency

`lakefile.toml` requires Tau Ceti from
`https://github.com/TauCetiProject/TauCeti.git` at a full revision recorded in
`lake-manifest.json`. Lake materializes it under `.lake/packages/TauCeti`.

An editable Tau Ceti checkout is a separate optional input for work that genuinely
needs a Git worktree. It is never a build dependency and never replaces the Lake pin.
Do **not** advance the Lake pin merely to make staged `ForTauCeti` work appear
upstream.

## Optional editable/reference checkouts

These operations accept explicit paths or environment variables:

| work | flag | environment |
| --- | --- | --- |
| `scripts/export_for_tauceti.py --write` | `--tauceti-root` | `TAUCETI_ROOT` |
| `scripts/certify_davis_kahan_1970.py` upstream provenance | `--tauceti-root` | `TAUCETI_ROOT` |
| `scripts/check_tauceti_roadmap_topics.py` | `--roadmap-root` | `TAUCETI_ROADMAP_ROOT` |
| `scripts/check_roadmap_delivered.py` | `--roadmap-root` | `TAUCETI_ROADMAP_ROOT` |

`scripts/_external_checkouts.py` resolves explicit arguments first, then environment
variables, then conventional local/coordination paths, and finally -- for read-only
Tau Ceti use -- `.lake/packages/TauCeti`.

An export refuses the Lake package copy because it is a cache, not an editable
working tree. A checker that requires an absent optional checkout reports
`UNAVAILABLE`; `scripts/run_gates.py` treats that separately from pass and fail.

Current coordination checkouts such as `submodules/TauCetiRoadmap` and
`submodules/TauCetiReview` are allowed because the build does not require them.
See [`../submodules/README.md`](../submodules/README.md) for repository roles.

## Historical `external/TauCeti`

`external/TauCeti` was formerly a Git submodule. It is no longer tracked. A developer
may still keep an untracked editable clone at that path; the resolver accepts it for
compatibility with existing worktrees.

## Spectra -- removed 2026-07-29

`external/Spectra` was the read-only upstream reference for the Spectra collaboration.
The Spectra dependency is retired: maintained modules no longer import it, its source
tree is not vendored, and it has no build role.

The pinned upstream commit
`8dbaaf6728d1342ae16acf79fd7eef7c59b37e63` remains recorded in Lean provenance
headers and in [`../dev/external-lean-references.md`](../dev/external-lean-references.md).
Recovery and attribution material remain under `../retired/` and
`../dev/tauceti/spectra-provenance-map.md`.

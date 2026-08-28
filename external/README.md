# External development checkouts

This directory is reserved for **local, untracked** checkouts of external Lean
projects used during upstream collaboration. External source trees are not copied
or edited as ordinary DKPS files.

**This repository contains no Git submodules, and must not gain any.** Lake fetches
a Git dependency with a plain clone and does not initialise submodules, so a
submodule — or a Lake `path` dependency pointing into one — makes this repository
unusable as a dependency of anything else. The Palomar Registry additionally
rejects a submitted repository that contains submodules. See
[`../dev/palomar-readiness.md`](../dev/palomar-readiness.md).

## Tau Ceti — the build input is a pinned Git dependency

`lakefile.toml` requires Tau Ceti from
`https://github.com/TauCetiProject/TauCeti.git` at a full 40-character revision,
recorded in `lake-manifest.json`. `lake` materialises it under
`.lake/packages/TauCeti`. Nothing needs a checkout in this directory for the build
to work, and `git submodule update --init` is no longer a step in any workflow.

The staging library in `ForTauCeti/` is still measured against the real upstream:
that is what the pin is for. Do **not** advance the pin as a way of "landing"
staged work. `ForTauCeti/` is the deliverable, and
`scripts/export_for_tauceti.py` reproduces a `TauCeti/` copy on demand at
submission time. See [`../ForTauCeti/README.md`](../ForTauCeti/README.md).

## Optional editable checkouts

Three kinds of work want a real checkout the operator controls. Each takes an
explicit path, or an environment variable, and says so when one is missing:

| work | flag | environment |
| --- | --- | --- |
| `scripts/export_for_tauceti.py --write` (needs an **editable** tree) | `--tauceti-root` | `TAUCETI_ROOT` |
| `scripts/certify_davis_kahan_1970.py` upstream provenance | `--tauceti-root` | `TAUCETI_ROOT` |
| `scripts/check_tauceti_roadmap_topics.py` coverage layer | `--roadmap-root` | `TAUCETI_ROADMAP_ROOT` |
| `scripts/check_roadmap_delivered.py` | `--roadmap-root` | `TAUCETI_ROADMAP_ROOT` |

Resolution order is in `scripts/_external_checkouts.py`: explicit argument,
environment variable, then the historical in-repository path if you happen to have
a clone there, then — for read-only Tau Ceti uses only — `.lake/packages/TauCeti`.
An export refuses the Lake copy: it is a cache, not a working tree, and
`lake update` may replace it.

A checker with no checkout reports `UNAVAILABLE` and exits 3. `scripts/run_gates.py`
prints that as `SKIP` and counts it as neither passed nor failed. An unavailable
check is not a passing check.

## Submodules removed 2026-08-28

Three gitlinks were removed. Nothing was lost; the revisions they pinned are:

| path | upstream | revision at removal |
| --- | --- | --- |
| `external/TauCeti` | `https://github.com/TauCetiProject/TauCeti.git` | `1b39d420ac84ed9a5a7d536ce19b37818ad29c39` |
| `submodules/TauCetiRoadmap` | `https://github.com/Erotemic/TauCetiRoadmap.git` | `314943b32da2da9e9697fea63b264c9cbf683dff` |
| `submodules/TauCetiReview` | `https://github.com/TauCetiProject/TauCetiReview.git` | `222eed046013fbee91239aea4a5186b12f086e65` |

The Tau Ceti revision is the live build pin and is authoritative in
`lake-manifest.json`; the other two are review surfaces with no build role, and
their revisions are recorded here only so a reader can reconstruct what the
checkouts were.

Both historical paths are gitignored, so an existing local clone keeps working and
stays out of `git status`. To clear one:

```bash
git submodule deinit -f external/TauCeti          # if your clone predates the removal
rm -rf .git/modules/external/TauCeti external/TauCeti
```

That is local cleanup only — the tracked removal already happened, and no agent
should run it inside a shared worktree while another session is using the
repository.

## Spectra — removed 2026-07-29

`external/Spectra` was the read-only upstream reference for the Spectra
collaboration. **The Spectra dependency is retired**: in-scope `import Spectra`
is 0, both the vendored source tree and this submodule are gone, and the
submodule had no build role — `lakefile.toml` never required it.

Nothing was lost with it. The pinned upstream commit
`8dbaaf6728d1342ae16acf79fd7eef7c59b37e63` is still recorded in nine Lean
provenance headers and in [`../dev/external-lean-references.md`](../dev/external-lean-references.md);
upstream identity, snapshot digests, and complete-fork recovery material are
preserved under `../retired/`; the attribution ledger survives as
[`../dev/tauceti/spectra-provenance-map.md`](../dev/tauceti/spectra-provenance-map.md)
with its baseline `dev/tauceti/spectra-vendor-authorship-baseline.json`.

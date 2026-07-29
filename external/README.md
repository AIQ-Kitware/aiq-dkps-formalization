# External development checkouts

This directory is reserved for Git submodules used during active upstream
collaboration.  External source trees are not copied or edited as ordinary DKPS
files.

## Tau Ceti

`external/TauCeti` is the read-only reference checkout of the Tau Ceti project.
It is a live build input: `lakefile.toml` requires it by path, so the staging
library in `ForTauCeti/` is measured against the real upstream.

Initialize it with:

```bash
git submodule update --init --recursive
```

Do **not** advance its pin as a way of "landing" staged work. `ForTauCeti/` is
the deliverable; `scripts/export_for_tauceti.py` reproduces a `TauCeti/` copy on
demand at submission time. See [`../ForTauCeti/README.md`](../ForTauCeti/README.md).

## Spectra — removed 2026-07-29

`external/Spectra` was the read-only upstream reference for the Spectra
collaboration. **The Spectra dependency is retired**: in-scope `import Spectra`
is 0, the vendored tree moved to `retired/Spectra`, and the submodule had no
build role — `lakefile.toml` never required it. The gitlink and its `.gitmodules`
stanza are gone.

Nothing was lost with it. The pinned upstream commit
`8dbaaf6728d1342ae16acf79fd7eef7c59b37e63` is still recorded in nine Lean
provenance headers and in [`../dev/external-lean-references.md`](../dev/external-lean-references.md);
upstream identity is in [`../retired/Spectra.UPSTREAM.md`](../retired/Spectra.UPSTREAM.md);
and the attribution ledger survives as
[`../dev/tauceti/spectra-provenance-map.md`](../dev/tauceti/spectra-provenance-map.md)
with its baseline `dev/tauceti/spectra-vendor-authorship-baseline.json`.

If you have an older checkout where the submodule is still populated, clear the
local copy with:

```bash
git submodule deinit -f external/Spectra
rm -rf .git/modules/external/Spectra
```

That is local cleanup only — the tracked removal already happened, and no agent
should run it inside a shared worktree while another session is using the
repository.

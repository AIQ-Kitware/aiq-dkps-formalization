# Spectra provenance and integration map

Spectra is **not a current dependency**. This document is the maintained provenance
map for mathematics that originated in, passed through, or was adapted from the
retired Spectra collaboration. It is not a migration plan.

## Upstream identity and retained recovery evidence

- Repository: `https://github.com/adambornemann-glitch/Spectra`
- Upstream revision: `8dbaaf6728d1342ae16acf79fd7eef7c59b37e63`
- License: Apache-2.0
- Upstream/snapshot record: `retired/Spectra.UPSTREAM.md`
- Pristine snapshot digest list: `retired/Spectra.SHA256SUMS`
- Historical compatibility patch: `retired/patches-Spectra/0001-dkps-lean-v4.32-mathlib-compatibility.patch`
- Complete DKPS fork reconstruction patch: `retired/patches-Spectra/0002-dkps-complete-fork.patch`

Neither `vendor/Spectra` nor `external/Spectra` exists in the maintained tree,
and neither participates in the build. The former vendored fork was deleted only
after `0002-dkps-complete-fork.patch` was verified to reconstruct it exactly from
the pinned upstream revision. See `retired/patches-Spectra/README.md` for the
recovery recipe and for the list of DKPS-added files that survive only in that
patch.

Historical measurements such as `spectra-port-surface.json` and
`spectra-vendor-authorship-baseline.json` are provenance snapshots, not current
module-count or dependency reports. Current production code has no `import
Spectra` dependency.

## What provenance still survives in production

The migration deliberately preserved attribution at the declaration/module
boundary instead of keeping a donor source tree alive. Current evidence is
spread across:

- provenance headers in the promoted `ForTauCeti` and Davis--Kahan modules;
- `SpectraBridge` names where an attribution-preserving translation boundary is
  still mathematically useful;
- the upstream revision and recovery patches under `retired/`;
- the historical authorship and port-surface inventories in this directory.

The namespace rule is still live: new DKPS work belongs to its mathematical
owner, never to `namespace Spectra`. `scripts/check_spectra_namespace.py`
enforces that invariant. `namespace SpectraBridge` is allowed because it names a
DKPS-owned bridge rather than pretending a declaration is donor source.

## Attribution classes for retained or future extracted mathematics

When touching a declaration with Spectra ancestry, classify its provenance by
what actually happened:

1. **Direct upstream ancestry.** The mathematical construction came from Spectra
   but the current declaration is independently housed in Tau Ceti/ForTauCeti.
   Cite the exact upstream file and revision when central.
2. **Copied or closely adapted Spectra declaration.** Preserve copyright and
   license headers, name the exact upstream file and revision, and state the
   nature of the adaptation in module documentation.
3. **DKPS bridge over former Spectra infrastructure.** Keep the bridge in the
   canonical owning topic module, credit the specific Spectra declarations it
   translated, and avoid presenting the bridge as an independent upstream
   theorem.
4. **New DKPS theorem assembled using Spectra-era infrastructure.** Cite the
   mathematical source and any central Spectra ancestry while making clear that
   the theorem/proof assembly is new.
5. **Compatibility-only edit.** Treat it as historical build-port evidence, not
   mathematical authorship; the preserved patches under `retired/patches-Spectra`
   are the record.

## Recovery and archaeology

Do not reintroduce Spectra as a dependency merely to inspect old code. To recover
the exact former DKPS fork for archaeology, start from the pinned upstream commit
and apply `retired/patches-Spectra/0002-dkps-complete-fork.patch` following
`retired/patches-Spectra/README.md`.

The retired source contained a small number of DKPS-added modules with no live
counterpart. Their contents remain recoverable from that patch. Whether any such
mathematics deserves a future `ForTauCeti` implementation is a new API decision,
not unfinished Spectra migration work.

# Spectra upstream provenance (retired)

Spectra is no longer vendored or used as a build dependency. This file records
the upstream identity of the former snapshot and the evidence retained after its
removal.

## Upstream snapshot identity

The former `vendor/Spectra/` tree began as an exact `git archive` snapshot of:

- Repository: `https://github.com/adambornemann-glitch/Spectra.git`
- Commit: `8dbaaf6728d1342ae16acf79fd7eef7c59b37e63`
- Commit subject: `added more lean options to the lake file, fixed warnings.`
- License: Apache-2.0

`retired/Spectra.SHA256SUMS` preserves the digest list for that pristine
snapshot. The old `external/Spectra` reference submodule and the vendored source
tree have both been removed from the maintained repository.

## DKPS fork recovery

The former source tree accumulated compatibility edits and DKPS-added modules.
Before deleting it, the complete difference from the pristine upstream snapshot
was captured in:

`retired/patches-Spectra/0002-dkps-complete-fork.patch`

and verified to reconstruct the deleted tree exactly. The authoritative recovery
recipe and explanation of the earlier partial compatibility patch are in
`retired/patches-Spectra/README.md`.

The older
`retired/patches-Spectra/0001-dkps-lean-v4.32-mathlib-compatibility.patch` is
retained for historical provenance only; it does not contain the complete fork.

## Historical snapshot contract

While `vendor/Spectra/` existed, the intended contract was that the pristine
snapshot remain byte-for-byte equivalent to the pinned upstream commit and that
project-specific compatibility changes live in separately recorded patches. The
working tree eventually drifted from that contract; the complete `0002` patch
was created specifically so the drift and DKPS additions would not be lost when
the source tree was retired.

There is no current Spectra update procedure. A future need for old donor code
should use the recovery patch for inspection rather than recreating a live
vendored dependency by default.

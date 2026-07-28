# DavisKahan/Interop/TauCeti — Tau Ceti adapter boundary

This directory is the **narrow** boundary that translates between general Tau
Ceti APIs and Davis–Kahan paper terminology, for the cases where definitional
equality does not already suffice.

It is the Davis–Kahan-side counterpart of the Spectra interop bridges under
`DavisKahan/Interop/Spectra/`: as reusable foundations move from `ForTauCeti`
into the Tau Ceti library, Davis–Kahan consumes them through this layer instead
of importing a source facade to obtain a generic helper.

## What may live here

* compatibility aliases from Davis–Kahan names to canonical Tau Ceti / `ForTauCeti`
  declarations;
* theorem restatements using Davis–Kahan source terminology;
* bridges between historical Davis–Kahan record structures and the canonical
  Tau Ceti structures;
* source-specialized wrappers of general Tau Ceti theorems.

## What must NOT live here

* foundational proofs that belong in Tau Ceti (put them in `ForTauCeti`, then
  export);
* a large second compatibility universe. Adapters here are **transitional** —
  delete each one once its downstream users have migrated to the canonical name.

## Dependency direction

```text
Mathlib -> TauCeti -> ForTauCeti -> DavisKahan/Interop/TauCeti -> (rest of DavisKahan)
```

Adapters here may import `ForTauCeti.*` / `TauCeti.*` and Davis–Kahan modules,
but a lower-level *generic* module must never import an adapter here (that would
reintroduce the backwards dependency this boundary exists to remove). This is
checked by `scripts/check_dependency_layers.py`.

## Current status

`ClosedOperator.lean` is the active U1 boundary. It re-exports the historical
bundle only for source-facing and Spectra-dependent consumers while the generic
mathematics migrates to raw `LinearPMap` signatures. Its deletion condition is
the final migration of those consumers; it must not collect new generic proofs.

During staging, Davis–Kahan approximation-number consumers import the
`ForTauCeti.*` modules directly (they carry the final declaration names), so no
adapter is required there. An adapter file appears here only when a
Davis–Kahan name must be preserved that does not map to a canonical Tau Ceti
name by definitional equality.

# The DKPS Spectra fork, as a patch

**The vendored Spectra source is no longer in this repository** (lane
`SPECTRA-FORK`, 2026-07-30). Everything this project ever did on top of Spectra
lives in `0002-dkps-complete-fork.patch`, and that patch was verified to
reconstruct the deleted tree exactly before the tree was removed.

- upstream repository: `https://github.com/adambornemann-glitch/Spectra`
- upstream commit: `8dbaaf6728d1342ae16acf79fd7eef7c59b37e63`
- DKPS pristine-vendor superproject commit: `cd47c879fe146c2be6f698f4dea8161ac294001a`

## Rebuilding the tree

```sh
git clone https://github.com/adambornemann-glitch/Spectra.git spectra
cd spectra && git checkout 8dbaaf6728d1342ae16acf79fd7eef7c59b37e63
rm -rf .git .gitignore
patch -p1 < <this directory>/0002-dkps-complete-fork.patch
```

The result is byte-for-byte what `retired/Spectra/` contained. **This was
checked, not assumed**: `diff -rq` between a freshly patched pristine checkout
and the tree reported **zero differences** before the tree was deleted.

## Why there are two patches

`0001-dkps-lean-v4.32-mathlib-compatibility.patch` is the **historical** record,
kept for provenance. It is **incomplete**, which is why `0002` exists.

`Spectra.UPSTREAM.md` required the snapshot to stay byte-for-byte equivalent to
upstream, and required project-specific changes to live in a patch rather than
being *"edited into the snapshot as an undocumented fork."* Both rules were
broken over time. Measured against the tree's own `Spectra.SHA256SUMS`:

| | |
|---|---|
| files differing from pristine upstream | 25 |
| …covered by `0001` | 16 |
| **…with no patch record at all** | **9 (457 changed lines)** |
| **files added that upstream never had** | **11** |
| **total covered by `0002`** | **36** |

The undocumented 9 are Mathlib-compatibility in character — renames such as
`diff_mem` → `sdiff_mem`, a `notation` fix — plus a 363-line split of
`POVM.lean` into a new `POVMCore.lean`.

The `0001` change list below is retained because it describes *why* those
compatibility edits exist, which `0002` (a mechanical diff) does not.

## The eleven files that are ours, not upstream's

These did not exist upstream. Three have counterparts in the live libraries;
**eight exist only inside this patch**:

| file | live counterpart |
|---|---|
| `SpectralTheory/SeparatedIntertwiner.lean` | `ForTauCeti/…/SeparatedIntertwiner.lean` |
| `SpectralTheory/Calculus/SpectralGapInverse.lean` | `ForTauCeti/…/LinearPMap/SpectralGapInverse.lean` |
| `Spaces/Tensor/HilbertSchmidt.lean` | `DavisKahan/…/Ideals/HilbertSchmidt.lean` |
| `OneParameterUnitaryGroup/Product.lean` | — |
| `ProjValMeasure/GeneralMap.lean` | — |
| `QuantumMechanics/BornRule/Joint/ProjectivePVM.lean` | — |
| `QuantumMechanics/BornRule/POVMCore.lean` | — |
| `Spaces/Tensor/HilbertSchmidtFlow.lean` | — |
| `Spaces/Tensor/HilbertSchmidtGeneratorBridge.lean` | — |
| `Spaces/Tensor/HilbertSchmidtSpectralGap.lean` | — |
| `YosidaHille/RectangularIntertwining.lean` | — |

**The eight without counterparts are preserved here and nowhere else.** That
three of their siblings were worth promoting is the reason to look before
discarding them: whether any belongs in `ForTauCeti` is an open judgment, and
this patch is what keeps that judgment available.

## What `0001` changed, and why (historical)

Compatibility changes for the DKPS Lean 4.32 / root Mathlib pin:

- explicit complex coercions for exponential measurability;
- derivative equalities isolated from `convert`-generated typeclass goals;
- complex exponential derivatives restricted to `ℝ` while explicitly selecting
  Mathlib's operator-norm `ContinuousLinearMap` structures, avoiding duplicate
  additive, module, and topology instances;
- explicit function extensionality normalization in the Poisson limit;
- explicit subtype equalities for `LinearPMap` domain subtraction, addition,
  and scalar multiplication;
- stable rewrites for signed with-density integrals and pointwise negation;
- current `ContinuousLinearMap` application and projection APIs;
- current measure-theory names for null-set differences;
- explicit complement normalization for spectral-support almost-everywhere facts;
- direct imaginary-part transport for upper-half-plane Cauchy kernels.

`scripts/spectra_compatibility_patch.py` operated on the vendored tree and is
retired with it; the rebuild recipe above replaces it.

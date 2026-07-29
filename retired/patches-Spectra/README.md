# DKPS Spectra compatibility patch

The production Spectra dependency starts from the pristine public upstream
snapshot recorded in `vendor/Spectra.UPSTREAM.md`:

- upstream repository: `https://github.com/adambornemann-glitch/Spectra`
- upstream commit: `8dbaaf6728d1342ae16acf79fd7eef7c59b37e63`
- DKPS pristine-vendor superproject commit: `cd47c879fe146c2be6f698f4dea8161ac294001a`

That superproject commit predates every compatibility edit in this directory.
`external/Spectra` remains a read-only reference checkout and is not modified by
this patch. The root Lake manifest must resolve the dependency from
`vendor/Spectra`.

`0001-dkps-lean-v4.32-mathlib-compatibility.patch` contains only compatibility
changes needed for the DKPS Lean 4.32 / root Mathlib pin. The current revision
repairs the upstream modules exposed by the broad DKPS build and modernizes
additional modules that emitted avoidable Mathlib deprecation warnings:

- explicit complex coercions for exponential measurability;
- derivative equalities isolated from `convert`-generated typeclass goals;
- complex exponential derivatives restricted to `ℝ` while explicitly selecting Mathlib's operator-norm `ContinuousLinearMap` structures, avoiding duplicate additive, module, and topology instances;
- explicit function extensionality normalization in the Poisson limit;
- explicit subtype equalities for `LinearPMap` domain subtraction, addition,
  and scalar multiplication;
- stable rewrites for signed with-density integrals and pointwise negation;
- current `ContinuousLinearMap` application and projection APIs;
- current measure-theory names for null-set differences;
- explicit complement normalization for spectral-support almost-everywhere facts;
- direct imaginary-part transport for upper-half-plane Cauchy kernels.

Use the repository helper rather than editing the vendored sources casually:

```bash
python3 scripts/spectra_compatibility_patch.py verify
python3 scripts/spectra_compatibility_patch.py remove
python3 scripts/spectra_compatibility_patch.py apply
```

`verify` checks the patch digest, the pinned upstream metadata, the reference
submodule when available, the root Lake path, and that the current vendor diff
from the pristine-vendor commit is exactly the recorded patch.

When rebasing onto another upstream snapshot, first remove the patch, replace
and verify the pristine snapshot, commit that snapshot as its own commit, then
reapply/rework the compatibility changes and run:

```bash
python3 scripts/spectra_compatibility_patch.py refresh
python3 scripts/spectra_compatibility_patch.py verify
```

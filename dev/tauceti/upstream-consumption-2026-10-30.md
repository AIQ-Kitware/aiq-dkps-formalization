# DKPS consumption of accepted TauCeti results -- 2026-10-30

The current DKPS snapshot is `e4637c3919ae`, pinned to accepted TauCeti
`b3de655482f7b86c77d8982566e5a73801fd64fa`. The supplied accepted TauCeti
main tree is `463ab293070d4cb355d0a0e036469464070088bc`. Its Mathlib manifest
SHA is `2cabef97b63d3275776b8b060d802de6a6fa1055`, identical to DKPS's
pinned Mathlib SHA, and both use Lean `leanprover/lean4:v4.36.0-rc1`.

## Two independent checkpoints

1. Bump only `lakefile.toml` and `lake-manifest.json` to the accepted TauCeti
   main commit. Then run `lake exe cache get` before a focused `lake build`
   and a default `lake build`; commit the coherent green dependency checkpoint.
   Do not roll a failing pin update into an unrelated donor retirement.
2. Consume the accepted **real spectral grid** (SA-E32--E34, #18927): retire
   the six local grid declarations and make the donor's four remaining
   spectral-projection theorems and its Sylvester spectral-gap consumer use
   accepted `Real.*` declarations directly. Build the two changed modules,
   their importers, and the default targets; commit only after builds succeed.

Use the accepted source under `TauCeti/Order/Interval/Set/RealGrid.lean` and
`TauCeti/MeasureTheory/Constructions/BorelSpace/Real.lean`. The source explicitly
credits adaptation from DKPS. The full pre-retirement source is recoverable via
`git show e4637c3919ae:ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralGrid.lean`.
The historical source names and their replacements are recorded in
`dkps-upstream-contribution-census.md`; the staged record in
`extraction-manifest.json` remains **partially-upstreamed**, not completed.

## Other newly accepted results -- not automatically deletions

The supplied TauCeti tree also includes newly accepted work for SSP-A18
(#20357), SSP-C24 (#19817), SSP-C28/C29 foundations (#19329), the canonical
SSP-D16 slice (#20342), and symmetric-gauge faithfulness OI-B72 (#20867).
Their mathematical scope must be compared with individual maintained donor
statements and consumers before deleting proofs. In particular:

- SSP-C24's symmetric projected-subspace bound overlaps
  `ForTauCeti/Analysis/InnerProductSpace/SinTheta/Perturbation.lean`, but
  this donor includes stronger or differently specialized gap statements and
  downstream paper consumers. Migrate those proof branches separately.
- SSP-C28/C29's directed tangent representative does not subsume the
  isometry-dependent `sinThetaEmbedding` in
  `ForTauCeti/Analysis/InnerProductSpace/Residual/AngleEmbedding.lean` by
  name alone.
- SSP-D16 is only the canonical eigenbasis-indexed theorem; do not retire the
  broader arbitrary-eigenframe development on that basis.
- SSP-A18 and representation-diagonal Riesz measures (#20399) already have
  substantial upstream-consumption work represented in DKPS history. Avoid
  rebuilding deleted duplicates from old campaign notes.

This is **upstream consumption**, not copying accepted TauCeti proofs into
`ForTauCeti`. Keep true donor results, preserve paper-facing names in their
appropriate packages, and do not introduce aliases to keep removed declarations
alive. Earlier dated migration plans are historical evidence, not live todo
lists. The provenance census is the existing record; do not create a parallel
status ledger or new routine audit gate.

## Validation commands (run in the live Lean environment)

After the first ZIP / pin update:

```sh
lake exe cache get
lake build
```

After the second ZIP / source retirement:

```sh
lake exe cache get
lake build ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SpectralGrid \
  ForTauCeti.Analysis.InnerProductSpace.Sylvester.SpectralGap
lake exe cache get
lake build
```

Do not claim Lean compilation based on source inspection alone. The supplied
archives contain no `.lake` dependencies, and this analysis environment has no
`lake` executable; the migration's compile evidence must come from the live
checkout before the donor-retirement commit.

# DkpsQuench2026

Formalization of the 2026 Quench query-efficiency theorem family and its fully
grounded finite and compact-infinite strengthenings.

The directory is organized by mathematical subject.  Names such as `Perfect`,
`Bridge`, and `EndToEnd` are intentionally absent: they describe development
status or workflow position rather than mathematical content.

## Layout

```text
DkpsQuench2026/
├── Core/              foundational definitions, proof engine, shared certificates
├── Paper/             the paper-shaped Theorem 2 interfaces
├── Geometry/          aligned and augmented CMDS, radial and covariance geometry
├── Response/          response means, raw sampling, and regularity
├── Spectral/          Gram-spectrum transfer and random spectral regularity
├── Probability/       iid coverage and uniform response concentration
├── Rates/             polynomial covers and explicit safe schedules
├── QueryEfficiency/   public assumptions and final theorem family
└── prose/             exact retained paper transcription and source TeX
```

## Public theorem family

```lean
DkpsQuench2026.QueryEfficiency.finiteFixedSubset
DkpsQuench2026.QueryEfficiency.infiniteFixedSubset
DkpsQuench2026.QueryEfficiency.finiteAllQueries
DkpsQuench2026.QueryEfficiency.infiniteAllQueries
```

## Theory--practice OLS bridge

The paper deliberately proves a local nearest-neighbor theorem while evaluating
ordinary least squares in its experiments.  The formal boundary and the extra
assumptions needed for OLS are exposed under the stable namespace
`DkpsQuench2026.Paper.OLS`:

```lean
DkpsQuench2026.Paper.OLS.OLSFit
DkpsQuench2026.Paper.OLS.HighProbAffineRiskCompetitive
DkpsQuench2026.Paper.OLS.highProb_queryEfficient_crossBudget_of_affineRiskGap
DkpsQuench2026.Paper.OLS.highProb_queryEfficient_crossBudget_of_affineRealizable
DkpsQuench2026.Paper.OLS.lipschitz_not_sufficient_for_affineRealizability
```

The cross-budget theorem permits the OLS DKPS and sample-score baseline to use
different query subsets.  It therefore matches the shape of the practical
four-query-versus-eight-query evaluation while explicitly requiring an affine
risk gap and OLS risk consistency that are absent from the nearest-neighbor
Theorem 2 assumptions.

The corresponding public interfaces are:

```lean
DkpsQuench2026.QueryEfficiency.FiniteSubsetData
DkpsQuench2026.QueryEfficiency.FiniteSubsetAssumptions
DkpsQuench2026.QueryEfficiency.InfiniteSubsetData
DkpsQuench2026.QueryEfficiency.InfiniteSubsetAssumptions
```

## Build and audit

```bash
lake build DkpsQuench2026
lake build

grep -RIn '\bsorry\b' DkpsQuench2026 --include='*.lean'
grep -RIn '^axiom ' DkpsQuench2026 --include='*.lean'
```

The exact paper transcription is retained under `DkpsQuench2026/prose/`.
`papers/DKPS-formalized-vs-literature.tex` records the modernized comparison
between the printed theorem and the stronger formal theorem family.

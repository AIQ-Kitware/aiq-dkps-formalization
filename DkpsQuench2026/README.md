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

The rest of the Lean-side theory--practice chain is split into small modules:

```text
Paper/OLSInvariance.lean         rigid-coordinate invariance of affine OLS
Paper/OLSPerturbation.lean       empirical optimality, generalization, and DKPS transfer
Paper/TheoryPractice.lean        distinct MSE, MAE, and replicate-win claim shapes
Paper/EvaluationBridges.lean     deterministic population-to-card margin logic
Paper/EvaluationConcentration.lean explicit finite Chebyshev confidence bounds
Geometry/OLSAligned.lean         composition with aligned-CMDS concentration
```

Important public anchors include:

```lean
DkpsQuench2026.Paper.OLS.affinePredict_rigid
DkpsQuench2026.Paper.OLS.HighProbAffineGeneralizationOn
DkpsQuench2026.Paper.OLS.highProbAffineRiskCompetitive_of_olsRiskBridge
DkpsQuench2026.Paper.TheoryPractice.measure_not_empiricalCrossBudgetMAEClaim_le
DkpsQuench2026.Paper.TheoryPractice.measure_not_empiricalWinRateClaim_le
DkpsQuench2026.highProb_olsRiskBridge_of_finite_configError_on
```

The finite evaluation theorems return explicit failure-probability bounds; they
do not collapse a fixed 32-replicate experiment into an asymptotic theorem.
The only substantial statistical premise still exposed at the OLS training
layer is uniform convergence of the affine squared-risk class on a declared
admissible coefficient set, together with membership of the fitted coefficient
and witness in that set.  This coefficient control is named explicitly rather
than hidden inside the query-efficiency conclusion.

The corresponding public interfaces are:

```lean
DkpsQuench2026.QueryEfficiency.FiniteSubsetData
DkpsQuench2026.QueryEfficiency.FiniteSubsetAssumptions
DkpsQuench2026.QueryEfficiency.InfiniteSubsetData
DkpsQuench2026.QueryEfficiency.InfiniteSubsetAssumptions
```

## Acharyya concentration bridge

`Geometry/AlignedCMDS.lean` retains the established `ConfigError` bridge and
also exposes a Frobenius route through
`quench_uniform_embedding_error_of_aligned_spectral_frob`.  The latter consumes
Acharyya's `configFrobBound` directly and uses the elementary row bound
`‖error_i‖ ≤ ConfigFrobError`, so Quench's uniform embedding-error premise no
longer needs the extra `√n` introduced by the older row-sum `ConfigError` API.

This does not alter Quench's nearest-neighbor theorem.  It strengthens the
upstream concentration certificate that can be supplied to that theorem and
keeps the Quench-facing v1 Acharyya rate path separate from the revised
June-2026 Acharyya source version.

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

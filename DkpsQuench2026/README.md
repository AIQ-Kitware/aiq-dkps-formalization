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

Theorem 2 has two printed conclusions.  Both are proved end to end for the
literal tie-averaged nearest-neighbor estimator built from raw cached responses,
with the representation concentration derived through the CMDS/Davis--Kahan
chain rather than taken as a hypothesis.

```lean
-- "for any e > 0 there exists (n,m,r) such that MSE(y_NN) <= e with high probability"
DkpsQuench2026.QueryEfficiency.finiteFixedSubsetMSE
DkpsQuench2026.QueryEfficiency.infiniteFixedSubsetMSE

-- "y_NN is query-efficient relative to y_Q with high probability", for a fixed
-- query subset and then at the paper's full quantifier level over every m < M
DkpsQuench2026.QueryEfficiency.finiteFixedSubset
DkpsQuench2026.QueryEfficiency.infiniteFixedSubset
DkpsQuench2026.QueryEfficiency.finiteAllQueries
DkpsQuench2026.QueryEfficiency.infiniteAllQueries
```

The conditional interfaces in `Paper/` and `Geometry/` state the same
conclusions with the concentration event as an explicit premise.  They are the
reusable seams the capstones factor through, not the paper-facing results; the
`ASSUMPTION DISCLOSURE` note in `Paper/Theorem2.lean` says which is which.

Two hypotheses still exceed the source and are tracked as census gaps: the
replicate schedule `safeEntropyReplicates d n = (n + 1) ^ (4 + d)` against the
paper's `r = omega(n ^ 3)`, and the population nondegeneracy floor.

The schedule was `(n + 1) ^ (6 + 2 * d)` until the spectral certificate began
reporting the population Gram floor at its true scale.  The Gram matrix of `n`
centered points is `n` times an empirical covariance, so its leading eigenvalues
grow linearly, exactly as the compactness ceiling `4(n+1)B^2` does; reporting a
constant floor against a growing ceiling inflated the conditioning ratio in the
Davis--Kahan configuration bound by a factor `n`.  With the floor at scale, every
term of that bound vanishes for a merely bounded batch-scaled perturbation, so
the response tolerance loosened from `(n+1)^-2` to `(n+1)^-1`, the perspective
net shrank from `O((n+1)^(2d))` to `O((n+1)^d)`, and the replicate budget fell by
`d + 2` powers.  At `d = 2` and `n = 100` that is 1.1e12 cached responses per
model rather than 1.1e20.

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
The finite/high-probability bridge also no longer assumes that the scaled
perturbation rate tends to zero: that hypothesis is reserved for downstream
consistency/query-efficiency results that actually need a vanishing error
envelope.  The Term-2 contribution in `configFrobBound` now uses the sharper
`√α` denominator instead of `√(α/2)`.

The Frobenius route now reaches both fixed-population and growing target-augmented
query-efficiency capstones.  `GrowingConfigControl` tracks `configFrobBound`,
and the pairwise-distance engine bounds each target/reference radial error
straight from `ConfigFrobError`; the growing path therefore no longer
reintroduces the legacy `sqrt(n+1)` factor.  `Rates/SafeSchedule.lean` uses that
improvement together with the direct pairwise response→CMDS bridge to retune
the explicit raw-response schedule from the original `(n+1)^-5` / `(n+1)^13`
to tolerance `(n+1)^-2` / finite replicate budget `(n+1)^6`.  The
compact-infinite cover exponent correspondingly drops from `5d` to `2d`, so its
declared replicate budget is `(n+1)^(6+2d)`.  The underlying Acharyya response
bookkeeping now exposes the exact structural ratio `n³γ/(r x²)` at tolerance
`η=x/n`.  `Acharyya2025.PaperRate` now closes the literal source specialization:
`r = ω(n³)` is represented by a little-o hypothesis, `x=(n³/r)^(1/2-δ)` tends
to zero for `δ ∈ (0,1/2)`, the concentration ratio becomes a bounded factor
times `(n³/r)^(2δ)`, and a growing DK `GrowingConfigControl` is produced at
that same scale.  The next integration step is to let the growing Quench
capstone consume that paper-scale certificate directly instead of choosing the
explicit safe schedule.  For the fixed-population route,
`quench_part2_from_aligned_configFrobError_hp`,
`queryEfficient_nn_of_response_mean_frob`, and
`queryEfficient_nn_of_second_moment_frob` use the DK-sharpened Acharyya bound
all the way to Quench's uniform embedding-error premise.  The core Frobenius
bridge accepts any deterministic envelope that eventually dominates
`configFrobBound`; `quench_part2_from_aligned_configFrobQuadratic_hp` specializes
this to the explicit `C₁ ε + C₂ ε²` spectral majorant.  This gives Quench a
polynomial spectral concentration input.  `Acharyya2025.PaperRate` now carries
that bridge through the paper's real-power scale and proves the corresponding
response and growing spectral rates vanish under `r = ω(n³)` and bounded
second moments.  The older `ConfigError` declarations remain as compatibility
APIs.

This keeps the Quench-facing v1 Acharyya rate path separate from the revised
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

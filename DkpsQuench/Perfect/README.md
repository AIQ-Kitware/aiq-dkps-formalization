# Perfect Quench

This directory contains the complete end-to-end Quench theorem family. It starts
from raw cached response replicates and derives the response concentration,
population geometry, spectral regularity, explicit asymptotic schedules, and
nearest-neighbor risk comparison needed by the paper-facing capstones.

The four public endpoints are:

- `perfectQuench_finite_fixedSubset`;
- `perfectQuench_infinite_fixedSubset`;
- `perfectQuench_finite_allQueries`;
- `perfectQuench_infinite_allQueries`.

There are no incomplete proof bodies under `DkpsQuench/Perfect` in the current
source tree.

## The two routes

The finite-model route assumes a finite model class and uses a direct union
bound over target models. Finiteness also supplies compactness of the
perspective image and a uniform population-response norm bound.

The compact-infinite route assumes a compact perspective image and one
pathwise Lipschitz condition on the raw response embedding. From these it
derives:

- sample-mean and population-mean Lipschitz regularity;
- a population-response norm envelope;
- polynomial finite covers of the perspective range;
- measurable finite-net response events;
- entropy-aware uniform concentration.

Both routes use the same population-geometry, covariance, spectral, CMDS, and
query-efficiency layers.

## Dependency graph

```text
Definitions
├── PopulationGeometry
├── CovarianceFloor
├── CenteredCovariance
├── GramSpectrumBridge
├── SpectralRegularity
│   └── RawResponses
│       └── Compactness
│           └── PolynomialCover
│               └── UniformConcentration
│                   └── RateSchedule
│                       └── SpectralCapstone
│                           └── Capstone
└───────────────────────────────────────────────┘
```

## What is derived internally

The public capstones do not require callers to provide:

- centered configurations or Gram matrices;
- positive-semidefinite or rank proofs;
- samplewise spectral floors and ceilings;
- response-mean concentration events;
- population response norm envelopes;
- finite nets, cover sizes, or entropy exponents;
- entrywise CMDS error schedules;
- polar-decomposition smallness bookkeeping;
- a `GrowingConfigControl` certificate.

These objects are constructed from the smaller paper-facing assumptions.

## Current public assumptions

The finite fixed-subset theorem uses:

- a measurable perspective map;
- positive mass in every target-centered perspective ball;
- an iid reference sampler;
- measurable pairwise-independent raw response replicates with uniform second
  moment control;
- exact realization of perspective distances by population response means;
- a positive population covariance floor;
- a score-Lipschitz inequality;
- positive baseline MSE;
- a positive number of queried response rows.

The compact-infinite theorem additionally uses compactness of the perspective
range and pathwise raw-response Lipschitzness.

A separate positivity proof for the stored score-Lipschitz constant is no
longer required. The proof replaces any valid constant `γ` by `max γ 1` before
using the quantitative nearest-neighbor bound.

## Remaining hypothesis-reduction opportunities

The theorem family is complete, but two fields appear derivable using machinery
already in the repository:

1. `RawIIDResponseModel.mean_measurable` should follow from joint measurability
   of the raw response family, the coordinate mean identities, and parameter
   integration.
2. `PerspectiveNondegeneracy.center_is_mean` should follow from the quadratic
   floor. The covariance development already obtains integrability of centered
   squared linear forms; probability-space `L² → L¹` and the definition of
   `perspectiveMean` should finish the centered-mean identity.

The response-distance realization hypothesis is a larger architectural seam.
It can disappear only if the public perspective is constructed canonically from
population response distances; pairwise realization alone does not make an
arbitrary supplied perspective measurable or canonical.

## Source comparison

The exact Quench transcription remains under
`DkpsQuench/prose/quench-icml-nonanon_transcription.md`. The modernized theorem
reconstruction, source discrepancies, and live hypothesis audit are maintained
in `papers/DKPS-formalized-vs-literature.tex`; a second distilled copy of the
short paper proof is intentionally not maintained.

## Validation

```bash
lake build DkpsQuench.Perfect
lake build Acharyya2024 Acharyya2025 DkpsQuench Helm2025

grep -RIn '\bsorry\b' DkpsQuench/Perfect --include='*.lean'
grep -RIn '^axiom ' DkpsQuench/Perfect --include='*.lean'
```

For a kernel-level release audit, also inspect the four final declarations with
`#print axioms` in a temporary audit module.

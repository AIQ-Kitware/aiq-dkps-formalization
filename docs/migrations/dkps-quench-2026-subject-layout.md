# DkpsQuench2026 subject-oriented migration

This migration replaces the historical `DkpsQuench` library and the development
status name `Perfect` with one canonical `DkpsQuench2026` library organized by
mathematical subject.

## Removal after applying the ZIP overlay

```bash
rm -rf DkpsQuench DkpsQuench.lean
```

## Module crosswalk

| Old | New |
|---|---|
| `DkpsQuench.Basic` | `DkpsQuench2026.Core.Definitions` |
| `DkpsQuench.Internal` | `DkpsQuench2026.Core.ProofEngine` |
| `DkpsQuench.Coverage` | `DkpsQuench2026.Probability.Coverage` |
| `DkpsQuench.Theorem2` | `DkpsQuench2026.Paper.Theorem2` |
| `DkpsQuench.QueryEfficiency` | `DkpsQuench2026.Paper.QueryEfficiency` |
| `DkpsQuench.AcharyyaBridge` | `DkpsQuench2026.Geometry.AlignedCMDS` |
| `DkpsQuench.Radial` | `DkpsQuench2026.Geometry.Radial` |
| `DkpsQuench.GrowingAcharyyaBridge` | `DkpsQuench2026.Geometry.AugmentedCMDS` |
| `DkpsQuench.GrowingResponseBridge` | `DkpsQuench2026.Response.Means` |
| `DkpsQuench.Perfect.Definitions` | `DkpsQuench2026.Core.Certificates` |
| `DkpsQuench.Perfect.PopulationGeometry` | `DkpsQuench2026.Geometry.Population` |
| `DkpsQuench.Perfect.CovarianceFloor` | `DkpsQuench2026.Geometry.Covariance` |
| `DkpsQuench.Perfect.CenteredCovariance` | `DkpsQuench2026.Geometry.CenteredCovariance` |
| `DkpsQuench.Perfect.GramSpectrumBridge` | `DkpsQuench2026.Spectral.GramSpectrum` |
| `DkpsQuench.Perfect.SpectralRegularity` | `DkpsQuench2026.Spectral.Regularity` |
| `DkpsQuench.Perfect.RawResponses` | `DkpsQuench2026.Response.RawSampling` |
| `DkpsQuench.Perfect.Compactness` | `DkpsQuench2026.Response.Regularity` |
| `DkpsQuench.Perfect.UniformConcentration` | `DkpsQuench2026.Probability.UniformConcentration` |
| `DkpsQuench.Perfect.PolynomialCover` | `DkpsQuench2026.Rates.PolynomialCover` |
| `DkpsQuench.Perfect.RateSchedule` | `DkpsQuench2026.Rates.SafeSchedule` |
| `DkpsQuench.Perfect.SpectralCapstone` | `DkpsQuench2026.QueryEfficiency.Spectral` |
| `DkpsQuench.Perfect.Capstone` | `DkpsQuench2026.QueryEfficiency.{Assumptions,Finite,Infinite,AllQueries}` |

## Public declaration crosswalk

| Old | New |
|---|---|
| `DkpsQuench.Perfect.FinitePerfectSubsetData` | `DkpsQuench2026.QueryEfficiency.FiniteSubsetData` |
| `DkpsQuench.Perfect.FinitePerfectSubsetAssumptions` | `DkpsQuench2026.QueryEfficiency.FiniteSubsetAssumptions` |
| `DkpsQuench.Perfect.InfinitePerfectSubsetData` | `DkpsQuench2026.QueryEfficiency.InfiniteSubsetData` |
| `DkpsQuench.Perfect.InfinitePerfectSubsetAssumptions` | `DkpsQuench2026.QueryEfficiency.InfiniteSubsetAssumptions` |
| `DkpsQuench.Perfect.perfectQuench_finite_fixedSubset` | `DkpsQuench2026.QueryEfficiency.finiteFixedSubset` |
| `DkpsQuench.Perfect.perfectQuench_infinite_fixedSubset` | `DkpsQuench2026.QueryEfficiency.infiniteFixedSubset` |
| `DkpsQuench.Perfect.perfectQuench_finite_allQueries` | `DkpsQuench2026.QueryEfficiency.finiteAllQueries` |
| `DkpsQuench.Perfect.perfectQuench_infinite_allQueries` | `DkpsQuench2026.QueryEfficiency.infiniteAllQueries` |

There are no compatibility shims.  Update downstream imports and declaration
references to the canonical names.

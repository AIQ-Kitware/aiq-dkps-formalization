# Davis--Kahan hidden-foundation map

Recursive hidden-foundation map discovered while working ahead on the complete Davis--Kahan 1970 formalization.  Each node names its own production module; the campaign-era aggregate `DavisKahan.Experimental.MathAhead.HiddenFoundations.All` was deleted with `Experimental/MathAhead/` on 2026-08-27 and there is no aggregate module now.

## Summary

- Tracked nodes: **19**
- Textually present declarations: **19/19**
- Campaigns: **4**
- Findings: **0 errors**, **0 warnings**

## Node kinds

- `proof_candidate`: A full mathematical proof attempt is present; elaboration repair may remain.
- `construction`: A concrete definition or record assembly is present.
- `bridge`: Connects existing compiled or proof-carrying layers.
- `interface`: An honest explicit contract for a genuinely missing foundational campaign; fields are not counted as completed mathematics.

## Campaigns

### Two-projection pair classification foundations

`section3-nonacute` · construction=1, proof_candidate=3

### Circle geometry feeding the existing contour continuation engine

`section8-circle` · no nodes

### Hilbert--Schmidt and Schatten ideal families

`sylvester-real-ideals` · construction=2, proof_candidate=2

### Free-beam ODE, Sobolev realization, and spectral gap

`section9-free-beam` · interface=2, proof_candidate=9

## Nodes

| Node | Kind | Confidence | Source | Lean | Declaration |
| --- | --- | --- | :---: | :---: | --- |
| `orthogonal-sum-equivalence` | proof_candidate | medium | yes | - | `TauCeti.DavisKahan.orthogonalSumEquiv` |
| `two-projection-equivalence-data` | construction | high | yes | - | `TauCeti.DavisKahan.TwoProjectionOperatorEquivalence` |
| `two-projection-ambient-unitary` | proof_candidate | medium | yes | - | `TauCeti.DavisKahan.TwoProjectionOperatorEquivalence.ambient` |
| `two-projection-classification` | proof_candidate | medium | yes | - | `TauCeti.DavisKahan.twoProjection_operator_classification` |
| `hs-completeness` | proof_candidate | low | yes | - | `TauCeti.DavisKahan.ExactSinTheta.paperHilbertSchmidt_complete` |
| `hs-complex-family` | construction | low | yes | - | `TauCeti.DavisKahan.ExactSinTheta.hilbertSchmidtComplex` |
| `schatten-foundation` | construction | high | yes | - | `TauCeti.schattenIdealFamily` |
| `schatten-family` | proof_candidate | high | yes | - | `ContinuousLinearMap.schattenENorm_add_le` |
| `free-beam-mode-ode` | proof_candidate | medium | yes | - | `TauCeti.DavisKahan.FreeBeam.mode_fourth_derivative` |
| `free-beam-boundary-determinant` | proof_candidate | medium | yes | - | `TauCeti.DavisKahan.FreeBeam.boundaryDet_eq` |
| `free-beam-characteristic` | proof_candidate | medium | yes | - | `TauCeti.DavisKahan.FreeBeam.characteristic_eq_zero_of_freeBoundary` |
| `free-beam-numeric-bound` | proof_candidate | high | yes | - | `TauCeti.DavisKahan.FreeBeam.four_seventy_three_pow_four_gt_five_hundred` |
| `free-beam-root-localization` | interface | high | yes | - | `TauCeti.DavisKahan.FreeBeam.PositiveRootLocalization` |
| `free-beam-root-bound` | proof_candidate | high | yes | - | `TauCeti.DavisKahan.FreeBeam.positive_root_fourth_power_gt_five_hundred` |
| `free-beam-sobolev-foundation` | interface | high | yes | - | `TauCeti.DavisKahan.FreeBeam.SobolevTraceFoundation` |
| `free-beam-closed-operator` | proof_candidate | medium | yes | - | `TauCeti.DavisKahan.FreeBeam.SobolevTraceFoundation.operator` |
| `free-beam-selfadjoint` | proof_candidate | high | yes | - | `TauCeti.DavisKahan.FreeBeam.SobolevTraceFoundation.operator_isSelfAdjoint` |
| `free-beam-third-eigenvalue` | proof_candidate | high | yes | - | `TauCeti.DavisKahan.FreeBeam.SobolevTraceFoundation.firstPositiveSpectralValue_gt_five_hundred` |
| `free-beam-spectrum-gap` | proof_candidate | high | yes | - | `TauCeti.DavisKahan.FreeBeam.SobolevTraceFoundation.spectrum_subset_zero_union_Ioi_five_hundred` |

## Dependency graph

- `orthogonal-sum-equivalence` <- (root)
- `two-projection-equivalence-data` <- (root)
- `two-projection-ambient-unitary` <- `two-projection-equivalence-data`, `orthogonal-sum-equivalence`
- `two-projection-classification` <- `two-projection-ambient-unitary`
- `hs-completeness` <- (root)
- `hs-complex-family` <- `hs-completeness`
- `schatten-foundation` <- (root)
- `schatten-family` <- `schatten-foundation`
- `free-beam-mode-ode` <- (root)
- `free-beam-boundary-determinant` <- `free-beam-mode-ode`
- `free-beam-characteristic` <- `free-beam-boundary-determinant`
- `free-beam-numeric-bound` <- (root)
- `free-beam-root-localization` <- (root)
- `free-beam-root-bound` <- `free-beam-root-localization`, `free-beam-numeric-bound`
- `free-beam-sobolev-foundation` <- (root)
- `free-beam-closed-operator` <- `free-beam-sobolev-foundation`
- `free-beam-selfadjoint` <- `free-beam-closed-operator`
- `free-beam-third-eigenvalue` <- `free-beam-sobolev-foundation`, `free-beam-root-bound`
- `free-beam-spectrum-gap` <- `free-beam-third-eigenvalue`

# Declaration grounding ledger

## Pinned inputs

- Repository snapshot: merge commit `4285a6e`.
- Lean toolchain: `leanprover/lean4:v4.32.0`.
- Mathlib: `3dffaf2f18b47d11948f6390838ea6f2ae662aaf`.

The table records the substantial nonlocal declarations used by this package.
Routine core lemmas and tactics are omitted; no mathematical helper is omitted.

## Repository declarations

| Declaration family | Exact source file |
|---|---|
| `PaperUnitaryInvariantNorm`, `prefixGauge_le_of_all_kyFan_le`, `mem_of_all_mul_kyFan_le`, `mul_gauge_le_of_all_mul_kyFan_le` | `DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean` |
| `PaperSymmetricNormingFunction`, `toPaperNorm` | `DavisKahan/Sources/DavisKahan1970/Ideals/NormCorrespondence.lean` |
| `paperNuclearNorm` | `DavisKahan/Sources/DavisKahan1970/Ideals/UnitaryInvariantNormInstances.lean` |
| `FiniteVector.lpGauge`, `lpSymmetricGauge`, `linftyGauge`, `linftySymmetricGauge`, zero-padding laws | `ForTauCeti/Analysis/Normed/FiniteLpGauge.lean` |
| `ContinuousLinearMap.approximationNumber`, monotonicity, norm bound, near minimizers, additive inequality | `ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Basic.lean` |
| `ContinuousLinearMap.le_approximationNumber_of_linearIndependent` | `ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/MinMax.lean` |
| `ContinuousLinearMap.rank_comp_le_natCast_right` | `ForTauCeti/LinearAlgebra/Dimension/RankComp.lean` |
| `approximationSingularValue`, `kyFanApproximationGauge`, scaling and positivity | `DavisKahan/OperatorIdeal/ApproximationNumbers/Core.lean` |
| finite-source singular system | `DavisKahan/OperatorIdeal/ApproximationNumbers/FiniteSourceSingularSystem.lean` |
| `ContinuousLinearMap.exists_linearIndependent_lowerBound_of_lt_approximationNumber` | `ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/MinMaxUpper.lean` |
| `pvmRangeSubspace`, projection-fixes-range theorem | `DavisKahan/Interop/Spectra/PVMSubspace.lean` |
| exact Section 7 singular-family coefficient theorem | `DavisKahan/Experimental/Scratch/Section7/InfiniteTanTwoThetaCore.lean` |
| orthonormal-family Ky Fan variational bound | `DavisKahan/DoubleAngle/KyFanOrthonormal.lean` |
| `BlockOperatorData`, `SolvesRiccati` | `DavisKahan/Experimental/InfiniteDimensional/Riccati/BoundedBasic.lean` |
| `solvesRiccati_iff_pointwise` | `DavisKahan/Experimental/InfiniteDimensional/Riccati/BoundedCore.lean` |
| `UnboundedBlockData`, `StrongSolvesRiccati` | `DavisKahan/Riccati/UnboundedBasic.lean` |
| `strongSolvesRiccati_iff_pointwise` | `DavisKahan/Riccati/UnboundedReduction.lean` |
| `ContractiveReducingGraphSelection`, `strongSolvesRiccati` | `DavisKahan/Riccati/UnboundedExistence.lean` |
| closed-operator symmetry bridge | `DavisKahan/SpectralTheory/ClosedOperator/Basic.lean` |
| closed semibound `toLinearMap` bridges | `DavisKahan/Sylvester/ClosedSylvesterEquation.lean` |
| Spectra projection algebra and energy bounds | `vendor/Spectra/Spectra/SpectralTheory/Algebra.lean` |
| bounded self-adjoint operator/PVM construction | `vendor/Spectra/Spectra/Operator/SelfAdjointOperator.lean` and `vendor/Spectra/Spectra/OneParameterUnitaryGroup/PVM.lean` |

## Pinned Mathlib declarations

| Declaration | Exact pinned source file |
|---|---|
| `isUnit_one_sub_of_norm_lt_one` | `Mathlib/Analysis/SpecificLimits/Normed.lean` |
| `NormedRing.inverse_one_sub` | `Mathlib/Analysis/Normed/Ring/Units.lean` |
| `tsum_geometric_le_of_norm_lt_one` | `Mathlib/Analysis/SpecificLimits/Normed.lean` |
| `ContinuousLinearMap.isUnit_iff_bijective` | `Mathlib/Analysis/Normed/Operator/Banach.lean` |
| `Cardinal.cast_toNat_of_lt_aleph0` | `Mathlib/SetTheory/Cardinal/ToNat.lean` |
| `ENNReal.tsum_eq_iSup_sum` (audited but no longer needed by the final code) | `Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean` |

## Local new mathematics

The following are deliberately local declarations, not external references:

- `exists_finiteRank_gaugeApproximation_of_kyFan_dominated`;
- `exists_gramSpectralBandModel`;
- `exists_rank_le_norm_doubleAngleTangent_sub_lt`;
- `doubleAngleTangent_approximationNumber_le`;
- `approximationNumber_doubleAngleTangentOperator`;
- `stableSingularPair_doubleAngleTangent_le`;
- `sharp_transformed_prefix`;
- `exists_unboundedApproximateLeadingSingularFamily`;
- `unboundedStableSingularPair_doubleAngleTangent_le`;
- `sharp_unbounded_doubleAngleTangentOperator_kyFan`.

A compiler failure inside one of these proofs is a failure of the new proof
attempt, not evidence that an invoked helper was invented.

# Full Part III math-ahead restoration manifest

This human-readable manifest accompanies the machine-readable JSON file of the same stem.

- Base commit: `7463ca25c64a46c48411a2769b47714889974a97`
- Historical proof-body source: `2244e7c6bd7f`
- Exact-signature candidate bodies restored: **174**
- Two false tan 2Theta statements were source-corrected on 2026-07-20:
  `tanTwoTheta_residual_le` and `tanTwoTheta_perturbation_le` now require
  `OrderedInternalGap`. See
  `dev/tan-two-theta-ordered-gap-correction-2026-07-20.md`.

## `DavisKahan/Experimental/FiniteDimensional/Core/AngleOperators.lean` — 5
- `tanThetaMap`
- `angleOperator`
- `tanAngleOperator`
- `tanTwoAngleOperator`
- `principalAngles_orthogonal`

## `DavisKahan/Experimental/FiniteDimensional/DirectRotation.lean` — 12
- `angleComplexStructure`
- `directRotation_symm`
- `directRotation_apply_eq_self_of_mem_common`
- `directRotation_eq_polarFactor`
- `directRotation_eq_cos_add_J_sin`
- `directRotation_sq`
- `directRotation_comm_angleOperator`
- `directRotation_unique`
- `directRotation_minimizes_displacementSquare_uiNorm`
- `directRotation_minimizes_uiNorm_of_largestAngle_le_pi_div_three`
- `directRotation_minimizes_max_displacement`
- `directRotation_minimizes_sum_sq_basis_angles`

## `DavisKahan/Experimental/FiniteDimensional/DoubleAngle/SinTheta.lean` — 1
- `sinTwoTheta_residual_le`

## `DavisKahan/Experimental/FiniteDimensional/DoubleAngle/TanTheta.lean` — 7
- `tanTwoTheta_residual_le`
- `tanTwoTheta_perturbation_le`
- `isAcute_canonical_tanTwoTheta`
- `existsUnique_reducingSubspace_preserving_gap`
- `spectral_repulsion_compression`
- `spectral_repulsion_uiNorm`
- `largestPrincipalAngle_lt_pi_div_four`

## `DavisKahan/Experimental/FiniteDimensional/Generalized.lean` — 4
- `generalizedSinTheta_frobenius_le_of_spectralDistance`
- `generalizedSinTheta_nuclear_le_of_spectralDistance`
- `spectralSubspace_path_continuous`
- `sinTwoTheta_acute_of_small_perturbation`

## `DavisKahan/Experimental/FiniteDimensional/Norms/Rectangular.lean` — 1
- `schatten`

## `DavisKahan/Experimental/FiniteDimensional/Residual/AngleEmbeddings.lean` — 2
- `tanThetaEmbedding`
- `tanTwoThetaEmbedding`

## `DavisKahan/Experimental/FiniteDimensional/Sharpness.lean` — 9
- `modelTanThetaPerturbation`
- `principalAngles_model`
- `sinTheta_model_equality`
- `tanTheta_model_equality`
- `sinTwoTheta_model_equality`
- `tanTwoTheta_model_equality`
- `sinTheta_constant_optimal`
- `sinTwoTheta_constant_optimal`
- `directSum_models_simultaneous_equality`

## `DavisKahan/Experimental/FiniteDimensional/TanTheta/GraphOperator.lean` — 6
- `singularValues_graphOperator`
- `tanTheta_residual_le`
- `isTransverse_of_tanTheta_residual_gap`
- `tanTheta_perturbation_le`
- `tanThetaMap_perturbation_le`
- `tanTheta_vector_le`

## `DavisKahan/Experimental/InfiniteDimensional/Core/AbstractSpectrum.lean` — 1
- `sinTwoThetaEmbedding`

## `DavisKahan/Experimental/InfiniteDimensional/Core/Forms.lean` — 5
- `formSum`
- `ClosedForm.associatedOperator`
- `formPerturbationSize`
- `klmn`
- `sinTheta_formPerturbation`

## `DavisKahan/Experimental/InfiniteDimensional/Core/OperatorAngle.lean` — 14
- `operatorAbsoluteValue`
- `angleOperator`
- `sinAngleOperator`
- `cosAngleOperator`
- `tanAngleOperator`
- `sinTwoAngleOperator`
- `tanTwoAngleOperator`
- `sinAngleOperator_eq_abs_projection_sub`
- `norm_sinAngleOperator`
- `directedGap_eq_subspaceGap_of_acute`
- `acute_iff_exists_bounded_angularOperator`
- `norm_angularOperator_eq_tan_maximalAngle`
- `angleOperator_orthogonalComplement`
- `maximalAngle_triangle`

## `DavisKahan/Experimental/InfiniteDimensional/Core/SpectralProjection.lean` — 15
- `spectralProjection`
- `spectralSubspace_hasOrthogonalProjection`
- `boundedBorelFunctionalCalculus`
- `spectralProjection_empty`
- `spectralProjection_univ`
- `spectralProjection_comp`
- `spectralProjection_isOrthogonalProjection`
- `spectralProjection_comm`
- `reduces_spectralSubspace`
- `spectralProjection_compl`
- `spectralProjection_stronglyCountablyAdditive`
- `spectralProjection_eq_zero_of_disjoint_spectrum`
- `boundedBorelFunctionalCalculus_indicator`
- `boundedBorelFunctionalCalculus_mul`
- `norm_boundedBorelFunctionalCalculus_le`

## `DavisKahan/Experimental/InfiniteDimensional/Core/Unbounded.lean` — 6
- `adjoint`
- `addRelative`
- `spectralProjection`
- `isSelfAdjoint_addBounded`
- `isSelfAdjoint_of_relativelyBounded`
- `sinTheta_unbounded_boundedPerturbation`

## `DavisKahan/Experimental/InfiniteDimensional/Core/UnboundedSpectral.lean` — 31
- `closedOperator_adjoint_closed`
- `closedOperator_adjoint_adjoint`
- `selfAdjoint_resolventData_of_im_ne_zero`
- `norm_closedOperatorResolvent_le_inv_abs_im`
- `closedOperatorCayleyTransform`
- `closedOperatorCayleyTransform_unitary`
- `selfAdjointSpectralProjection`
- `selfAdjointSpectralProjection_idempotent`
- `selfAdjointSpectralProjection_symmetric`
- `selfAdjointSpectralProjection_empty`
- `selfAdjointSpectralProjection_univ`
- `selfAdjointSpectralProjection_inter`
- `selfAdjointSpectralProjection_disjoint_additive`
- `selfAdjointSpectralProjection_iUnion_tendsto`
- `selfAdjointSpectralProjection_eq_zero_of_disjoint_spectrum`
- `selfAdjointSpectralProjection_Icc_range_le_domain`
- `spectralCutoff_isOrthogonalProjection`
- `spectralCutoff_range_le_domain`
- `spectralCutoff_commutes_on_domain`
- `spectralCutoff_tendsto_identity`
- `boundedSpectralTruncation`
- `boundedSpectralTruncation_isSymmetric`
- `boundedSpectralTruncation_eq_on_cutoff`
- `boundedSpectralTruncation_tendsto_on_domain`
- `mem_domain_iff_boundedSpectralTruncation_norm_bounded`
- `boundedSpectralTruncation_lowerBound`
- `boundedSpectralTruncation_upperBound`
- `boundedSpectralTruncation_commutes_cutoff`
- `domain_eq_top_of_spectrumIn_Icc`
- `boundedRealization_of_spectrumIn_Icc`
- `boundedInverse_of_spectrumOutside`

## `DavisKahan/Experimental/InfiniteDimensional/DirectRotation.lean` — 6
- `directRotation`
- `directRotation_unitary`
- `directRotation_maps_subspace`
- `directRotation_intertwines`
- `directRotation_sq`
- `directRotation_minimal`

## `DavisKahan/Experimental/InfiniteDimensional/DoubleAngle.lean` — 4
- `sinTwoTheta_reflectionDefect`
- `sinTwoTheta_residual`
- `sinTwoTheta_generalSeparation`
- `ideal_sinTwoTheta`

## `DavisKahan/Experimental/InfiniteDimensional/Ideals/CompactAndSingular.lean` — 3
- `compactSpectralSubspace`
- `compact_projection_difference`
- `hermitianDilation_spectralProjection_sinTheta`

## `DavisKahan/Experimental/InfiniteDimensional/Ideals/Rectangular.lean` — 5
- `compactOperatorNorm`
- `hilbertSchmidt`
- `traceClass`
- `schatten`
- `kyFan`

## `DavisKahan/Experimental/InfiniteDimensional/Ideals/Symmetric.lean` — 8
- `operatorNorm`
- `compactOperator`
- `schatten`
- `traceClass`
- `hilbertSchmidt`
- `kyFan`
- `gauge_diagonalPart_le`
- `gauge_offDiagonalPart_le`

## `DavisKahan/Experimental/InfiniteDimensional/OperatorBlocks/OffDiagonal.lean` — 6
- `continuedSpectralSubspace`
- `continuedSpectralSubspace_hasOrthogonalProjection`
- `gap_preserved_of_offDiagonal`
- `tanTwoTheta_offDiagonal`
- `aPrioriTanTheta`
- `spectral_repulsion_offDiagonal`

## `DavisKahan/Experimental/InfiniteDimensional/Sharpness.lean` — 4
- `sinTheta_planar_equality`
- `sinTwoTheta_planar_asymptotically_sharp`
- `sqrtTwo_threshold_sharp`
- `ideal_planar_extremizer`

## `DavisKahan/Experimental/InfiniteDimensional/SinTheta/Continuation.lean` — 1
- `continuous_continuedProjection`

## `DavisKahan/Experimental/InfiniteDimensional/SinTheta/General.lean` — 5
- `sinTheta_residual`
- `sinTheta_perturbation`
- `sinTheta_generalSeparation`
- `spectralProjection_sinTheta`
- `ideal_sinTheta`

## `DavisKahan/Experimental/InfiniteDimensional/SinTheta/SpectralBridge.lean` — 4
- `norm_sub_midpoint_le_of_spectrumIn_Icc`
- `centered_isUnit_of_spectrumOutside`
- `centeredIntervalExteriorWitness_of_gap`
- `sylvester_mem_and_gauge_le_of_intervalExteriorGap`

## `DavisKahan/Experimental/InfiniteDimensional/Sylvester/Basic.lean` — 4
- `sylvesterResolventIntegral`
- `sylvester_solve`
- `norm_sylvester_le_of_orderedSeparation`
- `norm_sylvester_le_of_generalSeparation`

## `DavisKahan/Experimental/InfiniteDimensional/Sylvester/Resolvent.lean` — 5
- `norm_resolvent_le_inv_distance`
- `ContourSeparatesSpectrum`
- `rieszProjection`
- `rieszProjection_eq_spectralProjection`
- `continuous_rieszProjection_path`

## Retired duplicate continuation roadmap API

The following unused speculative names were removed with the obsolete duplicate API; the module path now imports the completed proof-carrying continuation stack:

- `IsPiecewiseC1ClosedContour`
- `ContourSelectsSpectralComponent`
- `ProofCarryingSeparatingContour`
- `ResolventCurveIntegrable`
- `proofCarryingContour_resolventCurveIntegrable`
- `normalizedRieszProjection`
- `continuousOn_normalizedRieszProjection_operatorPath`
- `normalizedRieszProjection_eq_spectralProjection`
- `unitary_transport_of_continuous_projection_path`
- `continuedSpectralProjection_unitary_transport`

Replacement modules:

- `DavisKahan.Experimental.InfiniteDimensional.SinTheta.ContinuationContour`
- `DavisKahan.Experimental.InfiniteDimensional.SinTheta.ContinuationTransport`
- `DavisKahan.Experimental.InfiniteDimensional.SinTheta.ContinuationSpectralIdentification`
- `DavisKahan.Experimental.InfiniteDimensional.SinTheta.ContinuationRotationChain`
- `DavisKahan.Experimental.InfiniteDimensional.SinTheta.ContinuationTheorem`

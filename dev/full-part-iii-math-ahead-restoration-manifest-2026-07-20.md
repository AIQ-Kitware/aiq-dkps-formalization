# Full Part III math-ahead executable manifest

This human-readable file accompanies the machine-readable JSON manifest.

- Historical restoration base: `7463ca25c64a46c48411a2769b47714889974a97`
- Historical proof-body source: `2244e7c6bd7f`
- Executable guarded declarations: **39**
- Active Experimental repair roots: **0**
- Parked Experimental repair roots: **0**

The historical restoration count is no longer treated as executable proof debt. Unsupported or false declarations from the abandoned ambient route were retired on 2026-07-21; their exact source is preserved under `dev/retired-full-part-iii-ambient-route-2026-07-21/`. See `dev/full-part-iii-experimental-closure-2026-07-21.md`.

## `DavisKahan/Experimental/FiniteDimensional/Core/AngleOperators.lean` — 5
- `angleOperator`
- `principalAngles_orthogonal`
- `tanAngleOperator`
- `tanThetaMap`
- `tanTwoAngleOperator`

## `DavisKahan/Experimental/FiniteDimensional/DirectRotation.lean` — 12
- `angleComplexStructure`
- `directRotation_apply_eq_self_of_mem_common`
- `directRotation_comm_angleOperator`
- `directRotation_eq_cos_add_J_sin`
- `directRotation_eq_polarFactor`
- `directRotation_minimizes_displacementSquare_uiNorm`
- `directRotation_minimizes_max_displacement`
- `directRotation_minimizes_sum_sq_basis_angles`
- `directRotation_minimizes_uiNorm_of_largestAngle_le_pi_div_three`
- `directRotation_sq`
- `directRotation_symm`
- `directRotation_unique`

## `DavisKahan/Experimental/FiniteDimensional/DoubleAngle/SinTheta.lean` — 1
- `sinTwoTheta_residual_le`

## `DavisKahan/Experimental/FiniteDimensional/Generalized.lean` — 4
- `generalizedSinTheta_frobenius_le_of_spectralDistance`
- `generalizedSinTheta_nuclear_le_of_spectralDistance`
- `sinTwoTheta_acute_of_small_perturbation`
- `spectralSubspace_path_continuous`

## `DavisKahan/Experimental/FiniteDimensional/Norms/Rectangular.lean` — 1
- `schatten`

## `DavisKahan/Experimental/FiniteDimensional/Residual/AngleEmbeddings.lean` — 6
- `isTransverse_of_tanTheta_residual_gap`
- `singularValues_graphOperator`
- `tanThetaEmbedding`
- `tanTheta_residual_le`
- `tanTheta_vector_le`
- `tanTwoThetaEmbedding`

## `DavisKahan/Experimental/FiniteDimensional/Sharpness.lean` — 8
- `modelTanThetaPerturbation`
- `principalAngles_model`
- `sinTheta_constant_optimal`
- `sinTheta_model_equality`
- `sinTwoTheta_constant_optimal`
- `sinTwoTheta_model_operatorNorm_equality`
- `tanTheta_model_equality`
- `tanTwoTheta_model_equality`

## `DavisKahan/Experimental/FiniteDimensional/TanTheta/GraphOperator.lean` — 2
- `tanThetaMap_perturbation_le`
- `tanTheta_perturbation_le`

## Additional compilation modules

- `DavisKahan/Experimental/FiniteDimensional/TanTheta/GraphOperator.lean`
- `DavisKahan/Experimental/FiniteDimensional/DoubleAngle/TanTheta.lean`
- `DavisKahan/Experimental/FiniteDimensional/Generalized.lean`
- `DavisKahan/Experimental/FiniteDimensional/DirectRotation.lean`
- `DavisKahan/Experimental/FiniteDimensional/All.lean`
- `DavisKahan/Experimental/InfiniteDimensional/Core/AbstractSpectrum.lean`
- `DavisKahan/Experimental/InfiniteDimensional/Core/OperatorAngle.lean`
- `DavisKahan/Experimental/InfiniteDimensional/Core/SpectralProjection.lean`
- `DavisKahan/Experimental/InfiniteDimensional/All.lean`
- `DavisKahan/Experimental/PartIII.lean`
- `DavisKahan/Experimental/All.lean`

## Source corrections

- `DavisKahan/Experimental/FiniteDimensional/DoubleAngle/TanTheta.lean`: Replace absolute InternalGap by OrderedInternalGap. The old statements were false for interlacing diagonal-block spectra; an explicit three-dimensional quarter-turn counterexample is recorded in dev/tan-two-theta-ordered-gap-correction-2026-07-20.md.
- `DavisKahan/Experimental/FiniteDimensional/DoubleAngle/SinTheta.lean`: Replace the ill-typed InternalGap body by the source-complete interval/exterior residual signature. The residual separation is between M and the unwanted spectrum of A on U orthogonal; ordered and general separated-spectrum variants are supplied alongside it. See dev/sin-two-theta-residual-gap-correction-2026-07-20.md.
- `DavisKahan/Experimental/FiniteDimensional/Sharpness.lean`: The one-sided sinTwoAngleOperator has one nonzero singular value per principal plane, while the historical symmetric perturbation has two; arbitrary UI-norm equality is false. The retained operator-norm theorem is rank-insensitive and correct.
- `DavisKahan/Experimental/InfiniteDimensional`: Retire the unsupported incomplete-RCLike ambient facade and use the canonical complete-complex, real-complexified, vendored-Spectra, and production unbounded routes. Historical source is preserved under dev.
- `DavisKahan/Experimental/FiniteDimensional/TanTheta/GraphOperator.lean`: Replace mixed ambient/subtype graph statements by the canonical rectangular trial-coordinate tangent perturbation theorem.
- `DavisKahan/Experimental/FiniteDimensional/DoubleAngle/TanTheta.lean`: Retire the false arbitrary-UI and contour-mixed family; retain the canonical finite coordinate definition and production bounded complex operator-norm theory.

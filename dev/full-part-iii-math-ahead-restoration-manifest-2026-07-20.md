# Full Part III math-ahead executable manifest

This human-readable file accompanies the machine-readable JSON manifest.

- Mathematics-ahead base: `d5e54a708c014d97c4124036d332c6d7caa2a10e`
- Executable guarded declarations: **39**
- Active Experimental compiler roots: **4**
- Parked Experimental roots: **0**

The active entries are complete candidate mathematics awaiting Lean elaboration repair: the finite principal-plane construction, direct-rotation majorization, generalized residual theory, and planar sharpness. The registry is not compilation evidence; its checker compiles each active root and then runs `lake build DavisKahan.Experimental`.

## `DavisKahan/Experimental/FiniteDimensional/Core/AngleOperators.lean` — 5
- `angleOperator`
- `principalAngles_orthogonal`
- `tanAngleOperator`
- `tanThetaMap`
- `tanTwoAngleOperator`

## `DavisKahan/Experimental/FiniteDimensional/DirectRotation.lean` — 12
- `angleComplexStructure`
- `directRotationCosine`
- `directRotation_apply_eq_self_of_mem_common`
- `directRotation_comm_cosine`
- `directRotation_eq_cos_add_J_sin`
- `directRotation_eq_polarFactor`
- `directRotation_minimizes_displacementSquare_uiNorm`
- `directRotation_minimizes_max_displacement`
- `directRotation_minimizes_restrictedDisplacement_uiNorm`
- `directRotation_minimizes_sum_sq_basis_angles`
- `directRotation_symm`
- `directRotation_unique`

## `DavisKahan/Experimental/FiniteDimensional/DoubleAngle/SinTheta.lean` — 1
- `sinTwoTheta_residual_le`

## `DavisKahan/Experimental/FiniteDimensional/Generalized.lean` — 2
- `generalizedSinTheta_frobenius_le_of_spectralDistance`
- `generalizedSinTheta_nuclear_le_of_spectralDistance`

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

## `DavisKahan/Experimental/InfiniteDimensional/SinTheta/ContinuationWitnessGraph.lean` — 2
- `sinTwoTheta_acute_of_small_perturbation`
- `spectralSubspace_path_continuous`

## Source corrections

- The finite `Generalized` module no longer imports the infinite contour hierarchy. Its two complete-space complex continuation wrappers retain the same statements in `ContinuationWitnessGraph.lean`.
- `Core/SpectralProjection.lean` now uses the actual vendored Spectra PVM and calculus modules; the nonexistent `Spectra.SpectralTheory.SpectralTheorem` import is removed.
- The historical real `pi / 3` full-displacement UI-norm theorem is removed because multiplicity-space mixing gives counterexamples. The valid replacement is unrestricted UI-norm minimality of `(I - W) P_U`.
- Full displacement-square majorization and its operator-norm and basis-energy consequences remain active.
- Earlier tan 2 theta, sin 2 theta, and planar sharpness source corrections recorded in the JSON manifest remain in force.

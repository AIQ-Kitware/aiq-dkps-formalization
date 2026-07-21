# Full Part III math-ahead executable manifest

This human-readable file accompanies the machine-readable JSON manifest.

- Mathematics-ahead base: `3aeeefa0c26e5fa1292223a4257ea60ebddf4e4a`
- Executable guarded declarations: **39**
- Active Experimental compiler roots: **3**
- Parked Experimental roots: **0**

The three active entries are complete candidate mathematics awaiting Lean elaboration repair: `Generalized.lean`, `Sharpness.lean`, and `DirectRotation.lean`. The registry is not compilation evidence; its default checker runs `lake build DavisKahan.Experimental`.

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
- `directRotation_minimizes_sum_sq_basis_angles`
- `directRotation_minimizes_uiNorm_of_largestAngle_le_pi_div_three`
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

## Source corrections

- `DavisKahan/Experimental/FiniteDimensional/DoubleAngle/TanTheta.lean`: Replace absolute InternalGap by OrderedInternalGap. The old statements were false for interlacing diagonal-block spectra; an explicit three-dimensional quarter-turn counterexample is recorded in dev/tan-two-theta-ordered-gap-correction-2026-07-20.md.
- `DavisKahan/Experimental/FiniteDimensional/DoubleAngle/SinTheta.lean`: Replace the ill-typed InternalGap body by the source-complete interval/exterior residual signature. The residual separation is between M and the unwanted spectrum of A on U orthogonal; ordered and general separated-spectrum variants are supplied alongside it. See dev/sin-two-theta-residual-gap-correction-2026-07-20.md.
- `DavisKahan/Experimental/FiniteDimensional/Sharpness.lean`: The one-sided sinTwoAngleOperator has one nonzero singular value per principal plane, while the historical symmetric perturbation has two; arbitrary UI-norm equality is false. The retained operator-norm theorem is rank-insensitive and correct.
- `DavisKahan/Experimental/InfiniteDimensional`: Retire the unsupported incomplete-RCLike ambient facade and use the canonical complete-complex, real-complexified, vendored-Spectra, and production unbounded routes. Historical source is preserved under dev.
- `DavisKahan/Experimental/FiniteDimensional/TanTheta/GraphOperator.lean`: Replace mixed ambient/subtype graph statements by the canonical rectangular trial-coordinate tangent perturbation theorem.
- `DavisKahan/Experimental/FiniteDimensional/DoubleAngle/TanTheta.lean`: Retire the false arbitrary-UI and contour-mixed family; retain the canonical finite coordinate definition and production bounded complex operator-norm theory.
- Finite direct rotation uses the global polar cosine |P_V P_U + P_Vperp P_Uperp|; the one-sided |P_V P_U| cannot appear in a full-space trigonometric identity.
- Davis--Kahan Proposition 4.4 is retained only over real inner-product spaces; the paper gives a complex counterexample.
- The direct-rotation uniqueness endpoint is polar-factor uniqueness for a unitary-positive factorization, replacing the fictional principal-plane square-root proof.

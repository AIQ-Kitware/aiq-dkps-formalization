# Sylvester semigroup mathematics pass

Prepared for the repository state archived at commit `9e2557409aa7`.

This overlay is deliberately confined to `DavisKahan/Experimental`.  It is a
mathematics-first pass: every displayed theorem has an explicit proof term or
tactic proof, but the files were written without a Lean process.  Expect local
repairs to declaration names, coercions, continuity instances, and universe
parameters.  The central arguments and all normalization constants are exposed
in small steps so those repairs should remain local.

## Critical mathematical correction

The requested two-sided scalar multiplier cannot have both

```text
integral mu_d(t) exp(i t x) dt = 1/x for |x| >= d
```

and exact `L1` mass `1/d`.  The correct Haagerup--Zsido reciprocal kernel has

```text
integral norm(mu_d(t)) dt = pi / (2 d).
```

Consequently arbitrary two-sided spectral separation gives the sharp general
Fourier-multiplier estimate

```text
d * norm(X) <= (pi / 2) * norm(C),
```

not the ordered-gap constant-one estimate.  The ordered theory remains separate
and does have constant one through a decaying semigroup integral.  The overlay
encodes this split rather than formalizing the false normalization.

The Fourier formula is stated over complex Hilbert spaces.  Same-space
`exp(i t A)` is not available over a real Hilbert space without choosing extra
structure.  Real conclusions require the repository's complexification layer.

## Files

### Primary Sylvester layer

- `DavisKahan/Experimental/InfiniteDimensional/Sylvester/FourierSemigroup.lean`
  - scaled Haagerup--Zsido kernel;
  - exact Fourier and mass identities;
  - bounded exponential groups;
  - finite spectral-step reconstruction;
  - norm-limit reconstruction;
  - right-inverse theorem and spectral-multiplier extensionality.
- `DavisKahan/Experimental/InfiniteDimensional/Sylvester/OrderedSemigroup.lean`
  - common cut extracted from ordered separation;
  - spectral exponential estimates;
  - Bochner integrability;
  - fundamental-theorem reconstruction.
- `DavisKahan/Experimental/InfiniteDimensional/Sylvester/Basic.lean`
  - the public Sylvester API;
  - ordered constant-one theorem;
  - general separated `pi/2` theorem;
  - uniqueness and compactness transport.
- `DavisKahan/Experimental/InfiniteDimensional/Sylvester/MathPass.lean`
  - aggregate experimental import.

### Secondary fronts

- `DavisKahan/Experimental/InfiniteDimensional/Ideals/CompactIntegral.lean`
- `DavisKahan/Experimental/InfiniteDimensional/Ideals/Rectangular.lean`
- `DavisKahan/Experimental/InfiniteDimensional/Ideals/Symmetric.lean`
- `DavisKahan/Experimental/InfiniteDimensional/Core/CompatibilitySinTwoTheta.lean`
- `DavisKahan/Experimental/InfiniteDimensional/GraphSubspace.lean`
- `DavisKahan/Experimental/InfiniteDimensional/SinTheta/ContinuationCore.lean`
- `DavisKahan/Experimental/InfiniteDimensional/SinTheta/ContinuationTransport.lean`
- `DavisKahan/Experimental/InfiniteDimensional/SinTheta/Continuation.lean`

The continuation facade now uses the repository's existing proof-carrying
`SpectralSeparatingContour` and `fixedContourRieszOperator` development.  It
does not recreate the removed fictional contour interface.

## Suggested compile order

Run the files individually, preserving the first failing local goal before
attempting the aggregate import.

```bash
lake env lean DavisKahan/Experimental/InfiniteDimensional/Ideals/Rectangular.lean
lake env lean DavisKahan/Experimental/InfiniteDimensional/Ideals/Symmetric.lean
lake env lean DavisKahan/Experimental/InfiniteDimensional/Ideals/CompactIntegral.lean
lake env lean DavisKahan/Experimental/InfiniteDimensional/Sylvester/FourierSemigroup.lean
lake env lean DavisKahan/Experimental/InfiniteDimensional/Sylvester/OrderedSemigroup.lean
lake env lean DavisKahan/Experimental/InfiniteDimensional/Sylvester/Basic.lean
lake env lean DavisKahan/Experimental/InfiniteDimensional/Core/CompatibilitySinTwoTheta.lean
lake env lean DavisKahan/Experimental/InfiniteDimensional/GraphSubspace.lean
lake env lean DavisKahan/Experimental/InfiniteDimensional/SinTheta/ContinuationCore.lean
lake env lean DavisKahan/Experimental/InfiniteDimensional/SinTheta/ContinuationTransport.lean
lake env lean DavisKahan/Experimental/InfiniteDimensional/SinTheta/Continuation.lean
lake env lean DavisKahan/Experimental/InfiniteDimensional/Sylvester/MathPass.lean
```

Start with imports and exact theorem names.  Do not change constants or weaken
hypotheses merely to close an elaboration goal.

# Lemma ledger

The signatures below are the signatures assumed by the mathematics pass.
Names in the first group were found in the repository or pinned dependencies.
Names in the second group describe mathematically explicit helper results whose
exact library names were not verified and may need to be supplied locally.

## Confidently present

### Reciprocal Fourier kernel

- `HaagerupZsido.reciprocalKernel : Real -> Complex`
- `HaagerupZsido.integrable_reciprocalKernel : Integrable reciprocalKernel`
- `HaagerupZsido.reciprocalKernel_fourier`:
  for `1 <= |x|`, the Fourier integral of `reciprocalKernel` at `x` is `x^-1`.
- `HaagerupZsido.integral_norm_reciprocalKernel`:
  `integral (fun t => norm (reciprocalKernel t)) = pi / 2`.

### Bounded exponential groups

- `expBounded : (H ->L[Complex] H) -> Real -> H ->L[Complex] H`
- `expBounded_at_zero' : expBounded A 0 = 1`
- `expBounded_add_smul : expBounded A (s+t) = expBounded A s oL expBounded A t`
- `expBounded_hasDerivAt : HasDerivAt (expBounded A) (A oL expBounded A t) t`
- `expBounded_norm_bound : norm (expBounded A t) <= exp (|t| * norm A)`
- `expBounded_mem_unitary`: a skew-adjoint generator exponentiates to a unitary.
- `smul_I_skewSelfAdjoint`: `I smul A` is skew-adjoint when `A` is self-adjoint.

### Spectral projections and functional calculus

- `boundedSelfAdjointSpectralPVM`
- `boundedSelfAdjointSpectralProjection`
- `boundedSelfAdjointSpectralProjection_isOrthogonalProjection`
- `boundedSelfAdjointSpectralProjection_mem_commutant`
- `boundedSelfAdjointSpectralProjection_apply_mem`
- `realSpectrum`
- `IsSelfAdjointOperator.adjoint_eq`
- `SpectraSeparated`
- `OrderedSpectraSeparated`

### Operator norm and composition

- `ContinuousLinearMap.opNorm_comp_comp_le`
- `ContinuousLinearMap.norm_adjoint`
- `ContinuousLinearMap.comp_apply`
- `ContinuousLinearMap.comp_add`, `add_comp`, `comp_sub`, `sub_comp`
- `ContinuousLinearMap.comp_smul`, `smul_comp`
- `ContinuousLinearMap.comp_finset_sum`, `finset_sum_comp`
- continuity of composition and addition in continuous-linear-map norm.

### Bochner integration

- `MeasureTheory.Integrable`
- `integral_smul_const`
- finite-sum interchange with a Bochner integral
- dominated convergence for Banach-valued integrals
- integral commutation with a continuous linear map
- scaling/change-of-variables for Lebesgue integration under `t |-> d*t`
- integrability of `t |-> exp (-d*t)` on `Ici 0` for `d > 0`
- its exact integral `1/d`.

### Compact maps

- `IsCompactOperator`
- `isCompactOperator_zero`
- `IsCompactOperator.add`
- `IsCompactOperator.smul`
- `IsCompactOperator.adjoint`
- `IsCompactOperator.comp_left_right`
- `isClosed_setOf_isCompactOperator`

### Approximation-number ideal support

- `RectangularSymmetricIdealFamily`
- `RectangularSymmetricIdealFamily.operatorNorm`
- `KyFanDominantIdealFamily.kyFan`
- `kyFanApproximationGauge`
- `opNorm_le_kyFanApproximationGauge`
- `kyFanApproximationGauge_add_le`
- `kyFanApproximationGauge_smul`
- `kyFanApproximationGauge_adjoint`
- `kyFanApproximationGauge_comp_le`
- `KyFanDominantIdealFamily.kyFan_gauge_complete`

### Graph-subspace support

- `projection`
- `graphSubspace`
- `graphSubspace_eq_range`
- `projection_graphSubspace_formula`
- `subspaceGap_graphSubspace`
- `IsAngularOperator`
- `Units.oneSub`
- `ContinuousLinearMap.isUnit_iff`
- projection idempotence, range membership, and orthogonal-complement formulas.

### Existing continuation support

- `SpectralSeparatingContour`
- `fixedContourRieszOperator`
- `fixedContourRieszOperator_operatorPath_isOrthogonalProjection`
- `continuous_fixedContourRieszOperator_operatorPath`
- `SpectralSeparatingContour.contourRieszProjection_eq_boundedSelfAdjointSpectralProjection`
- `boundedSelfAdjointSpectralProjection`
- `operatorPath`

## Helper declarations likely needing local implementation or renaming

Each item is a standard consequence of the displayed existing infrastructure;
none is intended as a new foundational assumption.

- `spectralPVM_proj_congr_of_inter_spectrum_eq`:
  PVM projections agree when two measurable sets have the same intersection
  with the supporting real spectrum.
- `measurable_piecewise_finite_partition`:
  a finite piecewise-constant function on measurable cells is measurable.
- `boundedSelfAdjointBorelCalculus_eq_finset_sum_indicator`:
  the Borel calculus of a finite step function is the corresponding finite sum
  of spectral projections.
- `boundedSelfAdjointBorelCalculus_id`:
  the Borel calculus of the identity function is the original self-adjoint
  operator.
- `boundedSelfAdjointBorelCalculus_norm_sub_le`:
  a uniform scalar bound on the spectrum bounds the operator-norm difference.
- `realSpectrum_isCompact`:
  the real spectrum of a bounded self-adjoint operator is compact.
- `pairwiseDisjoint_successiveDifference`:
  successive set differences of a finite cover are pairwise disjoint.
- `successiveDifference_covers_of_finset_ball_cover`:
  those successive differences retain the original cover.
- `active_ball_meets_spectrum` and `choose_spectrum_point_in_ball`:
  choose a representative from each active spectral ball.
- `exp_finset_orthogonal_idempotents`:
  exponentiation of a finite sum of orthogonal idempotents acts coefficientwise.
- `spectralProjection_pairwise_orthogonal`:
  disjoint measurable spectral cells have orthogonal projections.
- `spectralProjection_select_left` and `spectralProjection_select_right`:
  a spectral block selects its own coefficient from a finite spectral step.
- `tendsto_expBounded_of_tendsto`:
  norm convergence of generators implies norm convergence of bounded
  exponentials at each fixed time.
- `norm_bounded_of_tendsto`:
  every convergent operator sequence is uniformly norm bounded.
- `continuous_unitary_orbit`:
  continuity of `t |-> exp(i t A) C exp(-i t B)`.
- `measurable_separatedSylvesterMultiplier`:
  measurability of the reciprocal kernel, derivable from its integrability.
- `integral_finset_sylvester_blocks`:
  finite spectral block expansion commutes with the Bochner integral.
- `FiniteSpectralStep.operator_isSelfAdjoint`:
  a real finite spectral step is self-adjoint.

The first compiler pass should either map these to existing names or create
small local lemmas with exactly these statements.  The difficult one is the
finite-step Borel-calculus identity; the rest are elementary measure, topology,
or finite-sum facts.

# Per-declaration confidence

## Scalar and exponential layer

- `separatedSylvesterMultiplier`: complete.
- `integrable_separatedSylvesterMultiplier`: probably complete; scaling lemma name may differ.
- `separatedSylvesterMultiplier_identity`: complete mathematics; change-of-variables API may differ.
- `l1_norm_separatedSylvesterMultiplier`: complete mathematics; change-of-variables API may differ.
- `mul_l1_norm_separatedSylvesterMultiplier`: complete.
- `unitaryGroup`: complete.
- `semigroup`: complete.
- `unitaryGroup_zero`: probably complete.
- `semigroup_zero`: probably complete.
- `unitaryGroup_add`: probably complete.
- `semigroup_add`: probably complete.
- `unitaryGroup_mem_unitary`: probably complete.
- `unitaryGroup_neg_mul`: probably complete.
- `norm_unitaryGroup_le_one`: probably complete.
- `norm_unitaryGroup`: probably complete; requires a nonzero space.
- `norm_unitary_left_right`: complete mathematics; composition simplification may need repair.
- `hasDerivAt_unitaryGroup`: probably complete.
- `hasDerivAt_semigroup`: probably complete.
- `norm_semigroup_le_exp_norm`: probably complete.

## Finite spectral approximation

- `FiniteSpectralStep`: complete definition.
- `FiniteSpectralStep.operator`: complete.
- `FiniteSpectralStep.sum_projection_eq_one`: complete mathematics; PVM congruence helper required.
- `FiniteSpectralStep.norm_operator_sub_le`: analytically hard step at the finite-step Borel calculus identity.
- `exists_finiteSpectralStep`: complete compact-cover construction; finite indexing and representative choices need repair.
- `finiteSpectralStep_representatives_separated`: complete.
- `unitaryGroup_finiteSpectralStep`: analytically hard step at exponential functional calculus of orthogonal blocks.
- `finiteSpectralStep_reconstruction`: complete blockwise argument; finite-sum integration helper required.
- `tendsto_unitary_orbit`: probably complete.
- `separatedSylvester_reconstruction_complex`: complete mathematical limit argument; dominated-convergence names may differ.
- `separatedSylvester_integrable_complex`: probably complete.
- `spectral_step_integral_right_inverse`: complete mathematical limit argument; same finite-block helper required.
- `spectralMultiplier_ext`: complete as a corollary of the right-inverse theorem; its consumer-facing binder order may need adjustment.

## Ordered theory

- `restrictedSpectrum_top_eq_realSpectrum`: probably complete.
- `exists_common_cut_of_orderedSeparation`: complete mathematics; spectrum extrema need nonempty-spectrum edge handling.
- `semigroup_eq_cfc`: probably complete.
- `norm_semigroup_le_of_spectrum_subset_Iic`: analytically hard step at the CFC norm formula.
- `norm_semigroup_neg_le_of_spectrum_subset_Ici`: analytically hard step at the CFC norm formula.
- `orderedSemigroup_integrand_bound`: complete once the preceding two bounds elaborate.
- `orderedSylvester_integrable`: complete mathematics; exponential-integral API may differ.
- `hasDerivAt_ordered_solution_orbit`: complete product-rule calculation; derivative API repair expected.
- `ordered_orbit_sub_eq_integral`: complete fundamental-theorem argument; interval-integral orientation may need repair.
- `tendsto_ordered_solution_orbit_zero`: complete from the exponential bound.
- `orderedSylvester_reconstruction`: complete.

## Public Sylvester API

- `sylvesterOperator`: complete.
- `sylvesterOperator_add`: complete.
- `sylvesterOperator_sub`: complete.
- `sylvesterOperator_smul`: complete.
- `norm_sylvesterOperator_le`: complete.
- `norm_sylvester_le_of_coercive`: complete.
- `norm_sylvester_le_of_orderedSeparation`: complete once ordered reconstruction elaborates.
- `separatedSylvesterSolution`: complete.
- `separatedSylvester_reconstruction`: complete, complex scope.
- `separatedSylvester_integrable`: complete, complex scope.
- `sylvester_solve`: complete once the right-inverse theorem elaborates.
- `norm_sylvester_le_of_generalSeparation`: complete with constant `pi/2`.
- `sylvester_unique`: complete.
- `compact_mem_of_separatedSylvester_solution`: complete mathematics once compact-valued integration elaborates; complex scope.

## Ideals

- `compactOperatorSubmodule`: complete.
- `isClosed_compactOperatorSubmodule`: probably complete.
- `isCompactOperator_integral`: complete closed-subspace lifting argument; subtype integral API may differ.
- `RectangularSymmetricIdealFamily.compactOperatorNorm`: probably complete.
- `RectangularSymmetricIdealFamily.kyFan`: should be replaced directly by the existing `KyFanDominantIdealFamily.kyFan` rectangular family.
- `RectangularSymmetricIdealFamily.hilbertSchmidt`: analytically hard step at infinite-dimensional Hilbert--Schmidt completeness and basis independence.
- `RectangularSymmetricIdealFamily.traceClass`: analytically hard step at infinite-dimensional trace-class infrastructure.
- `RectangularSymmetricIdealFamily.schatten`: analytically hard step at infinite-dimensional Schatten infrastructure.
- `SymmetricNormIdeal.ofRectangular`: complete mathematics; structure telescope repairs likely.
- `SymmetricNormIdeal.operatorNorm`: probably complete.
- `SymmetricNormIdeal.compactOperator`: probably complete.
- `SymmetricNormIdeal.kyFan`: probably complete after redirecting to the existing family.
- `SymmetricNormIdeal.hilbertSchmidt`, `traceClass`, `schatten`: depend on the preceding analytic fronts.
- `gauge_unitary_conjugation`: complete.
- `gauge_diagonalPart_le`: complete reflection-averaging proof.
- `gauge_offDiagonalPart_le`: complete reflection-averaging proof.

## Geometry and continuation

- `sinTwoThetaEmbedding`: complete explicit formula.
- `sinTwoThetaEmbedding_eq_rangeAngle`: complete as an explicit operator identity; alignment with any older named `sinTwoAngleOperator` requires a bridge lemma.
- `acute_iff_exists_bounded_angularOperator`: complete for the repository's uniform definition `subspaceGap U V < 1`.
- `existsUnique_angularOperator`: complete once the acute construction elaborates.
- `tan_maximalAngle_eq_norm_angularOperator`: probably complete; trigonometric simplification may need repair.
- `norm_angularOperator_lt_one_iff`: probably complete; endpoint trigonometry may need repair.
- `continuedProjection`: complete definition on a proof-carrying contour.
- `continuous_continuedProjection`: complete wrapper around the existing continuity theorem.
- `continuedProjection_eq_spectralProjection`: complete wrapper around the existing spectral-identification theorem.
- `continuedProjection_isOrthogonalProjection`: complete wrapper.

# Divergences and semantic alignment

1. **Two-sided separation constant.**  The requested `1/d` scalar mass and
   constant-one general theorem are false.  The overlay uses `pi/(2d)` and
   the `pi/2` theorem.  Ordered separation remains constant one.
2. **Scalar field.**  Fourier reconstruction is complex-only.  The paper's real
   conclusions must pass through complexification.
3. **Unitary norm.**  Equality with one requires a nonzero Hilbert space.  The
   unconditional theorem is the contraction bound.
4. **Infinite-dimensional acuteness.**  The repository's bounded-operator
   `IsAcute` means the uniform condition `subspaceGap U V < 1`; this is stronger
   than the paper's purely intersection-based acute case.  A bounded graph
   operator is equivalent to the uniform condition, not to mere injectivity of
   crossed projections.
5. **Continuation interface.**  The old scalar-contour facade did not carry the
   hypotheses needed to identify a Riesz projection.  The replacement accepts
   `SpectralSeparatingContour`, which records those hypotheses explicitly.
6. **Double-angle compatibility.**  The overlay defines the infinite-dimensional
   embedding explicitly as `2 P_(U perp) P_range(X) P_U`.  A human must verify
   that this is the same orientation intended by each source-facing use of
   `sin(2 Theta)`.
7. **Infinite-dimensional Schatten families.**  Finite-dimensional Schatten
   norms and the approximation-number Hilbert--Schmidt layer exist, but a full
   rectangular complete Schatten/trace-class package does not.  The structure
   proofs in `Rectangular.lean` expose the exact required laws; the compiler
   agent should not mistake unresolved foundational names there for simple
   spelling repairs.
8. **Compactness transport.**  The compact-solution theorem is presently complex
   because it uses the Fourier representation.  A real statement requires
   proving that the complexified solution descends.

## Recommended first takeover

1. Repair the scalar kernel identities and bounded exponentials.
2. Land the finite-step support lemmas, one at a time.
3. Compile `finiteSpectralStep_reconstruction` before attempting the limit.
4. Compile the ordered semigroup path independently.
5. Redirect the Ky Fan family to `KyFanDominantIdealFamily.kyFan`.
6. Keep the full Schatten/trace infrastructure as a separate analytic campaign.
7. Compile the existing contour-based continuation wrappers only after the
   Sylvester files are stable.

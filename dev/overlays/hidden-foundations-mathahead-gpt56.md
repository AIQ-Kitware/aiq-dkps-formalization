# Hidden-foundation mathematics-ahead handoff

This overlay is a recursive audit and mathematics-ahead pass for the remaining
Davis--Kahan 1970 frontier.  It is deliberately additive and isolated under
`DavisKahan/Experimental/MathAhead/HiddenFoundations`.

The central purpose is to stop high-level frontier declarations from concealing
entire missing theories.  Every discovered foundation is classified as one of:

- **proof candidate**: a complete mathematical proof attempt is written;
- **construction**: a concrete definition or assembly is written;
- **bridge**: existing proof-carrying infrastructure is reused;
- **interface**: a genuine foundational campaign is exposed as a precise record.

An interface is not completion.  It identifies the exact theorems a later
analytic construction must provide.

## Static status

Run:

```bash
python3 scripts/check_davis_kahan_hidden_foundations.py --write-report
```

Current static result:

- 57/57 tracked declarations are textually present;
- 35 full-proof candidates;
- 7 concrete constructions;
- 8 bridges into existing infrastructure;
- 7 explicit unresolved-foundation interfaces;
- no missing internal dependency identifiers;
- no dependency cycles;
- no proof-escape markers in the hidden Lean files.

The machine-readable graph is:

```text
dev/davis-kahan-hidden-foundations.json
```

The generated report is:

```text
dev/davis-kahan-hidden-foundations-status.md
```

Use `--lean-probe` after the files begin to elaborate.  The probe is module
local, so one failing campaign does not hide the status of unrelated campaigns.

## Main discoveries

### 1. Section 3 is two distinct campaigns

The constructive nonacute direct-rotation result does not require a new
spectral theorem.  It is built from:

- final-space identities for the polar partial isometry;
- projection intertwinement of polar factors;
- an arbitrary isometric equivalence between the crossed Halmos defects;
- orthogonal assembly on the regular and defect summands.

That construction is attempted in full, culminating in:

```lean
ForMathlib.DavisKahan.Experimental.MathAhead.HiddenFoundations.proposition3_2_completed
```

The paper's Theorem 3.1 is different.  Its language of spectral multiplicity
functions requires a direct-integral classification theorem for bounded
self-adjoint operators.  No such production API was found.  The overlay proves
an operator-level classification assembly and isolates the missing
multiplicity theorem in `SpectralMultiplicityFoundation`.

### 2. Section 8 does not need another operator-valued contour theory

The repository already has a proof-carrying generic contour continuation layer,
including operator-valued contour integration, identification with genuine
spectral projections, norm transport, and continuation witnesses.  The missing
piece is geometric: produce one explicit positive circle and prove its winding
laws uniformly along the path.

`ContourReuseBridge.lean` forwards the existing analytic results.
`CircleContourGeometry.lean` supplies the circle specialization.

Do not revive the removed fictional contour API, and do not duplicate the
production contour integration layer.

### 3. Real Sylvester estimates are a transport problem

The complex Fourier representation can be descended to real Hilbert spaces by:

- complexifying the operators and the Sylvester equation;
- proving preservation of invertibility and real spectrum;
- preserving the spectral-separation hypothesis;
- applying all finite Ky Fan inequalities over the complexification;
- using the repository's Ky Fan completeness principle for UI norms.

The full proof attempt is in `RealSylvesterDescent.lean`.  This is independent of
the compiler agent's active finite-step Borel-calculus campaign.

### 4. Rectangular ideals split into an accessible Hilbert--Schmidt case and a
real missing Schatten theorem

The complex Hilbert--Schmidt family can be built from the existing canonical
Hilbert tensor representation.  A proof attempt is in
`HilbertSchmidtComplexFamily.lean`.

General trace and Schatten classes require a real approximation-number theorem:
the `ell^p` gauge must satisfy the triangle inequality, ideal domination,
adjoint invariance, and completeness.  `SchattenApproximationFoundation` states
that entire theorem package explicitly.  It does not pretend the package has
been proved.

### 5. The Section 9 obstruction is now precise

The finite matrix and printed arithmetic layers are no longer the hard part.
The remaining analytic construction consists of:

- an interval Sobolev space with endpoint traces through order three;
- the closed free-boundary fourth derivative;
- its adjoint-domain characterization and self-adjointness;
- compactness of the graph embedding;
- identification of the affine zero eigenspace;
- localization of the first positive root of
  `cos beta * cosh beta = 1`.

`FreeBeamCharacteristic.lean` develops the elementary ODE, boundary determinant,
characteristic equation, and exact `4.73^4 > 500` arithmetic.
`FreeBeamAnalyticFoundation.lean` exposes the remaining interval
functional-analysis layer as `SobolevTraceFoundation` and derives the spectral
gap from it.

## File-by-file compile order

The following order localizes failures and respects the dependency graph.

### Polar and Section 3 construction

```bash
lake env lean \
  DavisKahan/Experimental/MathAhead/HiddenFoundations/PolarIsometryFinal.lean
lake env lean \
  DavisKahan/Experimental/MathAhead/HiddenFoundations/PolarIntertwining.lean
lake env lean \
  DavisKahan/Experimental/MathAhead/HiddenFoundations/OrthogonalSummandCoordinates.lean
lake env lean \
  DavisKahan/Experimental/MathAhead/HiddenFoundations/Section3Nonacute.lean
lake env lean \
  DavisKahan/Experimental/MathAhead/HiddenFoundations/TwoProjectionOperatorClassification.lean
lake env lean \
  DavisKahan/Experimental/MathAhead/HiddenFoundations/SpectralMultiplicityFoundation.lean
```

### Ky Fan, real descent, and ideals

Compile these only after the compiler agent's complex separated Sylvester
reconstruction is available under its final promoted name.

```bash
lake env lean \
  DavisKahan/Experimental/MathAhead/HiddenFoundations/KyFanBochner.lean
lake env lean \
  DavisKahan/Experimental/MathAhead/HiddenFoundations/RealSylvesterDescent.lean
lake env lean \
  DavisKahan/Experimental/MathAhead/HiddenFoundations/HilbertSchmidtComplexFamily.lean
lake env lean \
  DavisKahan/Experimental/MathAhead/HiddenFoundations/SchattenApproximationFoundation.lean
```

### Existing contour reuse and explicit circle geometry

```bash
lake env lean \
  DavisKahan/Experimental/MathAhead/HiddenFoundations/ContourReuseBridge.lean
lake env lean \
  DavisKahan/Experimental/MathAhead/HiddenFoundations/CircleContourGeometry.lean
```

### Section 9 analytic layer

```bash
lake env lean \
  DavisKahan/Experimental/MathAhead/HiddenFoundations/FreeBeamCharacteristic.lean
lake env lean \
  DavisKahan/Experimental/MathAhead/HiddenFoundations/FreeBeamAnalyticFoundation.lean
```

Finally:

```bash
lake env lean \
  DavisKahan/Experimental/MathAhead/HiddenFoundations/All.lean
python3 scripts/check_davis_kahan_hidden_foundations.py \
  --lean-probe --write-report
```

## Confidence ledger

### High confidence in the mathematical architecture

- final projection of the polar partial isometry;
- decomposition into regular and crossed-defect parts;
- nonacute extension by an arbitrary defect-space isometry;
- operator-level classification by four trivial summands plus generic pair;
- reuse of the existing generic contour continuation theory;
- complexification route for real finite Ky Fan estimates;
- free-beam determinant and characteristic equation;
- exact numerical implication `beta > 4.73 -> beta^4 > 500`;
- the field list in the Schatten and interval-Sobolev interfaces.

### Complete proof attempts, but substantial elaboration repair is expected

- `PolarIsometryFinal.lean`;
- `PolarIntertwining.lean`;
- `OrthogonalSummandCoordinates.lean`;
- `Section3Nonacute.lean`;
- `TwoProjectionOperatorClassification.lean`;
- `CircleContourGeometry.lean`;
- `KyFanBochner.lean`;
- `RealSylvesterDescent.lean`;
- `FreeBeamCharacteristic.lean`.

### Analytically difficult proof attempts

- completeness of the Hilbert--Schmidt gauge through the tensor model;
- some final polar-range closure identities;
- the exact circle-path coercions into the production contour record.

### Explicitly incomplete foundational constructions

These are interfaces, not completed proofs:

- `SpectralMultiplicityFoundation`;
- `CompactPositiveListFoundation`;
- `SchattenApproximationFoundation`;
- `PositiveRootLocalization`;
- `SobolevTraceFoundation`;
- `UniformCircleSeparation` and `RealizedCircleContinuationData` are input-data
  records; their downstream bridges are complete relative to the supplied data.

## Lemma ledger

### Existing declarations used with high confidence

#### Spectra polar decomposition

- `Spectra.QuantumMechanics.Channels.polarIsometry`
- `Spectra.QuantumMechanics.Channels.polarIsometry_apply_eq`
- `Spectra.QuantumMechanics.Channels.polarIsometry_adjoint_comp_self`
- `Spectra.QuantumMechanics.Channels.polarRange`
- `Spectra.QuantumMechanics.Channels.ker_absOp`
- `Submodule.topologicalClosure_range_eq_orthogonal_ker_adjoint`

#### Existing Davis--Kahan geometry

- `halmosSourceDefect`
- `halmosTargetDefect`
- `halmosTrivialPart`
- `halmosGenericPart`
- `halmosTrivialPart_sup_genericPart`
- `spectraCanonicalIntertwiner`
- `spectraCanonicalPolarFactor`
- `IsPaperDirectRotation`
- the existing direct-rotation projection-intertwining declarations imported by
  `DavisKahan.Geometry.Polar.DirectRotation`.

#### Orthogonal projection API

- `Submodule.starProjection_eq_self_iff`
- `Submodule.starProjection_apply_eq_zero_iff`
- `Submodule.orthogonalProjection_eq_zero_iff`
- `Submodule.HasOrthogonalProjection.exists_orthogonal`
- `Submodule.topologicalClosure_minimal`

#### Bochner and approximation-number API

- `ContinuousSeminorm.integral_le`
- approximation-number Ky Fan gauges and their finite-sum triangle inequalities
  from `DavisKahan.OperatorIdeal.ApproximationNumbers.ScalarGeneric`;
- unitary invariance of approximation numbers;
- complexification maps and norm preservation already used elsewhere in the
  repository.

#### Free-beam elementary analysis

- derivative rules for `Real.sin`, `Real.cos`, `Real.sinh`, `Real.cosh`;
- `Real.sin_sq_add_cos_sq`;
- `Real.cosh_sq_sub_sinh_sq`.

### Names or signatures likely to need compiler repair

- `LinearIsometryEquiv.prod` and the exact `WithLp 2` coordinate constructors;
- `WithLp.norm_sq_eq_add_norm_sq`;
- the exact final-space projection theorem available in Spectra, if one was
  added after this overlay was written;
- `Unitary.norm_map` field access for bundled continuous-linear unitaries;
- star simplification for projection products;
- the exact namespace of the production contour path and winding fields;
- `Complex.circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable`;
- `Complex.circleIntegral_eq_zero_of_differentiable_on_ball`;
- the continuous-seminorm constructor used for the Ky Fan gauge;
- complexification spectrum/invertibility theorem names;
- `Metric.cauchy_iff` and sequence-limit spelling in the Hilbert tensor space;
- the exact constructor and fields of `DavisKahanExt.ClosedOperator.mk`.

When one of these names is wrong, preserve the mathematical statement and
repair the local invocation.  Do not replace the proof by a stronger input
record unless the argument itself is invalid.

## Semantic divergences and scope records

### Section 3

- The construction is currently over complex Hilbert spaces because the
  production Halmos and polar APIs are complex.  The paper treats real and
  complex spaces.
- `CrossedDefectsEquivalent` is the constructive Hilbert-dimension condition.
  A separate theorem should identify it with equality of Hilbert cardinal
  dimensions.
- `proposition3_2_parameterization_completed` gives an injective family of
  direct rotations indexed by defect-space equivalences.  A claim that this is
  surjective onto every possible direct rotation would require an additional
  restriction/extension uniqueness argument.
- Theorem 3.1 in the paper is stated by spectral multiplicity functions.  The
  overlay proves only the modern operator-level assembly and explicitly records
  the missing direct-integral classification theorem.

### Section 8

- The explicit geometry uses one circle uniformly separating the selected and
  complementary real spectra.  The production continuation layer allows more
  general contours.  This is a specialization chosen because it is sufficient
  for the intended real-spectrum application.
- The continuation conclusions are bridges relative to a supplied uniform
  separation record.  Producing that record from the final Section 8 gap
  hypotheses is still a source-level step.

### Sylvester and ideals

- The arbitrary two-sided separated-spectrum estimate retains the corrected
  `pi/2` constant.  Constant one belongs to ordered separation.
- The Fourier reconstruction remains complex; the real theorem is obtained by
  complexification and Ky Fan descent.
- `hilbertSchmidtComplex` is complex-only.
- General Schatten and trace-class families remain relative to the explicit
  approximation-number foundation record.

### Section 9

- `SobolevTraceFoundation` does not construct `L2(0,1)` or interval Sobolev
  traces.  It specifies exactly what a construction must prove.
- The characteristic-equation calculation covers classical modes.  Connecting
  every positive spectral vector of the weak fourth-derivative realization to
  that classical normal form is part of the Sobolev/ODE regularity campaign.
- `PositiveRootLocalization` records localization and minimality of the first
  positive root.  The overlay proves the exact arithmetic consequence but not
  the transcendental root isolation itself.

## Promotion policy

Promote only declarations that:

1. elaborate independently;
2. have a clean proof closure;
3. do not depend on an interface record supplied as an unconstrained argument;
4. match the source or have an explicit modern-scope name.

In particular, do not mark Theorem 3.1, Corollary 3.1, or the Section 9 free-beam
model complete merely because their interface records elaborate.

## Recommended compiler allocation

The highest-yield order after the active Sylvester work is:

1. polar final-space identities;
2. nonacute direct rotation and Proposition 3.2;
3. circle geometry into the already compiled continuation theory;
4. Ky Fan Bochner transport and real descent;
5. free-beam characteristic algebra;
6. complex Hilbert--Schmidt family;
7. separate analytic campaigns for spectral multiplicity, Schatten
   completeness, interval Sobolev traces, and root localization.

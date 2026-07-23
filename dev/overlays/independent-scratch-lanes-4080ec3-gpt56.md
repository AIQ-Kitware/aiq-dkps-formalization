# Independent scratch lanes on 4080ec3

These drafts deliberately avoid Jon's active Circle Riesz, `SinTheta/General`,
continuation, and polar-decomposition lanes.

## Lane A: rectangular Hilbert--Schmidt

Files:

- `DavisKahan/Experimental/Scratch/RectangularHilbertSchmidt/RealDescent.lean`
- `DavisKahan/Experimental/Scratch/RectangularHilbertSchmidt/All.lean`

The already-present complex tensor construction is reused from:

- `DavisKahan/Experimental/MathAhead/HiddenFoundations/HilbertSchmidtComplexFamily.lean`

The new mathematical step is completeness over real Hilbert spaces.  A complex
Hilbert--Schmidt limit of complexified real operators is shown to preserve the
real copy, then descended by `realPartOperator`.  This supplies a concrete
`hilbertSchmidtReal` rectangular family.

Do not replace the generic `RCLike` production declaration immediately.  First
compile the real and complex families independently.  Then choose one of these
promotion strategies:

1. specialize the production API to the two actual scalar fields used by the
   source-facing theorems;
2. add a scalar-dispatch class with instances for `Real` and `Complex`;
3. generalize the tensor representation to arbitrary `RCLike` and retain the
   current generic declaration.

### Assumed names likely needing repair

- `ContinuousLinearMap.apply`
- `Metric.tendsto_atTop`
- `tendsto_nhds_unique`
- `ContinuousLinearMap.continuous`
- `RealComplexification.ofReal.norm_map`
- `ClosedOperatorComplexification.continuous_im`
- `ClosedOperatorComplexification.norm_re_le`

### Names verified in this repository

- `RealComplexification.complexify`
- `RealComplexification.complexify_ofReal`
- `RealComplexification.complexify_add`
- `RealComplexification.complexify_sub`
- `isPaperHilbertSchmidt_complexify_iff`
- `paperHilbertSchmidtNorm_complexify`
- `opNorm_le_paperHilbertSchmidtNorm`
- `HiddenFoundations.paperHilbertSchmidt_complete`
- `HiddenFoundations.isPaperHilbertSchmidt_add`
- `HiddenFoundations.paperHilbertSchmidtNorm_add_le`

## Lane B: free-beam smooth Green core

Files:

- `DavisKahan/Experimental/Scratch/FreeBeam/SmoothGreenIdentity.lean`
- `DavisKahan/Experimental/Scratch/FreeBeam/All.lean`

The file proves the fourth-order Green formula and the free-boundary energy
identity before any Sobolev completion is chosen.  It should be compiled and
then used as the boundary calculation underlying the concrete interval-domain
construction.

This lane does not claim to construct the closed self-adjoint operator.  It
closes the classical integration-by-parts mathematics needed for symmetry and
positivity on a smooth core.

### Assumed names likely needing repair

- `intervalIntegral.integral_eq_sub_of_hasDerivAt`
- `intervalIntegral.integral_sub`
- `intervalIntegral.integral_nonneg`
- `Continuous.intervalIntegrable`
- `HasDerivAt.mul`
- `Continuous.pow`

## Confidence

- `realPartOperator`: probably complete.
- `complexify_realPartOperator_eq`: probably complete.
- `paperHilbertSchmidt_complete_real`: mathematically complete; topology and
  evaluation-map spellings are compiler-facing.
- `hilbertSchmidtReal`: mathematically complete once the previous theorem
  elaborates.
- `integral_green_formula`: complete.
- `integral_free_green_symmetry`: complete.
- `integral_free_energy`: complete.
- `integral_free_energy_nonneg`: probably complete; interval orientation may
  require a different integral nonnegativity lemma.

## Divergences

- The rectangular family draft is split into real and complex implementations,
  rather than pretending an arbitrary abstract `RCLike` field has already been
  dispatched to one of them.
- The free-beam draft proves the smooth-core Green and positivity identities;
  it does not yet supply endpoint traces on `H^4`, graph closedness, compact
  embedding, or self-adjointness.

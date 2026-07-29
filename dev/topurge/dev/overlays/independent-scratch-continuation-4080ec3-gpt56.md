# Independent scratch continuation on `4080ec3`

This package continues the isolated scratch work without touching the active
`General.lean`, `ExactSinTheta`, Circle Riesz, continuation, or polar lanes.
It is intended to be applied after
`aiq_dkps_independent_scratch_lanes_4080ec3_gpt56_20260723.zip`.

## Contents

### Generic ideal Banach space

`DavisKahan/Experimental/Scratch/IdealBanach/Basic.lean` packages the members
of any `RectangularSymmetricIdealFamily` as a fresh normed type whose norm is
the family gauge.  It constructs:

- the ideal-member submodule;
- a bundled `IdealOperator` type;
- additive and scalar structures;
- a normed additive group and normed space;
- completeness directly from `gauge_complete`;
- a contractive forgetful continuous linear map to bounded operators;
- commutation of that map with Bochner integration;
- membership and gauge bounds for ideal-norm Bochner integrals.

This removes the need to re-prove Banach-space and integration closure for
Hilbert--Schmidt, trace, Schatten, and Ky Fan families separately.

### Hilbert--Schmidt Bochner layer

`RectangularHilbertSchmidt/BochnerIntegral.lean` specializes the generic
construction to the completed complex and real Hilbert--Schmidt families.  It
provides ideal membership and the sharp Minkowski estimate for both scalars,
in bundled and raw-field forms.

The remaining Sylvester-specific task is to prove that the Fourier or Laplace
orbit is measurable and integrable in the Hilbert--Schmidt norm.  Once that is
available, the integral membership and norm estimate are immediate applications
of this file.

### Complex free-beam smooth core

`FreeBeam/ComplexGreenIdentity.lean` proves the Hermitian fourth-order Green
identity and positivity formula for complex-valued smooth data.  It is the
correct scalar version for the eventual complex Hilbert-space operator.

`FreeBeam/SmoothKernel.lean` proves, for both real and complex data, that a
smooth free-end solution of `u'''' = 0` is affine.  Thus the smooth zero-mode
space is contained in the expected two-parameter affine family.  This is the
kernel calculation needed to identify the first positive eigenvalue as the
third eigenvalue after the Sobolev realization is constructed.

## Lemma ledger

### Confident declarations

- `RectangularSymmetricIdealFamily.zero_mem`
- `RectangularSymmetricIdealFamily.add_mem`
- `RectangularSymmetricIdealFamily.smul_mem`
- `RectangularSymmetricIdealFamily.gauge_nonneg`
- `RectangularSymmetricIdealFamily.gauge_zero`
- `RectangularSymmetricIdealFamily.gauge_eq_zero`
- `RectangularSymmetricIdealFamily.gauge_add_le`
- `RectangularSymmetricIdealFamily.gauge_smul`
- `RectangularSymmetricIdealFamily.opNorm_le_gauge`
- `RectangularSymmetricIdealFamily.gauge_complete`
- `NormedAddCommGroup.ofCore`
- `NormedSpace.ofCore`
- `Metric.complete_of_cauchySeq_tendsto`
- `Metric.cauchySeq_iff`
- `ContinuousLinearMap.integral_comp_comm`
- `MeasureTheory.norm_integral_le_integral_norm`
- `intervalIntegral.integral_eq_sub_of_hasDerivAt`
- `intervalIntegral.integral_sub`
- `Complex.normSq_eq_conj_mul_self`
- `Complex.reCLM`
- `Complex.normSq_nonneg`
- `paperHilbertSchmidtNorm`
- `IsPaperHilbertSchmidt`
- `HiddenFoundations.hilbertSchmidtComplex`
- `Scratch.RectangularHilbertSchmidt.hilbertSchmidtReal`

### Likely spelling or signature repairs

- `Complex.conjCLE.toContinuousLinearMap.hasFDerivAt`
  - assumed to be the derivative of conjugation as a real continuous linear map.
- `Complex.conjCLE_apply`
  - simplification theorem for the conjugation equivalence.
- `Complex.continuous_conj`
  - may be exposed as `continuous_conj` or through the continuous equivalence.
- `Continuous.normSq`
  - assumed continuity of `x ↦ Complex.normSq (f x)`.
- `Continuous.ofReal`
  - assumed continuity after coercion from real to complex.
- `intervalIntegral.integral_const`
  - used through simplification in the generic affine lemma.
- Namespace inference for `IdealOperator.mem`, `norm_def`, and `toOp_sub`
  may require explicit arguments because the family is an indexed structure.
- `norm_integral_le_integral_norm` may need its `μ` argument or namespace made
  explicit.

## Confidence

- `IdealOperator`, algebraic instances: **probably-complete**.
- `IdealOperator.core`: **probably-complete**.
- `IdealOperator.instCompleteSpace`: **complete mathematics; likely coercion repair**.
- `toOp_integral`, `mem_integral_toOp`, gauge estimate: **probably-complete**.
- Hilbert--Schmidt specializations: **probably-complete once generic layer compiles**.
- Complex Green formula and free symmetry: **complete mathematics; derivative API repair likely**.
- Complex energy and positivity: **complete mathematics; real-part/integral spelling repair likely**.
- Real and complex smooth-kernel affine classification: **probably-complete**.

## Divergences and scope limits

- The integral theorem assumes integrability in the ideal norm.  Raw
  operator-norm integrability is weaker and is not enough by itself.
- The raw-field theorem therefore asks for an integrable bundled lift.  A later
  orbit-specific theorem must establish that lift.
- The Hilbert--Schmidt files produce separate real and complex families.  They
  do not pretend that an arbitrary abstract `RCLike` implementation is
  definitionally one of those two scalar types.
- The free-beam results are smooth-core calculations.  They do not construct
  the completed Sobolev domain, prove closedness, characterize the adjoint
  domain, or establish self-adjointness.
- The affine result proves containment of smooth zero modes in the affine
  family.  The eventual operator-domain proof must also show that both affine
  modes belong to the domain and are linearly independent there.

## Suggested compiler order

```bash
lake env lean \
  DavisKahan/Experimental/Scratch/IdealBanach/Basic.lean

lake env lean \
  DavisKahan/Experimental/Scratch/RectangularHilbertSchmidt/BochnerIntegral.lean

lake env lean \
  DavisKahan/Experimental/Scratch/FreeBeam/ComplexGreenIdentity.lean

lake env lean \
  DavisKahan/Experimental/Scratch/FreeBeam/SmoothKernel.lean

lake env lean DavisKahan/Experimental/Scratch/All.lean
```

Promote the generic ideal type first.  Then the Hilbert--Schmidt integral file
should mostly become applications.  Keep the free-beam declarations in the
smooth-core namespace until the Sobolev trace and operator-domain structures
exist.

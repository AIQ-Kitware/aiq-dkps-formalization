# Shared hard-foundation scratch campaign

Base commit: `dfd9d37ebc86421eea50ee79e71e2420d507878d`

This overlay is additive under
`DavisKahan/Experimental/Scratch/SharedFoundations`.  It does not edit the
nonacute polar files reserved for the active Opus campaign and does not alter
the ordinary dependency graph.

The files are full mathematical proof drafts prepared without a Lean
executable.  They have passed static import, manifest, JSON, and proof-escape
checks, but have not been elaborated.

## Purpose

The campaign develops foundations shared by several remaining tracks:

* old and rectangular symmetric-ideal gauge transport;
* operator modulus and polar-factor transport;
* directed reflection/double-angle identities;
* isometric range projections and Ritz residual algebra;
* residual control of reflection defects;
* compatible Banach operator norms and corrected Theorem 5.1;
* genuine bounded spectral selections;
* exact Section 7 source wrappers.

It deliberately does not duplicate the existing approximation-number library.

## Modules and intended promotions

### `Ideal/TwoWayFactorization.lean`

Proves membership and gauge transport when two operators factor through one
another by contractions.  This supports polar partial isometries, reflections,
projection blocks, zero extensions, and rectangular compression arguments.

Candidate consumers:

* `SinTheta/General.lean`
* `DoubleAngle.lean`
* Section 4 ideal promotion
* rectangular Hilbert--Schmidt and Schatten families

### `Ideal/OperatorAbsoluteValueComplex.lean`

Connects the local `ForMathlib.operatorAbs` to Spectra's bounded polar
decomposition and proves, for the older square `SymmetricNormIdeal`, that
membership and gauge are preserved by the operator modulus.  The proof uses
only the two contraction factorizations

`T = U |T|` and `|T| = U* T`.

This is intended to replace the operator-modulus leaf in
`SinTheta/General.lean` for the complex case.  Real descent remains separate.

### `Ideal/ReflectionTransport.lean`

Introduces the directed block

`Wᗮ.starProjection ∘L U.starProjection`

and proves its exact reflection equivalence to `sinTwoAngleOperator` for the
mirror subspace.  This is the correct ideal-valued object.

The existing leaf
`SymmetricNormIdeal.sinAngle_reflected_mem_gauge_eq` uses the full absolute
projector difference.  That statement is not generally compatible with
arbitrary ideal gauges: in the two-line finite-dimensional model the full
sine has two copies of the nonzero singular value, while the directed block
has one.  Operator norms agree, but trace and Hilbert--Schmidt gauges do not.
The scratch theorem is therefore a corrected directed statement, not a proof
of the current leaf.

### `Residual/IsometricRangeProjection.lean`

Proves:

* an isometric bounded embedding has closed range;
* its range has an orthogonal projection;
* the range projection equals `X X*`;
* `X* X = I`;
* the complementary projection annihilates `X`;
* `X` and `X*` are contractions.

These facts are shared by generalized tangent, Section 6 residual theory,
Section 7 reflection residuals, and finite-rank comparisons.

### `Residual/TrialResidual.lean`

Defines the canonical subspace trial residual, proves the Ritz-difference
identity, and shows that the exact-range cross block factors through any
residual:

`P_rangeᗮ A P_range = (P_rangeᗮ (A X - X M)) X*`.

It supplies operator-norm and rectangular ideal-gauge bounds.

### `Residual/IsometricRitzPair.lean`

Packages `M = X* A X` and proves Galerkin orthogonality:

* `X* residual = 0`;
* `P_range residual = 0`;
* `P_rangeᗮ residual = residual`;
* the cross block is exactly `residual X*`.

This should be reused by the generalized tangent and Ritz campaigns rather
than reproved locally.

### `Residual/ReflectionDefect.lean`

Combines the existing sharp off-diagonal reflection estimate with the trial
residual factorization to prove

`norm (J A J - A) <= 2 * norm (A X - X M)`

for a complex self-adjoint ambient operator and an isometric trial map.  This
is a direct candidate for the complex form of
`reflectionDefect_range_le_residual`.

### `Residual/ReflectionDefectIdeal.lean`

At the basic rectangular-family abstraction, proves ideal membership and the
robust bound

`gauge (J A J - A) <= 4 * gauge residual`.

The factor four follows from triangle plus adjoint invariance.  A sharp factor
two for every symmetric gauge needs a stronger off-diagonal block theorem and
should not be smuggled into the minimal family interface.

### `Sylvester/BoundedLeftInverse.lean`

Introduces explicit quantitative bounded-left-inverse data.  This is the
correct Banach-space foundation: a lower bound alone does not imply that the
closed range of an operator between arbitrary Banach spaces is complemented.

### `Sylvester/CompatibleNorm.lean`

Derives full two-sided scaling from the contraction compatibility property and
proves the Theorem 5.1 inequality under an explicit bounded left inverse of
`A`.

The current frontier theorem assumes only

`(gamma + delta) * norm y <= norm (A y)`.

For arbitrary Banach spaces this supplies injectivity and closed range, but no
bounded projection onto the range and therefore no bounded left inverse.  The
source statement needs one of the following repairs:

* `A` invertible;
* an explicit bounded left inverse;
* complemented range with a quantitative projection;
* a Hilbert/self-adjoint specialization from which invertibility follows.

Do not promote the scratch proof by silently retaining the weaker current
hypothesis.

### `Spectral/BoundedSelection.lean`

Packages the genuine bounded complex spectral subspace together with:

* self-adjointness;
* measurability;
* the PVM projection;
* equality with the star projection;
* the reduction theorem.

This is an audited replacement shape for the malformed scalar-generic
`spectralSubspace` surface in `SinTheta/General.lean`, which currently lacks
both self-adjointness and measurability inputs.

### `Source/Section7Wrappers.lean`

Provides an exact wrapper for the compiled sine-double-angle theorem and a
corrected tangent wrapper.  The current frontier tangent conclusion omits the
positive denominator

`1 - 2 * directedGap U V ^ 2`.

The denominator-free statement is not an exact promotion of the compiled
result and should be audited against the source before modification.

## Suggested compile order

```bash
lake env lean DavisKahan/Experimental/Scratch/SharedFoundations/Ideal/TwoWayFactorization.lean
lake env lean DavisKahan/Experimental/Scratch/SharedFoundations/Ideal/OperatorAbsoluteValueComplex.lean
lake env lean DavisKahan/Experimental/Scratch/SharedFoundations/Ideal/ReflectionTransport.lean
lake env lean DavisKahan/Experimental/Scratch/SharedFoundations/Residual/IsometricRangeProjection.lean
lake env lean DavisKahan/Experimental/Scratch/SharedFoundations/Residual/TrialResidual.lean
lake env lean DavisKahan/Experimental/Scratch/SharedFoundations/Residual/IsometricRitzPair.lean
lake env lean DavisKahan/Experimental/Scratch/SharedFoundations/Residual/ReflectionDefect.lean
lake env lean DavisKahan/Experimental/Scratch/SharedFoundations/Residual/ReflectionDefectIdeal.lean
lake env lean DavisKahan/Experimental/Scratch/SharedFoundations/Sylvester/BoundedLeftInverse.lean
lake env lean DavisKahan/Experimental/Scratch/SharedFoundations/Sylvester/CompatibleNorm.lean
lake env lean DavisKahan/Experimental/Scratch/SharedFoundations/Spectral/BoundedSelection.lean
lake env lean DavisKahan/Experimental/Scratch/SharedFoundations/Source/Section7Wrappers.lean
lake env lean DavisKahan/Experimental/Scratch/SharedFoundations/All.lean
```

## Likely mechanical repairs

* exact names of projection norm lemmas and three-factor norm bounds;
* simplification of `letI`-dependent range projections;
* coercions between `LinearMap.range`, `Set.range`, and subtypes;
* `ContinuousLinearMap.id` norm simplification;
* scalar normalization in `CompatibleCrossOperatorNorm.comp_le_mul`;
* exact namespace of spectral-projection commutation;
* adjoint composition normal forms;
* the `reflectionDefectIdeal` proof may prefer rewriting the second block by
  `offdiag_adjoint` before membership bookkeeping.

These should be repaired without changing the mathematical statements.

## Promotion discipline

Promote coherent pieces independently.  In particular:

1. range projection and Ritz residual algebra can land before any source
   theorem;
2. the complex reflection-residual norm theorem can close its leaf after
   scalar-generic scope is audited;
3. the operator-modulus result can close the complex old-ideal leaf;
4. the Section 7 sine wrapper can be promoted immediately once it compiles;
5. statement repairs for the full-sine ideal leaf, Theorem 5.1, spectral
   selection, and tangent wrapper require explicit review before editing the
   frontier.

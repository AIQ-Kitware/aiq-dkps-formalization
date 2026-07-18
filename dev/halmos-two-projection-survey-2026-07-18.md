# Halmos two-projection implementation survey — 2026-07-18

## Scope

This note records the sources used for the operator-valued Halmos
implementation in
`DavisKahan/Experimental/InfiniteDimensional/SpectraBridge/HalmosTwoProjections.lean`.
The implementation deliberately avoids approximation numbers, Ky Fan gauges,
and compact-operator ideal infrastructure.

## Mathematical source

The local distilled transcription
`prose/distilled_literature/Halmos1969_two_subspaces.tex` records the standard
four elementary summands and the generic block

```text
P = [[1, 0], [0, 0]],
Q = [[C², CS], [CS, S²]],
C² + S² = 1.
```

For the formal development, the scalar direct-integral realization is not
made a second primitive foundation.  The theorem is expressed through the
single positive contraction `C` and its commuting sine square.  A direct
integral is then a spectral representation of `C`, available when a later
argument genuinely needs scalar fibers.

## Pinned Mathlib APIs

The repository pins Mathlib revision
`3dffaf2f18b47d11948f6390838ea6f2ae662aaf`.

### `Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`

Used for:

- `Submodule.HasOrthogonalProjection`;
- `Submodule.starProjection`;
- `Submodule.starProjection_eq_self_iff`;
- `Submodule.starProjection_apply_eq_zero_iff`;
- `Submodule.starProjection_orthogonal'`;
- `Submodule.sup_orthogonal_of_hasOrthogonalProjection`;
- projection Pythagoras and orthogonality membership.

### `Mathlib/Analysis/InnerProductSpace/Projection/Submodule.lean`

Used for orthogonal-complement closure and the decomposition
`K ⊔ Kᗮ = ⊤` once `K` admits an orthogonal projection.

### Complete and closed subspace APIs

A complemented subspace is first shown complete by the repository-local
`Submodule.isComplete_coe_of_hasOrthogonalProjection`.  Its intersection is
then handled through `IsComplete.isClosed`, `IsClosed.inter`, and
`IsClosed.completeSpace_coe`.  This avoids relying on a nonexistent
`IsComplete.inter` declaration in the pinned Mathlib revision.

### `Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Abs.lean`

Used for:

- the positive operator modulus `CFC.abs`;
- `CFC.commute_abs_self` for normal operators;
- the square identity `|T|² = T⋆T` through the existing Spectra bridge.

### `Mathlib/Analysis/InnerProductSpace/Adjoint.lean`

Used for self-adjoint projection identities, unitary adjoint inverses, and
quadratic-form manipulation.

### `Mathlib/Analysis/InnerProductSpace/Rayleigh.lean`

Inspected for the norm/quadratic-form interface.  The final minimality proof
uses a direct pointwise operator-norm estimate instead of an eigenvector or
compactness argument.

## Repository-local APIs

### `SpectraBridge/DirectRotation.lean`

Provides:

- the canonical intertwiner `QP + QᗮPᗮ`;
- its positive modulus and inverse unit in the acute regime;
- the polar-factor direct rotation;
- projection and complementary-projection intertwining;
- unitary identities.

### `ForMathlib/Analysis/InnerProductSpace/CoerciveUnit.lean`

Provides `ContinuousLinearMap.norm_apply_sq_le_of_positive`, the elementary
positive-operator Cauchy--Schwarz estimate used to convert an inverse norm
bound into the exact cosine coercivity required by the minimization theorem.

### `ForMathlib/Analysis/InnerProductSpace/ReducingSubspace.lean`

Provides the reusable `ContinuousLinearMap.Reduces` interface and the theorem
that an invariant subspace of a symmetric operator is reducing.  The Halmos
generic remainder is registered as reducing both source and target
projections, so later functional-calculus arguments can work entirely on that
block.

## Resulting architecture

The implementation separates three layers:

1. **Geometric decomposition:** common, source-defect, target-defect,
   exterior, and generic subspaces.
2. **Operator Halmos model:** positive commuting cosine/sine squares and
   their exact projection-polynomial identities.
3. **Direct rotation:** reuse the accepted Hermitian-part and uniqueness
   theorems, prove the diagonal cosine compressions, and derive operator-norm
   extremality without duplicating the direct-rotation foundation.

This is intended to be reused by later sine/cosine spectral mapping,
double-angle, graph-subspace, continuation, and equality-case work.


## Accepted-base integration

The authoritative base for this attempt is
`aiq-dkps-formalization-source-2026-07-18T130536-5-2db660147904.tar.gz`.
That base already contains the proof of acute direct-rotation uniqueness and
the Hermitian-part identity.  The Halmos module therefore imports only the
lower `DirectRotation` layer, while `DirectRotationSquare` imports the Halmos
module and reuses its cosine algebra to prove minimality.  This avoids an
import cycle and avoids maintaining duplicate versions of the accepted
quadratic-form arguments.

# Targeted mathematical repair after the Experimental build audit

Base commit: `d5e54a708c014d97c4124036d332c6d7caa2a10e`.

This repair is deliberately theorem-by-theorem. It does not replace the older
infinite-dimensional source tree with compatibility stubs.

## Spectral projection root

`Core/SpectralProjection.lean` imported a vendored module that has never
existed. The bounded complex self-adjoint projection layer is nevertheless
available from the actual Spectra PVM and bounded-calculus modules. The genuine
PVM, measurable projection, selected range, star-projection identity, and
orthogonal-projection predicate are moved to the dependency root. The later
contour-identification module imports this core instead of defining it again.

The real route remains the existing qualified complexification/restriction
bridge. No scalar-generic continuous-functional-calculus facade is introduced.

## Finite versus infinite dependencies

The finite `Generalized` module contained two theorems whose variables are
complete complex Hilbert spaces and whose proofs use the full common-contour
continuation witness. They were mathematically sound but architecturally
misplaced. Their statements are preserved under the same namespace in
`ContinuationWitnessGraph.lean`; finite residual theory no longer imports
the contour/Riesz hierarchy.

This is the key correction to the supplied build cascade: the cascade was not
proof that every dependent infinite module should be retired. It arose because
two infinite endpoint wrappers were imported through the finite aggregate.

## Direct rotation

The squared-displacement result remains the field-generic Section 4 endpoint:
for every unitary carrying `U` onto `V`, the direct rotation weakly minimizes
all Ky Fan sums and therefore every UI norm of
`(I-R)^*(I-R)`.

The historical real full-displacement theorem under a largest-angle bound of
`pi / 3` is not valid for arbitrary competitors. In two equal principal-angle
planes, a competitor may rotate the multiplicity space so that its two
rotation angles become `0` and `2 theta`. Its trace displacement is
`4 sin theta`, whereas the plane-by-plane direct rotation has trace
displacement `8 sin (theta / 2)`; for `0 < theta < pi / 3`, the former is
strictly smaller. This is a multiplicity-mixing obstruction, not a field issue.

The valid replacement is Davis--Kahan restricted-displacement minimality:
for every UI norm and without an angle restriction,

`N ((I - R) P_U) <= N ((I - W) P_U)`.

The full positive displacement-square theorem, operator-norm consequence, and
orthonormal-basis energy consequence are retained.

## Compiler boundary

The remaining active roots are:

- `DavisKahan/FiniteDimensional/DirectRotation/PrincipalPlanes.lean`;
- `DavisKahan/FiniteDimensional/DirectRotation/Majorization.lean`;
- `DavisKahan/Experimental/FiniteDimensional/Generalized.lean`;
- `DavisKahan/Experimental/FiniteDimensional/Sharpness.lean`.

Their mathematics is retained as candidate code. The compiler agent should
repair elaboration, names, coercions, and tactic details rather than restoring
the false full-displacement endpoint or the misplaced finite-to-infinite
import.

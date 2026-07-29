# Finite coordinate tangent singular values and ordered residual split

Base commit: `2fcfa654152f2e8803ac85b3ab340374fd3d771d`.

## Mathematical construction

For an isometric trial map `X : F -> E` and exact subspace `U`, set

- `S = P_(U perp) X`,
- `C = P_U X`,
- `C0 = |C| = (C star C)^(1/2)`,
- `T = S C0^+`.

The right singular basis of `S` diagonalizes `S star S`.  The identity
`C star C + S star S = I` therefore shows that the same basis diagonalizes
`C0`, with eigenvalues `sqrt (1 - sigma_i^2)`.  Under transversality these
numbers are positive, so the Moore--Penrose inverse acts by their reciprocals.
Consequently

`T star T v_i = sigma_i^2 / (1 - sigma_i^2) v_i`,

and the singular values of `T` are

`sigma_i / sqrt (1 - sigma_i^2) = tan (arcsin sigma_i)`.

The scalar quotient is proved antitone along the decreasing singular-value
sequence, so the diagonal comparison has the canonical sorted order and the
zero-padding convention is explicit.

## Ordered residual theorem

For a nonzero finite coordinate space, an `OrderedGap M top A Uperp delta`
implies the paper interval hypothesis by choosing

- `alpha` as the largest eigenvalue of `M`,
- `beta = -norm M`.

The ordered gap places the unwanted exact spectrum above `alpha + delta`.
The accepted paper-exact Ky Fan witness theorem then yields the all-UI bound
for the canonical tangent.  The zero-dimensional coordinate case is handled
separately.

The pointwise theorem is derived from the operator-norm residual theorem and
the exact factorization `S = T C0`.  This repairs the historical proof, whose
last inequality silently treated an arbitrary vector as normalized.

## Dependency split

Completed coordinate declarations now live in
`DavisKahan/Experimental/FiniteDimensional/Residual/AngleEmbeddings.lean`.
`CanonicalEmbedding.lean` and `Generalized.lean` import that module directly.

The historical `TanTheta/GraphOperator.lean` file retains only the unresolved
ambient graph/Riccati perturbation family.  No declaration was deleted.  This
keeps speculative ambient geometry from preventing elaboration of the
coordinate tangent layer while preserving the old theorem statements for a
later dedicated batch.

## Compiler focus

The likely repair seams are the diagonal Gram calculation, scalar coercions in
the reciprocal cosine factors, and the exact syntax for rewriting bundled
singular-value sequences.  The mathematical route and theorem statements
should be preserved.

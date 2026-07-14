# Exact infinite-dimensional `sin Θ` scaffold

This subtree is an additive experimental dependency graph for the complete
Davis--Kahan `sin Θ` theorem, including the generalized non-isometric trial-map
statement and the unbounded self-adjoint extension.

The files are ordered by dependency:

1. `RectangularIdeals.lean`
2. `BoundedSylvester.lean`
3. `BoundedSpectralBridge.lean`
4. `FrameFactorization.lean`
5. `BoundedSinTheta.lean`
6. `UnboundedCore.lean`
7. `ApproximationNumbers.lean`
8. `UnboundedSylvester.lean`
9. `UnboundedSinTheta.lean`

The scaffold intentionally exposes many small proof obligations.  It should not
be imported by the supported finite theory until the relevant declarations are
implemented and audited.

The fastest useful tranche is the bounded chain through
`generalizedSinTheta_bounded`.  The unbounded chain should remain downstream of
a stable partial-operator, adjoint, and spectral-resolution implementation.

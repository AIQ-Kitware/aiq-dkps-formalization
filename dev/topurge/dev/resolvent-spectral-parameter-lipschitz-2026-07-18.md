# Resolvent spectral-parameter Lipschitz step

Date: 2026-07-18
Base: `4f1f3a91d38e`

## Base audit

The authoritative archive contains the accepted Halmos/minimality,
close-projection transport, quantitative affine-path resolvent continuity,
and complex CFC resolvent-distance commits.  It also contains the later
bounded-perturbation sine-theta and Stone-generator work.  This change does
not modify any file owned by those later workstreams.

## Result

For the repository convention

`R_A(z) = (A - z I)⁻¹`,

the first resolvent identity gives

`R_A(z) - R_A(w) = (z-w) R_A(z) R_A(w)`.

Taking norms yields

`‖R_A(z)-R_A(w)‖ ≤ ‖z-w‖ ‖R_A(z)‖ ‖R_A(w)‖`.

A uniform bound `‖R_A(z)‖ ≤ M` on a set therefore gives an `M²` Lipschitz
constant.  For a complex self-adjoint operator, the accepted CFC theorem
supplies `M = δ⁻¹` from a common distance `δ` to the real spectrum, so the
resolvent is `δ⁻²`-Lipschitz on any uniformly separated contour image.

## Consequence for continuation

The contour-integrand proof now has both required continuity estimates:

1. variation in the operator/path parameter from the second resolvent identity;
2. variation in the contour/spectral parameter from the first resolvent identity.

The next step is a proof-carrying piecewise-C1 closed path and the normalized
curve integral.  Because this repository defines the resolvent as
`(A-zI)⁻¹`, the standard positively oriented Riesz formula carries a minus
sign relative to the usual `(zI-A)⁻¹` convention.

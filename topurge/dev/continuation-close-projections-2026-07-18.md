# Close projections and Section 8 continuation

Date: 2026-07-18

## Result implemented

`DavisKahan/Experimental/InfiniteDimensional/SinTheta/Continuation.lean` now
proves the complex-Hilbert-space theorem
`range_equiv_of_projection_norm_lt_one`.  Given abstract orthogonal
projections `P,Q` with `||P-Q|| < 1`, it constructs a global unitary operator
`W` satisfying `W comp P = Q comp W`.

## Construction

For a bounded operator `P`, define its fixed-point subspace as
`(P - 1).ker`.  This presentation is automatically closed.  When `P` is
idempotent and symmetric, a direct inner-product calculation identifies `P`
with the canonical orthogonal projection onto that fixed-point subspace:

* idempotence puts `P x` in the fixed-point subspace;
* symmetry shows `x - P x` is orthogonal to every fixed point.

Applying this to both projections rewrites their subspace gap as exactly
`||P-Q||`.  The strict norm bound therefore gives an acute pair, and the
completed complex direct rotation supplies the required norm-preserving,
surjective intertwiner.

## Why this is the next Section 8 rung

The local geometry is no longer a blocker.  Once a Riesz projection path is
proved norm-continuous, nearby path values can be related by this theorem.
A compactness/subdivision argument can then compose the local unitaries and
transport the selected spectral component from `t=0` to `t=1`.

## Remaining analytic dependency

The current resolvent module still treats the following as provisional:

* `ContourSeparatesSpectrum`;
* `rieszProjection`;
* `rieszProjection_eq_spectralProjection`;
* `continuous_rieszProjection_path`.

The next substantial task is to replace the first two with proof-carrying
contour/integral definitions and prove a local quantitative continuity
estimate from the second resolvent identity.

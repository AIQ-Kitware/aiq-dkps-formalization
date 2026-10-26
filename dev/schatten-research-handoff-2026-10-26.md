# Schatten transport research checkpoint — 26 October 2026

Manuscript and visualization updates are assigned separately. This record
describes new mathematics and the exact next proof obligations.

## All-rank real nuclear canonical-value criterion

`RealNuclearOptimality.lean` proves
`RealTransport.realNuclearMatchingMinimum_eq_canonical_iff`. For any finite
labelled family `theta` in `[0, pi/2]`, its exact real nuclear matching
minimum equals `sum_i 4 sin(theta_i/2)` if and only if every angle is at
most `pi/3` and at most one labelled angle is strictly positive. In
particular, two equal positive angles still exclude the canonical value:
multiplicities are counted, not collapsed.

`realTransportPowerMinimum_one_eq_canonical_iff` transfers this statement
to the literal unrestricted ambient transport minimum for any equal-rank
subspaces of any finite-dimensional real inner-product space. Its right
side ranges over the original `Fin (finrank K)` angle labels. Zero angles,
right angles, rank zero, and common ambient directions are included.
There is no determinant restriction or prescribed-block competitor
restriction. The formal conclusion identifies the optimum value with
the canonical spectral sum; it does not yet state an iff for the named
real completed direct-rotation operator.

The proof uses two independently checkable facts. First, an identity
matching bounds the optimum by the sum of singleton minima. Equality
with the canonical sum forces each singleton to use its canonical
branch, equivalently `theta <= pi/3`. Second, introducing one edge gives
a strict saving over two canonical rotations whenever both angles are
positive (`RealNuclearExchange`). Conversely, with at most one positive
angle, every edge has a zero endpoint and every matching has the same
canonical cost. Zero-label removal in the ambient sum is explicit.

The module also supplies nuclear matching attainment, the bound by every
matching, and the exact cost change on inserting one edge. The two
existing nuclear matching definitions are exposed to downstream proofs;
their definitions and hypotheses have not changed.

Focused build: `lake build
DavisKahan.FiniteDimensional.DirectRotation.RealNuclearOptimality` passed
(7,308 jobs), after the required cache fetch. Full aggregate validation
will be recorded after it finishes. No historical-priority claim is made:
this is an exact consequence of the already compiled unrestricted
matching theorem and scalar exchange, extending the earlier model
four-dimensional canonical criterion to all ambient ranks.

## Next mathematical target

Determine precisely when the real nuclear minimum equals
`sum_i 2 sin(theta_i)`, the complex nuclear spectral value. Independent
scalar reasoning predicts that a positive two-angle nuclear edge has
zero field penalty exactly when its two angles agree, and that a
singleton has zero field penalty only at zero or a right angle. Thus
every strictly acute positive angle should need even multiplicity;
right-angle multiplicity should be unrestricted. Establish the scalar
equality cases, pass them through the matching minimum, and construct
the required within-level involutions before asserting the parity iff.
The unrestricted complex nuclear endpoint must also be connected to its
accepted-angle value before calling the comparison a full field theorem.

The two sorted-sum formula, its finite matching normalization/induction,
the uniform field gap, and the operator-ideal extension remain unproved
by this checkpoint. Scalar submodularity alone is insufficient for any
of those conclusions.

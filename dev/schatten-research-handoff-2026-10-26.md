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
(7,308 jobs), after the required cache fetch. The full default build then passed (21,037 jobs), and the theorem
was committed immediately as `fb0298d7d`. No historical-priority claim is made:
this is an exact consequence of the already compiled unrestricted
matching theorem and scalar exchange, extending the earlier model
four-dimensional canonical criterion to all ambient ranks.

## Exact real nuclear multiplicity obstruction

`RealNuclearFieldEquality.lean` now proves
`realTransportPowerMinimum_one_eq_sine_sum_iff_even_multiplicities`.
For every finite real equal-rank pair, its literal unrestricted nuclear
minimum equals `sum_i 2 sin(theta_i)` if and only if every angle strictly
between zero and `pi/2` has even multiplicity in the original accepted
principal-angle labels. Zero and right-angle multiplicities are arbitrary.
This is an equality of the actual ambient minimum, not merely a lower
bound over prescribed blocks.

`nuclear_singleton_eq_sine_iff` and `nuclear_pair_eq_sine_sum_iff`
prove the exact scalar equality cases. Every matching dominates the sine
sum. `realNuclearMatchingCost_eq_sine_sum_iff` classifies every matching
attaining that lower value: its involution must preserve each angle level
and have no fixed point on any strictly acute positive level. Passing to
an attaining matching makes this an iff for the matching minimum.
An odd acute multiplicity forces a strictly positive gap, as proved by
`sine_sum_lt_realNuclearMatchingMinimum_iff_odd_multiplicity`.

The necessity and construction use the classical finite-set equivalence
between even cardinality and a fixed-point-free involution, now proved in
`ForTauCeti/Data/Fintype/Involution.lean`. This is reusable combinatorics,
not a separate novelty claim. The within-level pairings are assembled by
Mathlib's fiber equivalence; no order of the repeated labels is assumed.
The ambient transfer explicitly restores zero angles and proves that an
acute level's cardinality is unchanged by positive-label restriction.

The focused module build passed (7,312 jobs), after its cache fetch. An
independent exhaustive diagnostic checked all 1,287 multisets through
rank eight on the angle grid `{0, 0.1, 0.3, pi/3, pi/2}` using exact finite
matching enumeration (floating evaluation, tolerance `1e-10`). No parity
counterexample was found. This diagnostic is not the proof.

The unrestricted complex nuclear endpoint still needs to be connected
formally to its sine value before this can be advertised as a complete
real-versus-complex comparison. The algebraic parity obstruction itself
is compiled. The complete optimizer classification for the ambient real
problem is not inferred from a classification of attaining matchings.

## Next mathematical target

Close the complex nuclear endpoint by positive-exponent continuity and
existing all-exponent scalar-phase attainment. Then state the exact
real-versus-complex equality criterion for pairs with the same accepted
principal-angle data. Continue to distinguish historical priority from
formal verification. The primary 2001 predecessor is
[Bolotnikov--Li--Rodman](https://journals.uwyo.edu/index.php/ela/article/download/117/117/117):
Lemma 3.3 treats a special `p<2` example; Theorem 4.5 concerns Q-norms under
additional block hypotheses. That limited comparison does not establish
historical novelty of the present all-rank nuclear parity theorem.

The two sorted-sum formula, its finite matching normalization/induction,
the uniform field gap, and the operator-ideal extension remain unproved
by this checkpoint. Scalar submodularity alone is insufficient for any
of those conclusions. Manuscript and visualization files remain untouched.

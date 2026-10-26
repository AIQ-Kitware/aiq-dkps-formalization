# Schatten transport research checkpoint — 26 October 2026

Manuscript and visualization updates are assigned separately. This record
describes new mathematics and the exact next proof obligations. The target
is the journal research extension on exact real and complex transport,
not an addition to the frozen 29-result Davis--Kahan source denominator.

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

At this checkpoint the algebraic parity obstruction compiled first.
The subsequent endpoint and field-comparison theorems below now identify
the same sine sum with the unrestricted complex minimum. The complete optimizer classification for the ambient real
problem is not inferred from a classification of attaining matchings.

## Complex nuclear endpoint and a full comparison of the fields

`SchattenPhaseMinimum.continuousOn_phaseMinimum_exponent` proves
continuity of the compact scalar minimum for every positive exponent,
including vanishing displacement chords. `SchattenOptimalPhase.phaseMinimum_one`
computes its endpoint as `2 sin(theta)` on the entire physical interval.

`SchattenNuclearEndpoint.sum_sine_le_nuclear_transport_complex` passes
the unrestricted strict-exponent lower bound to one, using continuity
of both the scalar minimum and the literal singular-value power sum.
`exists_unitary_minimizing_nuclear_transport_principalAngles_complex`
then supplies an actual ambient complex unitary attaining the sine sum
and comparison with every ambient unitary transporter. Its hypotheses
are just a finite-dimensional complex inner-product space and equal-rank
subspaces. Zero, repeated and right angles, rank zero, and arbitrary
common ambient directions are included. It does not classify all nuclear
optimizers or claim a nuclear local-to-global theorem.

`NuclearFieldComparison.exists_complex_nuclear_minimum_with_real_parity_criterion`
compares actual finite real and complex transport problems with the same
accepted angle data. The source ranks agree and the angle lists agree
under the resulting finite-index cast; the ambient dimensions need not
agree. An actual complex minimizer has cost no greater than the literal
unrestricted real minimum. The two minima are equal exactly when every
strictly acute positive real angle has even multiplicity. This theorem
does not silently assume a principal-angle invariance theorem for a
specific implementation of complexification: equal accepted-angle data
are an explicit hypothesis.

Focused builds passed: `NuclearFieldComparison` (7,682 jobs), and
`SchattenNuclearCorrection` (7,392 jobs), each after the cache fetch.
The real parity checkpoint previously passed the full default build
(21,041 jobs) and was committed immediately as `3aa3faa1c`. The endpoint,
field comparison and rounding application then passed the full default
build (21,047 jobs), with warnings treated as errors, and were committed
immediately as `0a7738706`. The working tree was clean at that mathematical
checkpoint.

## Exact invariant-subspace rounding application

`SchattenNuclearCorrection.exists_nearest_nuclear_subspace_preserving_unitary_complex`
proves that, for any unitary `A` and prescribed subspace `K`, a nearest
unitary `V` with `V(K)=K` exists in the accepted nuclear norm. Its distance
from `A` is exactly twice the sum of the principal-angle sines between
`A(K)` and `K`, and it compares with every ambient unitary preserving
`K`. The transport-to-correction equivalence already established for
positive finite Schatten exponents is specialized to one. This is an
application consequence, not an independent historical-priority claim.
No experimental, physical-implementation or statistical guarantees are
inferred.

## Next mathematical targets and priority boundary

For `1<p<2`, investigate the analogous real-versus-complex equality
criterion: even multiplicities may be necessary precisely for strictly
supercritical acute levels, while subcritical, critical and right levels
may have unrestricted multiplicities. This remains an unproved proposed
extension. A useful missing lemma is the complete equality case for the
clipped real two-angle cost versus the sum of the complex scalar minima.
An independent diagnostic found no counterexample on 1,386 multisets
through rank six for `p` in `{1.2, 1.5, 1.8}`. Each exponent used angles
`{0, c/2, c, (c+pi/2)/2, pi/2}`, with `c=arccos((2-p)/p)`, numerical
scalar phase minimization and exact finite matching enumeration, at an
equality tolerance of `1e-8`. This supplies no proof of the conjecture.

The two sorted-sum formula, its finite matching normalization/induction,
the uniform field gap, and the operator-ideal extension remain unproved
by this checkpoint. Scalar submodularity alone is insufficient for any
of those conclusions. Complex nuclear all-optimizer classification also
remains open; it cannot be inferred merely by taking a limit of the
strict-exponent optimizer descriptions.

Continue to distinguish historical priority from formal verification.
The primary 2001 predecessor is
[Bolotnikov--Li--Rodman](https://journals.uwyo.edu/index.php/ela/article/download/117/117/117):
Lemma 3.3 treats a special `p<2` example; Theorem 4.5 concerns Q-norms under
additional block hypotheses. That limited comparison does not establish
historical novelty of the present all-rank nuclear parity theorem.
Manuscript and visualization files remain untouched.

## Exact next application lemma

To express the proved complex nuclear rounding distance as a sharp
commutator certificate, a useful next lemma is
`nuclear(P_K-P_L) = sum_i 2 sin(theta_i)` for equal-rank finite complex
subspaces, in the accepted norm and principal-angle APIs. With
`L=A(K)`, the operator identity
`P_L-P_K = (A*P_K-P_K*A)*A.adjoint` and unitary invariance identify this
with the nuclear commutator norm. The angular rounding theorem is
compiled; that norm-spectrum lemma and the resulting exact commutator
formulation are not claimed by this checkpoint. Inspect the existing
modulus API and `Proposition35.section3SinAngleOperator`, together with
paired cosine bases, before starting a coordinate proof.

## Infinite-dimensional operator-ideal transport lower bound

`ForTauCeti/Analysis/OperatorIdeal/Family/UnitaryTransport.lean` proves
`OperatorIdealFamily.gauge_projection_sub_le_unitary_displacement`.
For every accepted `OperatorIdealFamily`, real or complex Hilbert space,
orthogonally complemented `K,L`, and ambient isometric equivalence
mapping `K` to `L`, the gauge of `P_K-P_L` is at most the gauge of `I-W`.
No dimension, separability, compactness, finite-rank or finite-gauge
hypothesis is imposed. The proof uses the source reflection and two
unitary translates of the displacement. It includes extended infinite
values. Left and right isometry invariance of the accepted family gauge
are proved as reusable lemmas. This is classical norm mathematics and
not an independent priority claim.

Focused build passed (4,996 jobs), after the cache fetch. The exact
infinite-dimensional Schatten optimum and its attainment remain open.
A useful proof route to investigate is finite-rank truncation of the
competing unitary itself, with no increase of its gauge, rather than
assuming Schatten-norm density of the source-commuting unitary group.

## Compact unitary truncation in arbitrary Hilbert dimension

`FiniteUnitaryTruncation.exists_finite_unitary_truncation` constructs an
actual ambient unitary equal to the input on a finite invariant subspace
and identity on its orthogonal complement. Its displacement factors as
`(I-U) P_M`, has rank at most `dim M`, and decreases every accepted
operator-ideal gauge. Its operator-norm error is bounded by the discarded
restriction. The ambient space may be real or complex, nonseparable and
infinite-dimensional.

`CompactUnitaryApproximation.exists_finite_unitary_approximation` chooses
`M` as the positive spectral band of the compact displacement modulus.
It achieves any positive operator-norm tolerance and preserves the
simultaneous gauge bounds. `exists_finite_unitary_approximation_sequence`
constructs one convergent sequence of finite-rank unitary perturbations
working for every operator-ideal family. No eigenbasis for the possibly
nonseparable kernel is chosen. Focused builds passed (5,192 and 6,370
jobs respectively), each after a cache fetch.

These are proved infinite-dimensional approximation results, not yet the
exact infinite-dimensional transport minimum. The approximants need not
carry the original source projection to the original target: the target
changes with the approximating unitary. A proof using this route must
pass the principal-angle cost through that change. Alternatively, an
ideal-norm approximation commuting with the source would preserve the
original target after multiplication by a fixed transporter. Both routes
still need their exact hypotheses and convergence statements discharged.

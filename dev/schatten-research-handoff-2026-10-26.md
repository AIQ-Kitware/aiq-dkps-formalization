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

## Schatten-norm density with simultaneous commutant preservation

`OperatorIdealFamily.tendsto_gauge_schatten_zero_of_singularValue_le`
proves a dominated-convergence theorem in the accepted Schatten family:
operator-norm convergence to zero upgrades to Schatten-gauge convergence
when every singular-value sequence is dominated by one fixed member of
that Schatten ideal. The parameter filter and both Hilbert dimensions
are arbitrary. `isCompactOperator_of_gauge_schatten_ne_top` derives
compactness directly from summability of approximation-number powers.

`CompactUnitaryApproximation` now records domination of the approximation
error's singular values by those of `U-I`. It also proves that one
truncation sequence preserves every bounded operator commuting with
`U`, not only a prescribed projection or self-adjoint observable. This
uses accepted Tau Ceti unitary intertwining of adjoints and reduction of
spectral-band subspaces.

`SchattenUnitaryApproximation.exists_schatten_finite_unitary_approximation_sequence`
therefore proves actual Schatten-norm density of finite-rank unitary
perturbations for all finite real exponents `p>=1`, preserving every
commutant of the input unitary and decreasing every ideal displacement
gauge. This includes the nuclear endpoint and arbitrary, potentially
nonseparable Hilbert spaces. The focused build passed (6,470 jobs).
These are classical approximation statements formally proved here;
historical novelty is not claimed for them. The exact infinite-dimensional
minimum is still a separate result, requiring geometric reduction and
attainment. The next use is approximation within the exact transport
fiber relative to a supplied feasible reference transporter.

## Exact-fiber density and an unrestricted lower-bound criterion

`SchattenTransportDensity.exists_schatten_transport_finite_update_sequence`
now proves that two Schatten perturbations of identity transporting the
same bounded operator to the same target can be approximated inside that
exact fiber: each approximant differs from the supplied reference by
finite rank, and converges to the competitor in Schatten gauge as well
as operator norm. Both fields, every finite `p>=1`, arbitrary bounded
source/target operators and nonseparable Hilbert spaces are included.

`schatten_transport_lower_bound_iff_finite_updates` proves that any
extended nonnegative lower bound for the whole transport fiber is
equivalent to its validity on these finite-rank updates of the reference.
The unrestricted side includes competitors with infinite cost. This
justifies the analytic limiting step in the proposed infinite-dimensional
proof; it does not supply the finite-dimensional geometric comparison or
the claimed angle-sum formula. Focused build passed (6,472 jobs).
The next geometric obligation is a common finite reducing support for
finite-rank competing corrections and the source projection, followed by
an exact comparison of its angle cost with the fixed active core.

## Finite reducing supports

`FiniteTransportSupport.exists_finite_transport_support` proves the next
geometric step: a finite-rank unitary perturbation and an orthogonal
projection have a common finite reducing support containing any supplied
finite core, with the unitary fixing the orthogonal complement pointwise.
The construction saturates the core and displacement range by the source
projection; it makes no assumption that the ambient competitor already
preserves principal planes. The companion lemmas
`LinearIsometryEquiv.apply_eq_self_of_mem_orthogonal_displacement` and
`isReducing_of_displacement_range_le` need no finite dimension or
closedness at all. Focused build passed (5,182 jobs).

Still needed for the finite-core exact optimum: restrict a finite-rank
competitor to this support, identify displacement gauges under orthogonal
zero extension, compare the support's accepted angle sum to the fixed
core, and apply the exact-fiber lower-bound criterion. These support and
density results are classical reduction tools, not separate historical
novelty claims.

## Exact spectral costs under finite-core restriction

`ContinuousLinearMap.singularValue_orthogonal_extension` and
`OperatorIdealFamily.gauge_orthogonal_extension` prove that orthogonal
zero extension preserves every approximation number and every accepted
ideal gauge. `eq_orthogonal_extension_iff` characterizes extension by its
actions on the source block and its orthogonal complement. The gauge
statement uses complete subspace carriers, as required by the accepted
family API; no finite dimension is imposed.

`SchattenFinite.gauge_schatten_rpow_eq_ofReal_finite` identifies the
accepted Hilbert-space Schatten power with the already-used finite
Schatten seminorm power. `gauge_schatten_ne_top_of_rank_le` proves ideal
membership for any finite-rank bounded map. No additional Schatten norm
is defined.

`Submodule.tsum_sine_penalty_eq_principalAngle_sum_of_finite_core`
proves that every zero-preserving ambient directed-sine penalty agrees
exactly with the accepted principal-angle sum on a finite reducing core
off which the two projections agree. This bypasses a choice of ambient
principal-plane enumeration and handles arbitrary Hilbert dimension.
The sine-map restriction lemma has been moved, with its same name and
proof, to `Projection/InvariantSubspace.lean` and generalized to infinite
ambient and carrier dimensions with explicit projection hypotheses.
Focused builds passed (4,996; 5,752; 6,782 jobs). Next apply these cost
identities to the existing finite complex global lower bound, then use
exact-fiber density to include all ambient competitors.

## Unrestricted Hilbert-space lower bound for finite-rank pairs

`DavisKahan/InfiniteDimensional/DirectRotation/SchattenFiniteRank.lean`
proves
`sine_phaseMinimum_sum_le_schatten_transport_of_finite_rank_reference`.
For `1<p<2`, orthogonally complemented complex Hilbert subspaces `K,L`
and one unitary `R` mapping `K` to `L` with `rank(I-R)<=n`, **every**
ambient unitary `U` mapping `K` to `L` satisfies

```
sum'_j ofReal (phaseMinimum p (arcsin (s_j((I-P_L)P_K))))
  <= SchattenGauge_p(I-U)^p.
```

This is a literal accepted Schatten-family inequality, not a prescribed
principal-block result. The competitor need not have finite-rank or
finite-Schatten displacement. The ambient space need not be separable or
finite-dimensional, and `K,L` themselves may have infinite rank and
corank. The finite-rank **reference** is a real hypothesis, not a claim
that arbitrary Schatten pairs have such a reference. Focused build passed
(7,364 jobs); the module is included in `InfiniteDimensional.All`.

Dependencies now include `Submodule.exists_finite_transport_section`,
which constructs the actual finite restricted unitary, complementary
projection agreement and exact displacement extension, and
`schatten_transport_lower_bound_iff_finite_rank`, which reduces an exact
fiber with finite-rank reference to finite-rank competitors. The generic
`Submodule.map_eq_iff_conjugate_starProjection` states projection
conjugacy without finite-dimensional or complex-only restrictions.

Next prove finite-rank attainment of this ambient cost by extending the
existing finite minimizer by identity, then replace the finite-rank
reference hypothesis by a general feasible Schatten reference. The
current theorem alone is a lower bound, not the full exact minimum.

## Exact Hilbert-space minimum and attainment for finite-rank references

`SchattenFiniteRankAttainment.exists_unitary_minimizing_schatten_transport_of_finite_rank_reference`
closes the exact `1<p<2` minimum under the preceding finite-rank reference
hypothesis. It supplies an actual finite-rank unitary attainer, the exact
ambient directed-sine phase sum, and comparison of its accepted Schatten
gauge with **every** feasible ambient unitary. No finite dimension,
separability, finite source rank, finite source corank, or competitor
ideal-membership assumption is added.

The construction
`exists_finite_rank_transport_attaining_sine_phaseMinimum_sum` works for
every finite `p>=1`; only the combined global-minimum theorem currently
uses `1<p<2`. `Submodule.exists_transport_extension_by_identity` proves
the actual extension by identity, including subspace transport and exact
displacement factorization, even for an infinite reducing block.
Attainment focused build passed (7,368 jobs).

`SchattenAngleContinuity.continuousOn_phaseMinimum_angle` proves continuity
of the scalar phase minimum on all nonnegative angles for `p>=0`, including
zero and the bifurcation. It normalizes the variable phase interval to
the fixed unit interval and uses compact-minimum continuity, rather than
differentiating a selected optimizer. Its focused build passed (6,666
jobs). This opens a simpler route to the **general** Schatten lower bound:
truncate the competing unitary itself, let the target projections vary,
and pass each finite singular-value penalty to the limit. The finite-rank
reference can then be removed from the lower-bound theorem; full general
attainment still requires compact-pair geometry and balanced defect
spaces. Neither general attainment nor historical priority is claimed.

## General unrestricted Hilbert-space lower bound (no reference)

`SchattenGlobalLowerBound.sine_phaseMinimum_sum_le_schatten_transport`
now removes the finite-rank reference entirely from the `1<p<2` lower
bound. Its only geometric inputs are orthogonally complemented complex
Hilbert subspaces and an actual ambient unitary mapping one to the other.
The inequality includes infinite values, nonseparable spaces and
infinite-rank subspaces and competitors. Finite Schatten cost itself
implies the compactness needed in the nontrivial proof branch.

The proof truncates the competitor, varies its target projection, and
passes each finite spectral penalty sum through operator-norm convergence.
Nonnegativity then recovers the full infinite sum. This avoids assuming
a compact-pair decomposition or choosing an ambient principal-angle
enumeration for the lower bound. The older, weaker reference-dependent
lower-bound declaration and proof have been removed, and the finite-rank
attainment theorem now consumes the general result directly. Focused
build passed (7,370 jobs after migration).

General ideal-theoretic **attainment and optimizer classification** are
still open: the present exact-attainment theorem retains its finite-rank
reference hypothesis. Defect-index balance, construction of a general
Schatten attainer, and its finite-rank relation to a direct rotation for
`1<p<2` have not been promoted to Lean theorems.

## Nuclear endpoint in Hilbert space

The general lower-bound theorem and finite-rank-reference exact minimum
now cover **`1<=p<2`**, including `p=1`. The finite-section proof uses the
already-compiled unrestricted finite nuclear theorem at the endpoint;
the Hilbert limiting proof is unchanged and does not differentiate a
nuclear norm.

`SchattenNuclearEndpoint.phaseMinimum_one_sum_eq_twice_nuclear_sine`
identifies the full ambient endpoint value as
`2 * SchattenGauge_1((I-P_L)P_K)`, including infinite values.
`twice_nuclear_sine_le_transport` proves this lower bound for every
complex Hilbert-space unitary transporter, with no finite-rank reference.
`exists_unitary_minimizing_nuclear_transport_of_finite_rank_reference`
attains exactly that value by a finite-rank unitary whenever a finite-rank
feasible reference exists; its comparison includes every ambient
competitor. Focused endpoint build passed (7,378 jobs).

The exact minimum for general Schatten-class pairs, all infinite-dimensional
optimizer classifications, and feasibility characterized by defect-index
balance remain beyond these theorems. In particular, a proof with a
finite-rank **reference transporter** must not be advertised as covering
every pair whose projection difference merely belongs to a Schatten ideal.

Primary-source novelty cross-check: Andruchow--Larotonda--Recht,
[Finsler geometry and actions of the p-Schatten unitary groups](https://arxiv.org/abs/0808.2274)
(2008), studies rectifiable-distance geometry and minimal exponential
curves, with the abstract's principal theorem assuming even positive
integer exponents. This is a different objective from the present
displacement `||I-U||_p`; the comparison is not evidence of historical
priority. The full theorem-level predecessor audit remains necessary.
The classical density, finite-section and zero-extension lemmas are not
claimed as novel mathematics independently of the transport theory.

## Exact finite-rank projection-pair theorem with explicit defect balance

`SchattenFiniteRankPairs.exists_unitary_minimizing_schatten_transport_of_finite_rank_projection_sub`
now states the exact `1<=p<2` minimum directly from `rank(P_K-P_L)<=n`
and equality of `finrank(halmosSourceDefect K L)` and
`finrank(halmosTargetDefect K L)`. No reference transporter is supplied by
the caller. It constructs a finite-rank optimizer with the intrinsic
ambient angle cost and compares it against every ambient complex unitary.
The nuclear specialization gives exactly twice the nuclear directed
sine gauge. Infinite rank/corank and nonseparable ambient spaces are
still allowed.

`DirectRotationRank.rank_one_sub_nonacuteDirectRotation_le_projection_sub`
proves, over both fields in arbitrary Hilbert dimension, that every
completed direct rotation has displacement rank at most the projection
difference rank. The proof factors the displacement through the kernel
quotient of the projection difference; it uses the existing theorem that
a completed rotation fixes every vector on which the projections agree.
`finiteDimensional_crossedDefects_of_projection_sub_rank_le` proves both
crossed defects are finite-dimensional, so the displayed finrank balance
is a substantive equality of finite defects, not the degenerate value
`finrank=0` for an infinite-dimensional space. An isometric defect
identification and then a finite-rank feasible reference are constructed.
Focused pair build passed (7,384 jobs).

Next obligations: prove necessity of defect balance for compact/ideal
transporters, and construct/generalize ideal attainers when the projection
difference is Schatten but not finite-rank. Current pair hypotheses are
sufficient; an iff feasibility classification is not yet claimed.

## Finite-rank feasibility is now an iff

`DirectRotationRank.finite_rank_transport_iff_projection_sub_finite_rank_and_defect_balance`
proves the complete finite-rank feasibility criterion, over both scalar
fields and arbitrary Hilbert dimension: a finite-rank perturbation of
identity transports the subspaces iff their projection difference has
finite rank and their crossed-defect dimensions agree. The sufficiency
constructs a completed direct rotation with displacement rank bounded by
the projection difference rank. Necessity identifies both global defects
with the actual defects of a finite reducing section.

`Submodule.finite_crossedDefect_balance_of_finite_rank_transport`
also proves that both defects really are finite-dimensional and the
projection difference has finite rank. Its complement/intersection and
support-range lemmas have no ambient completeness or dimension assumption.
Focused build, including the exact pair optimizer consumer, passed
(7,386 jobs).

This iff currently concerns the finite-rank restricted unitary group.
To exclude finite Schatten cost for unbalanced finite-rank projection
pairs, next prove that a compact-displacement transporter for such a pair
can be replaced by a finite-rank-displacement transporter. A useful route
is to approximate it by a finite-rank unitary, use a small-gap direct
rotation to correct the target, and note that the target correction has
finite-rank projection difference. This avoids assuming a Fredholm-index
identity that has not yet been connected to the projection API.

## Compact and Schatten feasibility; infinite-cost obstruction

`CompactTransportFinitePairs.exists_finite_rank_transport_of_compact_transport_of_projection_sub_rank_le`
implements the target-correction argument just described. Together with
`compact_transport_iff_defect_balance_of_projection_sub_rank_le`, it
proves that compact and finite-rank unitary feasibility coincide for a
finite-rank projection pair, and both are exactly crossed-defect balance.
The proof works over both fields and arbitrary Hilbert dimension.

`SchattenFeasibility.schatten_transport_iff_defect_balance_of_projection_sub_rank_le`
extends this equivalence to **every finite real `p>=1`** in the accepted
Schatten family. `schatten_transport_eq_top_of_defect_imbalance` proves
that, for an unbalanced finite-rank projection pair, every ambient
unitary transporter has infinite cost at all these exponents. An
unrestricted ambient unitary equivalence therefore must not be mistaken
for feasibility in a Schatten restricted unitary group.

Combining this obstruction with the balanced-pair optimizer gives the
complete finite-valued feasibility and value classification for complex
finite-rank projection pairs at `1<=p<2`: balanced defects give the
compiled exact finite-rank attainer and angle sum; unbalanced defects
force infinite cost for every feasible ambient competitor. Focused
feasibility build passed (7,168 jobs). This does not yet treat general
compact or Schatten projection differences of infinite rank, nor classify
all optimizers. The underlying index obstruction is classical.

## Canonical regime at `p>=2` in arbitrary complex Hilbert dimension

`SchattenCanonical.schatten_nonacuteDirectRotation_le_transport` proves
that every completed direct rotation minimizes the accepted Schatten
gauge for every finite real `p>=2`, against every ambient complex unitary
transporter. No finite dimension, separability, compactness, finite-cost
or competitor block hypothesis is imposed; a crossed-defect isometric
identification supplies the completed direct rotation and includes the
right-angle sector. This is the classical Q-norm regime, not a priority
claim.

`OperatorIdealFamily.gauge_schatten_gram_eq_sq` proves the native extended
identity `Gauge_(p/2)(T* T)=Gauge_p(T)^2` in arbitrary complex Hilbert
dimensions, including infinite values. The canonical comparison applies
the existing full Hilbert-space squared-displacement Ky Fan theorem,
accepted symmetric-gauge dominance and this identity. No new norm or
parallel operator-ideal family is defined. Focused builds passed (6,600
and 7,472 jobs respectively).

Still needed to assert ideal attainment directly from a general
`P_K-P_L in S_p` hypothesis: prove that the completed rotation differs
from identity by a member of that ideal. A promising algebraic route is
`(I-R)(I+R)=2(I-S)`, with `S` the canonical intertwiner, together with
invertibility of `I+R` from the nonnegative Hermitian part of `R` and
`I-S=(P_K-P_L)J_K`. This gives a bounded right factor of the projection
difference and avoids assuming compact spectral enumeration.

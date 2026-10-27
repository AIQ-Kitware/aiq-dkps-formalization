# Schatten transport research checkpoint — 26 October 2026

Manuscript and visualization updates are assigned separately. This record
describes new mathematics and the exact next proof obligations. The target
is the journal research extension on exact real and complex transport,
not an addition to the frozen 29-result Davis--Kahan source denominator.

Historical-search handoff: the user-supplied external review is archived in
[historical-priority-review-2026-10-26.md](historical-priority-review-2026-10-26.md).
It records the Aubrun–Szarek exercise lead, inspected neighboring formulations,
source-authentication limits and remaining citation checks. Its older infinite-
dimensional status is superseded by the frontier below. Reuse that record
before repeating the literature search; do not infer first-discovery priority.

## Current frontier — read before chronological entries

As of 27 October, the complex nuclear endpoint also has exact general
infinite-rank attainment and intrinsic sine value under trace-class
projection difference and balanced defects. Its uniqueness criterion is
complete without standing hypotheses: unique global optimizer iff K=L.
Opposite explicit global optimizers have separation `2 ||P_K-P_L||`.
The finite-dimensional nuclear endpoint now has a single dual-positivity
certificate characterizing every ambient optimizer, and all optimizers
fix the full kernel of the projection difference. The complete infinite-
rank nuclear **every-optimizer** certificate and phase/multiplicity
parametrization remain open; see the final entry for the exact analytic
obligation. These statements supersede older nuclear value/uniqueness
gaps in chronological entries, without extending historical-priority claims.


General infinite-rank complex Schatten `1<p<2` attainment and the complete
classification of **every** global optimizer are **proved**, under native
Schatten projection difference and balanced crossed defects. Every optimizer
has the same canonical inactive tail and a finite strictly active correction
with an explicit rank budget (`aeb6384f1`, `113746cf9`). Every nearest
projection-commuting correction is also classified, with a closed commutator
uniqueness certificate and rank budget (`ddbef2d43`). The two-level
self-adjoint symmetry application below has passed the full default build
(21,241 jobs). Earlier statements calling these endpoints open are historical
stages and are superseded. Historical priority remains qualified; see the
supplied-review addendum in the paper-directory novelty review.

The infinite optimizer-space finite-cutoff homeomorphism, operator-norm
compactness and independent multiplicity-coordinate topology are now proved;
see the latest topology entries below. Rank labels are locally constant
and separated, and simple active factors with no right defect give exactly
`2^s` isolated optimizers. Necessity of the infinite uniqueness threshold
is now also proved: uniqueness is equivalent to the closed projection-gap
bound `2 sqrt(p-1)/p`, under the native Schatten hypothesis alone. The
exact nearest-commuting-correction iff uses the same threshold on the
actual commutator norm, also without a separate balance assumption.
The strongest iff statements now make even native Schatten membership
part of the conclusion: arbitrary orthogonally complemented projection
pairs have a unique optimizer exactly when their difference is Schatten
and their gap obeys the closed threshold. The correction version has the
analogous necessary-and-sufficient membership and norm conditions.
The next mathematical targets are quantitative stability or certified
approximation from inexact input, and connectedness of rank strata.
Critical scalar-phase conditioning is now proved exactly: the excess
cost divided by the fourth power of phase tends to a strictly positive
explicit coefficient. Two-sided local quartic growth and failure of
every positive quadratic modulus are compiled. The same coefficient
now holds for the literal planar Schatten-power cost divided by the
fourth power of actual operator-norm transporter distance. The planar
no-quadratic-modulus theorem therefore excludes quadratic growth over
all ambient feasible unitary transporters. A positive lower growth bound
for every near-minimizer remains a separate task.
The original norm objective, as well as its `p`-th power, now has its
exact positive critical coefficient and its actual ambient planar
no-quadratic-modulus theorem; see the latest critical-norm entry below.
Varying-data stability is now also proved for simultaneous source and
target changes: throughout the closed canonical regime, actual
infinite-dimensional Schatten optimizers obey a dimension-free Lipschitz
bound in the sum of the two projection errors.
The endpoint constant is `p/(2-p)`. This differs from an objective-error
certificate for an arbitrary near-minimizer of one fixed problem, which
remains open.
Nearest projection-commuting correction is now also Lipschitz in the
input unitary, with constant `1/sqrt(1-gamma^2)` and endpoint `p/(2-p)`.
This uses the polar factorization of the actual diagonal block and
contractivity of pinching, so it avoids the extra loss of an image-gap
triangle estimate. See the correction-data entry below.
General infinite-rank complex Charbonnier **attainment** is now also proved:
native Hilbert--Schmidt projection difference and balanced crossed defects
are necessary and sufficient for a finite-cost global attainer. Its exact
angle value and a finite correction with an explicit critical rank budget
are compiled; see the new attainment entry below. General infinite-rank
complex nuclear attainment is also proved by the explicit phase construction
recorded at the end of this handoff. Classification of every nuclear optimizer
and real infinite-dimensional optimization remain open. The later entries
supersede earlier Charbonnier and strict-Schatten classification gaps.
The native infinite Charbonnier rank-one first variation, constrained
stationarity, compact gradient and actual finite minimizing gradient-cutoff
sectors are now proved. The full zero-gradient reflection sector and preservation of every intrinsic
angle sector are now also proved. Every finite-cost global smoothed optimizer
fixes all vectors on which the projections agree. The next gap is closed-
threshold canonical uniqueness, then canonical-tail necessity and the full
finite-cutoff characterization of every ambient optimizer.
The dated sections below preserve proof history; use this paragraph and the
latest endpoint sections for the current frontier.

## Explicit diagonal-block construction of every nearest correction

`SchattenCorrectionDataStability.lean` now proves
`schatten_correction_isMin_iff_eq_diagBlock_factorThru_modulus`.
Let `E` be any complete complex Hilbert space, `K` an orthogonally
complemented submodule, `A` an actual unitary, and `1<p<2` finite. Assume
`[A,P_K]` belongs to the native Schatten ideal and its operator norm is
at most `sin(criticalAngle p) = 2 sqrt(p-1)/p`. For **every** ambient unitary
`C`, the following are equivalent:

- `C` commutes with `P_K` and globally minimizes the native extended
  Schatten distance to `A` over all commuting ambient unitaries;
- as an operator, `C = T.factorThru T.modulus`, where
  `T = K.diagBlock A = P_K A P_K + (I-P_K) A (I-P_K)`.

This is an exact construction and characterization at the **closed**
threshold, not an optimization within a prescribed block ansatz. It
requires no separate index balance, separability or finite-rank hypothesis.
The native objective includes competitors at infinite distance. Existing
existence establishes that the literal accepted `factorThru` expression
is an actual unitary in this regime.

Reusable supporting statements are
`ContinuousLinearMap.IsPositive.eq_modulus_of_unitary_factorization`,
`ContinuousLinearMap.eq_factorThru_modulus_of_unitary_factorization_of_coercive`
(in `ForTauCeti/.../Polar/Perturbation.lean`, either scalar field and arbitrary
Hilbert dimension), and
`canonical_correction_eq_diagBlock_factorThru_modulus`
(in `DavisKahan/Geometry/Polar/CommutingCorrectionStability.lean`).
The proof identifies the positive factor with the accepted modulus and
uses coercivity to eliminate the kernel in the accepted factor-through API.
No new polar-factor definition or forwarding facade is introduced.

Focused build passed (8,056 jobs), and the full default build passed
(21,271 jobs), with warnings treated as errors. This construction uses
classical polar uniqueness; its formal verification is not a historical first-priority claim.
Paper and visualization changes remain assigned separately.

The input-error sharpness target described here is now **compiled**, in
`SchattenCorrectionSharpness.lean`; see the next entry. Its real-coordinate
version has the conventional two-dimensional witness
`A=[[c,s],[-s,c]]`, `B=[[-c,s],[-s,-c]]`, with `c=cos(theta)>0` and
`s=sin(theta)`. Their diagonal polar corrections are `I` and `-I`, both
commutator norms equal `s`, and their input/output distance ratio is `1/c`.
At the critical angle this is `p/(2-p)`. The compiled witness uses the
existing diagonal eigenbasis model of these actual unitaries.
General objective-error control for arbitrary near-minimizers also remains
open, and must distinguish norm excess from power-cost excess.

## Sharp correction conditioning at every commutator budget

`SchattenCorrectionSharpness.lean` proves
`exists_nearest_schatten_corrections_attaining_commutator_ratio` and
`exists_nearest_schatten_corrections_attaining_critical_ratio`.
For every finite `1<p<2` and **every**
`0 <= gamma <= sin(criticalAngle p)`, there are genuine complex 2-dimensional
unitaries `A,B,C,D` such that:

- both `C,D` commute with the fixed diagonal-line projection;
- both input commutators are native Schatten and have norm **exactly** `gamma`;
- `C,D` globally minimize their respective native extended Schatten costs
  over **all** ambient commuting unitaries;
- `norm(A-B)>0` and
  `norm(C-D) = norm(A-B)/sqrt(1-gamma^2)`.

Consequently the preceding dimension-free certificate cannot use a smaller
uniform coefficient at any admissible budget. In particular `p/(2-p)` is
attained at the exact critical budget, not just approached in a limit.
The angle-parametrized equality theorem is
`exists_nearest_schatten_corrections_attaining_cosine_ratio`.

The witness uses `A=scalarPhaseTransport theta 0`,
`B=scalarPhaseTransport (pi-theta) 0`, `C=I`, `D=-I`, and
`theta=arcsin(gamma)`. Its diagonal blocks are `cos(theta) I` and
`-cos(theta) I`. The exact commutator is `sin(theta)` times an actual
unitary; the input distance is `2 cos(theta)` and output distance `2`.
`planar_nearest_schatten_corrections` certifies both global minimizing
properties using the preceding literal diagonal-polar characterization.
Thus this is an ambient optimization result, rather than merely sharpness
of an algebraic bound on a constructed family.

Focused build passed (8,080 jobs), and the full default build passed
(21,273 jobs), with warnings treated as errors. Coordinate lemmas were
added to the existing planar model rather than duplicating its unitary
construction. This is an exact sharp consequence of the Schatten optimizer
theory; sharp classical polar conditioning alone is not claimed historically
new. Manuscript and visualization changes remain separate.

The next extension selected after this checkpoint was general
infinite-rank **Charbonnier** attainment, now completed in the later entry below. Its natural feasibility ideal is
Schatten 2, because the penalty is quadratic near zero. Existing unrestricted
lower bounds and finite-rank attainment do not yet establish that endpoint.
The candidate proof splits off a finite spectral cutoff and uses the
canonical smoothed-optimal tail; both the exact tail cost and global
attainment must be proved before promoting the result.

## Exact infinite Charbonnier canonical and cutoff-tail costs

`CharbonnierCanonicalTrace.lean` proves
`charbonnier_nonacuteDirectRotation_eq_minimum_sum_of_subcritical`:
for every positive `tau`, compact complex projection difference and actual
crossed-defect completion, if
`projectionGap K L <= sin(smoothedCriticalAngle tau)`, the literal
Charbonnier cost of the canonical rotation equals the intrinsic sum of
`smoothedPhaseMinimum tau` over directed sine singular angles. No Schatten
membership, finite-rank or separability hypothesis is imposed, and the
equality includes infinite costs.

`CharbonnierSubcriticalTail.lean` proves
`charbonnier_canonical_cutoff_tail_eq_minimum_sum`: removing a finite sine
sector above any positive cutoff no larger than the closed critical sine
leaves exactly this minimum cost on the full complementary pair.
Critical eigenvalues and nonseparable fixed directions are included.

The proof identifies actual finite restrictions with the restricted-pair
canonical rotation, applies the existing finite exact optimizer theorem,
and passes to the norm limit by lower semicontinuity. Scalar monotonicity
is used only in the subcritical range where the canonical branch applies.
The unrestricted Hilbert lower bound supplies the reverse inequality.
Thus no unproved infinite spectral decomposition or exchange of divergent
traces is assumed.

Focused builds passed (7,294 and 7,302 jobs), and the full default build
passed (21,277 jobs), with warnings treated as errors. The next step is
finite smoothed-block replacement plus the proved canonical tail: this
will establish full infinite-rank attainment under native Schatten-2
projection difference and balanced crossed defects. That assembly is
not asserted by the tail theorem alone.

## General infinite-rank Charbonnier attainment and exact feasibility

`CharbonnierGlobalAttainment.lean` now proves the following unrestricted
complex Hilbert-space endpoints, for every positive smoothing parameter.
No separability, finite ambient dimension, finite-rank difference or
prescribed competitor block assumption is imposed.

- `exists_charbonnier_minimizer_by_finite_correction`: given actual crossed-
  defect equivalence and native Hilbert--Schmidt projection difference,
  every positive cutoff at or below the smoothed critical sine yields
  a global optimizer `U`. It has finite literal Charbonnier cost, exact
  intrinsic `smoothedPhaseMinimum` angle sum, and agrees with completed
  direct rotation `R` on the whole complementary tail. The actual update
  rank is at most the cutoff dimension.
- `exists_unitary_minimizing_charbonnier_transport_of_projection_sub_ne_top`:
  native Schatten-2 projection difference and equality of the finite crossed-
  defect dimensions give an actual finite-cost attainer with that value,
  compared against **every** ambient unitary transporter, including
  infinite-cost competitors.
- `exists_charbonnier_minimizer_with_critical_rank_budget`: one can choose
  `rank(R-U) <= n` with
  `n * sin(smoothedCriticalAngle tau)^2 <= norm(P-Q)_{S_2}^2`.
  The Lean statement uses the native extended gauge and real powers.
  Critical eigenspaces require no phase correction.
- `charbonnier_finite_minimum_iff_projection_sub_and_defect_balance`:
  finite-cost global attainment holds **iff** the projection difference
  is native Hilbert--Schmidt and the crossed defects balance. Necessity
  uses the previously proved full feasibility criterion; sufficiency
  now supplies global attainment, rather than only a feasible reference.

The reusable either-field, arbitrary-dimension donor
`ContinuousLinearMap.charbonnierCost_unitary_displacement_eq_block_add_tail`
(in `ForTauCeti/.../OperatorIdeal/ReducingTrace.lean`) supplies exact block
replacement additivity, including divergent block and tail costs.
`CharbonnierCanonicalTrace.lean` also now exposes
`charbonnier_nonacuteDirectRotation_minimal_of_subcritical`, an unrestricted
infinite-dimensional canonical-optimality sufficiency theorem through the
closed smoothed gap threshold. Necessity and uniqueness are not claimed
by that theorem.

The assembly proof uses a finite common reducing sine sector, optimizes
its actual restricted pair, replaces that block in the canonical rotation,
and combines the exact finite optimum, proved infinite canonical tail and
intrinsic reducing-trace decomposition. Native Schatten-2 membership
ensures finite cost because the penalty is quadratic near zero. The
unrestricted Hilbert lower bound proves global optimality of the assembled
unitary. Right-angle defects are inside the finite sector; zero and
infinite fixed sectors remain on the canonical tail.

Focused build passed (7,346 jobs), and the full default build passed
(21,279 jobs), with warnings treated as errors. These are new compiled
scope extensions, not a theorem-level historical priority clearance.
The paper and visualizations remain assigned to a different agent.

### Next obligations at the attainment checkpoint (superseded below)

Attainment does not yet classify arbitrary minimizers. The finite smoothed
classification already exists, but the infinite analogue of
`SchattenStationarity.lean` / `SchattenGradientCutoff.lean` is missing.
The next decisive analytic lemma is a rank-one first variation of the
**native finite Charbonnier trace** for `1-U in S_2`, at every real time:
for unit `x`, with `U_s = U exp(s i rankOne(x,x))`, prove

```
d/ds CharbonnierCost_tau(1-U_s)
  = Re inner x (smoothedUnitaryGradient tau U_s x).
```

Use `toReal` only after proving finite cost along the whole variation.
The gradient is already defined by continuous functional calculus in
`SmoothedUnitaryVariation.lean`; its self-adjointness and commutation
statements already omit finite dimension. Its scalar symbol is
`Im(z)/sqrt(tau^2+|z-1|^2)`. Stationarity should then imply reflection
conjugation negates this gradient. Compact positive gradient cutoffs can
inherit finite global optimality using the proved Charbonnier block
additivity and cancellation of a **finite** complementary cost.

For the derivative limit, do not infer continuity of the trace from mere
operator-norm convergence. A possible route is finite unitary truncation
in native S_2, plus uniform control of the rank-one-perturbed singular-
value tails (rank-one interlacing), the quadratic Charbonnier bound and
the existing finite derivative/CFC arguments. This route remains unproved.
A general S_2-continuity lemma for the Charbonnier trace would also supply
the missing convergence, if established with actual hypotheses.
After stationarity, handle the zero-gradient reflection sector explicitly
and recover the finite active head and canonical inactive tail before
claiming all-optimizer classification or uniqueness. Infinite nuclear
attainment/classification and real infinite-dimensional theory remain
independent open directions.

## Native Charbonnier first variation and every-optimizer stationarity

The analytic first-variation obstruction in the preceding checkpoint is now
**closed**, including its native infinite trace-convergence step.

`ForTauCeti/Analysis/InnerProductSpace/CharbonnierRankOneVariation.lean`
proves `TauCeti.hasDerivAt_charbonnier_unitary_rankOne_variation`: on every
complete complex Hilbert space, for `tau>0`, an actual unitary `U` with
finite native Charbonnier displacement cost, and any unit vector `x`, the
real native cost along `U exp(s i rankOne(x,x))` has derivative
`Re inner x (smoothedUnitaryGradient tau U_s x)` at **every** real time.
No separability, finite-rank displacement, simple spectrum or nonzero
singular-value condition is required. Finite cost along the entire
variation is proved before taking `toReal`.

The missing convergence is supplied by
`ContinuousLinearMap.tendsto_charbonnierCost_of_singularValue_tail_le`
and `tendsto_charbonnierCost_of_bounded_rank_perturbation` in
`ForTauCeti/.../OperatorIdeal/CharbonnierConvergence.lean`. In either scalar
field and for arbitrary complete Hilbert carriers, operator-norm limits
preserve the native trace if the singular-value tails, after one fixed
finite index shift, are dominated by a fixed native Hilbert--Schmidt
operator. Interlacing supplies the rank-one shift for the varied finite
unitary approximations. Dominated convergence uses the quadratic bound;
mere operator-norm convergence is **not** asserted sufficient.

The existing `smoothedPhaseDerivative`, `smoothedUnitaryGradient` and their
basic scalar/self-adjointness/commutation/eigenvector lemmas were moved from
the finite paper namespace to their reusable `TauCeti` owner in
`CharbonnierGradientHilbert.lean`. The finite consumers use these declarations
directly; no alias, duplicate gradient or forwarding namespace remains.
The eigenvector lemma retains its actual finite-dimensional hypothesis.
The general Hilbert restriction theorem uses accepted CFC intertwining.
Continuity on the full unitary group, compactness for compact perturbations
of identity, and locally uniform convergence of gradient pairings are proved.
`CharbonnierFiniteRankVariation.lean` identifies the native finite-support
cost with its normal spectral trace and certifies its actual derivative.

`CharbonnierStationarity.lean` proves
`gradient_reflection_conjugate_eq_neg_of_charbonnier_minimal`.
For **every** finite-cost global ambient transporter `U`, its self-adjoint
gradient `G` satisfies `J_K G J_K = -G`. The proof derives vanishing feasible
rank-one derivatives, normalizes arbitrary vectors, and polarizes the two
zero diagonal quadratic forms. It does not assume a principal-plane form.

`CharbonnierGradientCutoff.lean` proves
`exists_charbonnier_minimizing_restriction_on_gradient_cutoff`.
Every positive gradient-modulus cutoff of **every** finite-cost global
optimizer is finite-dimensional, reduces both source and target projections
and the actual unitary, retains the forward and inverse restrictions, and
carries an unrestricted finite smoothed global minimizer. The complementary
gradient norm is at most the cutoff. No canonical-tail or block assumption
is imposed on the given optimizer. The either-field reusable restriction
lemmas in `CharbonnierMinimizerRestriction.lean` cancel the actual finite-cost
complementary trace; cancellation is never applied to an infinite cost.

Focused builds passed for stationarity (6,854 jobs) and cutoff sectors
(7,336 jobs). The full default build passed **21,295 jobs**, with warnings
treated as errors. This is proof evidence, not historical-priority evidence.
No manuscript or visualization was changed. The name-drift command was run;
it reports unrelated migration-map/upstream-name findings, including the
accepted approximation-number and Ky Fan APIs, rather than any moved
smoothed declaration. Compiler validation of `Challenge` is run separately
because it is outside the default targets.

### Classification obligations at the first-variation checkpoint (superseded below)

1. Prove the smoothed radial identity
   `U-U* = CFC(2 i sqrt(tau^2+|z-1|^2), U) * G`.
   It should imply `U x = U.symm x` on `ker G`, including identity and
   negative-identity directions. Establish the actual self-adjoint unitary
   restriction on the **whole** gradient kernel.
2. At a finite-cost global minimizer, use compact displacement and the
   either-field compact-reflection theorem to isolate a finite optimizing
   reflection support within that kernel, with an exactly fixed complement.
   Right-angle defect choices must be retained explicitly.
3. Combine positive cutoff classifications with the kernel classification,
   then prove the common canonical inactive tail and the finite active
   multiplicity/defect normal form for every optimizer. Only after that
   establish the exact infinite smoothed uniqueness iff and optimizer topology.

The native first variation and cutoff-sector results alone do not imply
that every optimizer has the canonical tail. Infinite nuclear and real
classification remain separate open workstreams.

## Full smoothed gradient kernel, angle preservation and fixed directions

`CharbonnierGradientKernelHilbert.lean` proves
`unitary_sub_star_eq_radial_mul_smoothedUnitaryGradient`:
for every actual complex Hilbert-space unitary and `tau>0`,

```
U - U* = CFC(z => 2 i sqrt(tau^2 + |z-1|^2), U) * smoothedUnitaryGradient tau U.
```

The continuous multiplier is bounded on the unit circle and nonsingular at
identity. Thus `unitary_apply_eq_symm_of_smoothedUnitaryGradient_apply_eq_zero`
and `exists_selfAdjoint_unitary_restriction_smoothed_gradient_kernel` identify
the actual self-adjoint unitary action on the **entire** gradient kernel.
No finite-dimensional kernel, compactness, minimality or nonzero-displacement
assumption is needed. Both identity and negative-identity directions remain.

`CharbonnierGradientKernel.lean` proves
`exists_finite_reflecting_support_on_gradient_kernel_of_charbonnier_minimal`.
At every finite-cost global ambient optimizer, this full kernel restriction
inherits unrestricted native optimality. Its nonidentity action is supported
on a finite source-reducing sector whose actual restriction is a finite
smoothed global optimizer, with the complementary kernel fixed pointwise.
The proof uses compact displacement, the existing compact-reflection theorem
and cancellation of the actual finite complementary cost. It retains
right-angle reflecting choices rather than assuming the kernel is fixed.

`CharbonnierOptimizerAngles.lean` proves
`commute_sinAngleOperator_of_charbonnier_minimal`: every finite-cost global
complex smoothed optimizer commutes with `K.sinAngleOperator L`, in arbitrary
complete Hilbert dimension. Unequal principal-angle sectors cannot mix.
Compact gradient spectral completeness combines all positive minimizing
cutoffs with the actual self-adjoint zero-gradient restriction.
The finite input is the new direct consequence
`commute_sinAngleOperator_of_smoothed_minimal` in
`SmoothedOptimizerAngles.lean`: the existing weighted-attainment cosine
commutation theorem, Pythagoras and accepted modulus commutation give the
full sine commutation identity without new coordinates.

`apply_eq_self_of_projections_eq_of_charbonnier_minimal` now proves that every
such ambient optimizer fixes **each** vector `x` with `P_K x=P_L x`, including
common-source and common-orthogonal directions. Its reusable either-field
conditional form is
`apply_eq_self_of_projections_eq_of_charbonnier_minimal_of_commute` in
`CharbonnierMinimizerRestriction.lean`.
The native-faithfulness lemma
`ContinuousLinearMap.charbonnierCost_eq_zero_iff` holds for every **nonnegative**
smoothing scale and either scalar field, without finite rank, compactness
or completeness. The leading approximation number gives the operator norm,
so no illegal cancellation of an infinite trace enters this proof.

Focused build passed (7,348 jobs), and the full default build passed
**21,303 jobs**, with warnings treated as errors. `lake build Challenge`
also passed (19,755 jobs) after the preceding gradient ownership move;
the static name-drift findings for unrelated upstream declarations therefore
do not establish a compiler failure of those Challenge consumers.
Paper and visualization changes remain separate. These are exact scope
extensions of the optimizer theory; no new historical priority clearance
is inferred from their compilation.

### Strongest next mathematical endpoint

Close **infinite smoothed canonical uniqueness through the closed threshold**,
then the full canonical-tail necessity and finite-cutoff optimizer iff.
The remaining route is now explicit and independent of first-variation debt:

1. Adapt `SchattenCanonicalUniqueness.lean` using the proved smoothed angle
   commutation and fixed-direction theorem. Every positive sine cutoff is
   finite and carries an unrestricted minimizing restriction. Convert its
   native cost with `charbonnierCost_eq_ofReal_sum` and apply
   `smoothed_canonical_unique_minimizer` at the inherited closed principal-
   angle bound. Compact sine spectral completeness identifies the ambient
   unitary with `spectraCanonicalPolarFactor`.
2. Adapt `SchattenOptimizerTail.lean`. The actual infinite inactive restriction
   inherits native smoothed minimality, has finite cost by native S_2
   compression and `charbonnierCost_ne_top_iff_schatten_two`, and satisfies
   the closed gap bound. Apply step 1 and the existing geometric canonical-
   cutoff-tail identity to prove agreement with every completed rotation.
3. Combine canonical-tail necessity with exact Charbonnier block replacement
   additivity and the already compiled global attainer. Prove global minimality
   iff the actual finite restriction is a finite global minimum. Insert
   `smoothed_transport_isMin_iff_phase_and_defect_equiv_complex` to obtain the
   full multiplicity/defect normal form. Native feasibility guarantees a finite
   attainer, so arbitrary global minimizing competitors automatically have
   finite cost; do not retain that assumption unnecessarily in the final iff.
4. Treat the infeasible finite-cost regime separately: if an ambient transport
   exists but no finite-cost one exists, every feasible transport minimizes
   the extended objective at infinity. Do not apply finite-cost stationarity
   or phase classification in that regime.

The current kernel and angle theorems are **not yet** the full infinite
smoothed every-optimizer classification. Full infinite nuclear and real
classification remain independent open directions.

## Exact infinite-dimensional uniqueness threshold

`SchattenUniquenessThreshold.lean` proves
`schattenHilbertTransport_unique_minimizer_iff_projectionGap_of_defectEquiv` and
`schattenHilbertTransport_unique_minimizer_iff_critical_norm_of_defectEquiv`. For every
complete complex Hilbert space, finite `1<p<2`, native Schatten projection
difference, and an actual equivalence of the crossed defects, the global
ambient minimizing unitary is unique if and only if
`projectionGap K L <= sin(criticalAngle p) = 2 sqrt(p-1)/p`.
The objective is the native extended gauge, and every ambient competitor
is included, without a finite-cost assumption. The threshold is closed;
critical angles, repeated angles, zero directions and right defects are
not excluded by supplementary hypotheses.

The proof transfers uniqueness through the already compiled full
finite-cutoff homeomorphism, applies the finite exact uniqueness theorem,
and recovers the ambient gap from its actual reducing compressions. The
new reusable lemma
`ContinuousLinearMap.norm_eq_max_compressions_of_isReducing` gives that
norm identity in either scalar field, without compactness, completeness
or finite-dimensional assumptions beyond orthogonal complementation.
Thus a supercritical angle necessarily gives distinct ambient global
optimizers, rather than just nonuniqueness in a chosen competitor family.

Focused build passed (8,042 jobs), and the full default build passed
(21,249 jobs), with warnings treated as errors.
This is an exact consequence of the compiled classification; historical
priority is not inferred from its formal verification.

## Exact commuting-correction iff and removal of the balance hypothesis

`SchattenCorrectionCutoff.lean` proves
`existsUnique_nearest_schatten_commuting_unitary_iff_commutator` and
`existsUnique_nearest_schatten_commuting_unitary_iff_critical_norm`.
For every unitary `A` on any complete complex Hilbert space and every
orthogonally complemented `K`, assume only the native Schatten condition
`[A,P_K] in S_p`, with finite `1<p<2`. There is exactly one nearest unitary
commuting with `P_K` if and only if
`norm [A,P_K] <= sin(criticalAngle p) = 2 sqrt(p-1)/p`.
Every ambient commuting unitary is compared, including infinite-distance
competitors. A separate relative-index or defect-balance assumption is
unnecessary.

The necessity proof explicitly excludes a potentially misleading
extended-cost case: if a unique minimizer had infinite cost, every
commuting unitary would minimize. Identity and negative identity would
coincide, forcing the ambient space to be zero, where the cost is zero.
Finite cost therefore follows from uniqueness; compact transport then
implies balanced crossed defects. The generic equivalence
`OperatorIdealFamily.existsUnique_correction_iff_transport` records the
exact correction/transport uniqueness correspondence for either field
and every accepted ideal gauge.

The same module strengthens the transport criterion to **all** native
Schatten projection pairs:
`schattenHilbertTransport_unique_minimizer_iff_projectionGap` and
`schattenHilbertTransport_unique_minimizer_iff_critical_norm` no longer
assume a crossed-defect equivalence or even prior feasibility.
Necessity turns any unique transport into a unique commuting correction;
sufficiency has gap strictly below one and hence zero crossed defects.
Thus unbalanced pairs and the all-infinite-cost case are included rather
than silently excluded. The earlier balanced statements remain the
finite-cutoff proof lemmas, with the explicit `_of_defectEquiv` suffix.

Focused build passed (8,058 jobs), and the full default build passed
(21,251 jobs), with warnings treated as errors. This work adds
mathematical Lean results and this handoff only; manuscript and
visualization updates remain assigned separately.

## Unrestricted uniqueness, including non-Schatten data

`schattenHilbertTransport_unique_minimizer_iff` in
`SchattenCorrectionCutoff.lean` states the final criterion with no standing
compactness, ideal-membership, feasibility or defect-balance hypothesis:
for any orthogonally complemented pair on any complete complex Hilbert
space and finite `1<p<2`,

```
there exists exactly one ambient global Schatten optimizer
  iff (P_K-P_L belongs to S_p) and (gap K L <= 2 sqrt(p-1)/p).
```

`existsUnique_nearest_schatten_commuting_unitary_iff` gives the analogous
criterion for arbitrary ambient unitaries `A`:

```
there exists exactly one nearest P_K-commuting unitary
  iff ([A,P_K] belongs to S_p) and (norm [A,P_K] <= 2 sqrt(p-1)/p).
```

The objectives still use the native extended gauge and compare all
ambient feasible unitaries. Membership is necessary because uniqueness
forces finite cost. That argument is now the generic reusable lemma
`OperatorIdealFamily.gauge_unitary_sub_ne_top_of_unique_correction`,
valid in either scalar field for every accepted ideal gauge. It replaces
the former specialized proof rather than duplicating it. No separability
or rank restriction occurs. Earlier conditional iff statements remain
useful specializations of this mathematical frontier.

Focused build passed (8,058 jobs), and the full default build passed
(21,251 jobs), with warnings treated as errors. The next substantial
unclosed theorem is quantitative near-minimizer stability: control the
distance of an arbitrary almost-minimizing ambient unitary to the full
optimizer set, with explicit dependence on a strict critical-gap margin.
The critical boundary needs its own growth law; a quadratic estimate
must not be assumed there. Connectedness of the fixed-rank multiplicity
strata is an independent next task; local constancy alone does not prove
that these are the connected components.

## Exact critical Schatten phase conditioning

`SchattenCriticalGrowth.lean` proves
`tendsto_critical_phase_quartic_ratio`: for each real `1<p<2`, at
`theta_c = arccos((2-p)/p)`,

```
(F_{p,theta_c}(delta)-F_{p,theta_c}(0)) / delta^4
  -> p (2-p) (2 sin(theta_c/2))^(p-2) / 24   as delta -> 0, delta != 0.
```

`critical_phase_quartic_coefficient_pos` proves that this coefficient is
strictly positive. `critical_phase_quartic_growth` bounds phase excess
above and below by positive multiples of `delta^4` on a positive
feasible neighborhood. `tendsto_critical_phase_quadratic_ratio` and
`critical_phase_no_quadratic_modulus` prove that no positive quadratic
growth coefficient works even locally along feasible nonzero phases.
These statements include the exact critical equality case and use the
actual scalar Schatten power sum already linked to planar singular
values, but do not yet use a norm of the difference of two transporters.

The proof differentiates positive-chord powers, computes the fourth
phase variation as `p (2-p) chord(theta_c)^(p-2)`, and applies the accepted
L'Hopital theorem three times. All derivatives are justified on an actual
neighborhood with positive chords. Symbolic and high-precision numeric
checks agreed with the coefficient before formal proof; those diagnostics
are not evidence in place of the compiled Lean limit. The scalar slope
definition is exposed for reuse, without changing its definition.

Focused build passed (6,670 jobs), and the full default build passed
(21,253 jobs), with warnings treated as errors. The next
step is an exact operator-norm or Frobenius-distance phase formula and
the literal planar Schatten cost-to-distance limit, followed by the
ambient no-quadratic-modulus theorem. No historical-priority claim is
made for this conditioning consequence of the phase-transition theory.

## Critical growth for actual ambient planar transporters

`SchattenCriticalTransportGrowth.lean` proves
`tendsto_critical_planar_transport_quartic_ratio`. For finite `1<p<2`,
`theta=theta_c(p)`, the literal finite Schatten-power cost satisfies

```
( ||I-U_delta||_p^p - ||I-U_0||_p^p ) / ||U_delta-U_0||_op^4
  -> p (2-p) chord(theta_c)^(p-2) / 24    as delta -> 0+.
```

Here every `U_delta` is the actual bundled `scalarPhaseTransport` carrying
the same source line to the same target line. The reusable exact formula
`scalarPhaseTransport_norm_sub` identifies the operator distance between
any two phases with their unit-complex-phase distance;
`scalarPhaseTransport_norm_sub_zero` gives `abs(chord(delta))`.
`scalarPhaseTransport_schattenPower` identifies the literal cost on the
entire feasible phase interval, including endpoints.

`tendsto_critical_planar_transport_quadratic_ratio` makes the corresponding
quadratic quotient tend to zero. The endpoint
`critical_planar_transport_no_quadratic_modulus` states that, for **every**
positive coefficient and **every** positive operator-norm radius, a
feasible nonzero planar unitary transporter lies inside that radius and
violates that quadratic Schatten-**power** growth bound. Consequently
no such bound can hold over all ambient competitors. The canonical
phase's global optimality at equality is supplied separately by the
already compiled exact planar optimality theorem. This does not claim
an unrestricted quartic lower bound for every ambient competitor, nor
does it yet replace the power objective by its `p`-th root in the
conditioning theorem.

Focused build passed (6,842 jobs), and the full default build passed
(21,255 jobs), with warnings treated as errors. The next
useful extension is the original Schatten-norm excess (including its
exact coefficient), and a quantitative lower bound that applies to
every ambient near-minimizer rather than just phase curves.

## Critical conditioning for the original Schatten norm objective

`SchattenCriticalNormGrowth.lean` proves
`tendsto_critical_planar_schatten_norm_quartic_ratio`. For finite
`1<p<2`, actual feasible planar `U_delta`, and `theta=theta_c(p)`,

```
( ||I-U_delta||_p - ||I-U_0||_p ) / ||U_delta-U_0||_op^4
  -> (2-p) 2^(1/p-1) / (24 chord(theta_c))    as delta -> 0+.
```

`critical_schatten_norm_quartic_coefficient_pos` proves strict positivity.
The accepted Mathlib `dslope` identity and continuity at a differentiable
point transfer the power-cost limit through the positive `p`-th root.
This avoids a false nonvanishing assumption on intermediate objective
differences. The proof simplifies the derivative factor using justified
positive-base real-power identities.

`tendsto_critical_planar_schatten_norm_quadratic_ratio` makes the actual
norm-excess quadratic quotient tend to zero, and
`critical_planar_schatten_norm_no_quadratic_modulus` constructs a feasible
nonzero unitary transporter in **every** positive operator-norm
neighborhood violating **every** proposed positive quadratic modulus
for the original norm objective. Thus no certificate
`distance <= C sqrt(objective excess)` can hold uniformly at criticality,
even on one complex principal plane. This is an obstruction to a global
quadratic error estimate, not a claim of an unrestricted quartic lower
bound or of numerical performance. The exact fourth-order law is proved
along the displayed feasible phase curve.

Focused build passed (6,844 jobs), and the full default build passed
(21,257 jobs), with warnings treated as errors. The next
major proof obligation remains a lower growth bound for every ambient
near-minimizer, with constants uniform in Hilbert dimension and explicit
dependence on a strict critical-gap margin. At equality any such theorem
must accommodate the fourth-order obstruction just proved. The
phase-bifurcation amplitude and variation of optimizers under perturbed
projection data outside the canonical regime remain further research targets; neither is implied by
the fixed-pair quartic law.

## Dimension-free data stability, including the critical boundary

`Geometry/Polar/CanonicalStability.lean` proves
`norm_canonicalPolarFactor_sub_le_of_projectionGap_le`: on any complete
complex Hilbert space, for fixed `K` and arbitrary target subspaces `L,M`,
if both source/target projection gaps are at most `gamma < 1`, then

```
||R(K,L)-R(K,M)|| <= projectionGap(L,M) / sqrt(1-gamma^2).
```

There is no compactness, ideal, finite-rank or separability hypothesis in
this geometric theorem. The two-endpoint cosine estimate
`add_mul_norm_canonicalPolarFactor_sub_le_two_mul_projectionGap` permits
unequal cosine lower bounds. `canonical_modulus_coercive_of_gap_sq_add_le_one`
proves the full ambient modulus lower bound, retaining fixed directions.
The pre-polar target-difference identity is exact in operator norm.

`SchattenOptimizerDataStability.lean` transfers these bounds to **every**
actual global optimizer of each native Schatten problem, for finite
`1<p<2`. The two source/target projection differences must belong to `S_p`;
candidate finite cost and separate index balance are conclusions. The
main endpoints are `norm_schatten_minimizers_sub_le_of_projectionGap_le`
and `norm_schatten_minimizers_sub_le_at_closed_critical_gap`.
Throughout the entire closed canonical regime the latter gives

```
||U_L-U_M|| <= (p/(2-p)) * projectionGap(L,M).
```

Thus a target-projection error bound gives an actual optimizer error
bound, independently of Hilbert dimension. The critical equality case
is included: quartic growth of a fixed objective does not prevent
Lipschitz dependence of its unique optimizer on these projection data.
This is a deterministic error certificate, not a numerical-performance
or statistical guarantee. Optimality of the displayed Lipschitz constant
has not yet been formally proved here.

The reusable donor lemmas are
`ContinuousLinearMap.add_mul_norm_sub_unitary_le_two_mul_norm_sub`
(actual unitary factorizations, either scalar field, unequal form lower
bounds) and
`ContinuousLinearMap.mul_norm_sq_le_re_inner_modulus_of_sq_mul_norm_sq_le`
(complex Hilbert modulus coercivity from a squared norm lower bound).
They use accepted Tau Ceti Sylvester and modulus APIs and Mathlib's
operator-monotone square root. The full bounded-polar upstream module
is not needed: importing it alongside the still-unmerged local partial
polar module exposed an existing declaration collision, so the new
factorization lemma imports only its actual Mathlib adjoint dependencies.
No adapter or copied upstream polar implementation was introduced.

Historical boundary: the matrix polar perturbation estimate is classical,
not a novelty claim. An author-hosted primary account verifies the exact
factor `2/(sigma_min(X)+sigma_min(Y))` and attributes it to Li (1995):
[R.-C. Li, Handbook of Linear Algebra, Section 15.3, Fact 3, p.15-8](https://bpb-us-e1.wpmucdn.com/websites.uta.edu/dist/7/5059/files/2021/06/li2007HLA.pdf).
The author-hosted publication list and
[LAPACK Working Note 83](https://www.netlib.org/lapack/lawnspdf/lawn83.pdf)
also corroborate the bibliography. This proof formalizes that mechanism
and applies it to the new exact Schatten optimizer regime; it does not
establish first priority for projection-transport continuity.

Focused build passed (8,080 jobs), and the full default build passed
(21,265 jobs), with warnings treated as errors.
The exact outstanding objective-error lemma is a lower bound of the form
`ofReal(c * ||U-R||^2) + Phi(1-R)^p <= Phi(1-U)^p` for **every** feasible
ambient `U`, with positive `c=c(p,gamma)` under a strict critical-gap
margin. The current global lower bound uses a local-minimum normal form
and cannot simply retain such a residual for an arbitrary competitor.
At critical equality the quadratic version is false, by the preceding
compiled planar obstruction. A dimension-free assertion for the
unpowered norm excess also requires care: adding unchanged positive-cost
blocks dilutes norm excess under the `p`-th root. The power objective is
the natural first target; a formal ambient dilution counterexample is
an independent useful next step.

## Joint source and target error certificates

The data-stability results above now permit **both** projections to vary.
`norm_canonicalPolarFactor_sub_le_of_projectionGaps_le` states

```
||R(K,L)-R(N,M)||
  <= (projectionGap(K,N)+projectionGap(L,M)) / sqrt(1-gamma^2),
```

assuming only the two endpoint gaps `gap(K,L), gap(N,M) <= gamma < 1`.
There is no condition on either intermediate cross pair. The proof
combines the exact one-projection intertwiner norm identities with the
same two-endpoint polar perturbation argument; it does not apply the
canonical bound to an intermediate pair that might not be acute.

`norm_schatten_minimizers_sub_le_of_projectionGaps_le` and
`norm_schatten_minimizers_sub_le_at_closed_critical_gaps` transfer this
to **every** actual optimizer of the two native Schatten problems. The
closed-critical endpoint is

```
||U_(K,L)-U_(N,M)||
  <= (p/(2-p)) * (projectionGap(K,N)+projectionGap(L,M)).
```

Both endpoint projection differences must be native Schatten, finite
`1<p<2`, and both endpoint gaps must be in the closed canonical regime.
No candidate finite-cost, index-balance, separability, or finite-rank
assumption is added. The fixed-source statements are now short
specializations of these general proofs. This supplies a deterministic
optimizer error certificate when both input subspaces are estimated.

Focused build passed (8,080 jobs), and the full default build passed
(21,265 jobs), with warnings treated as errors. The
next concrete correction application is a bound for the nearest
`P`-commuting unitary as its input unitary `A` varies. The expected
`1/sqrt(1-gamma^2)` constant should be obtained from the polar factor of
`PAP+Pperp A Pperp`, not by inserting a cross pair with an unjustified
gap bound. Sharpness of the data constants remains to be formalized.

## Input-error certificate for nearest commuting-unitary correction

`SchattenCorrectionDataStability.lean` proves
`norm_nearest_schatten_corrections_sub_le_of_commutator_norm_le` and
`norm_nearest_schatten_corrections_sub_le_at_closed_critical_commutator`.
For actual global Schatten-nearest `P_K`-commuting unitaries `C,D` for
inputs `A,B`, respectively, with finite `1<p<2`,

```
||C-D|| <= ||A-B|| / sqrt(1-gamma^2)
```

provided both commutators are native Schatten and both commutator norms
are at most `gamma <= sin(theta_c(p))`. The closed-critical endpoint is

```
||C-D|| <= (p/(2-p)) * ||A-B||.
```

All norms in these error inequalities are operator norms. Minimality is
compared against **every ambient commuting unitary** in the native
extended Schatten gauge. There is no finite-candidate-distance,
finite-rank, index-balance or separability assumption; in particular
`A-B` need not itself be Schatten. The existing uniqueness theorem
provides existence and uniqueness in precisely this regime. Thus a
certified operator-norm input error yields a deterministic output error
certificate for optimal commuting-unitary rounding, even at the exact
Schatten transition. This is a data-stability theorem, not an objective-
error certificate for an arbitrary almost-minimizing output.

`Geometry/Polar/CommutingCorrectionStability.lean` proves the actual
diagonal-block identity `diagBlock(A)=S(AK,K) A`, constructs its positive
factor under the canonical correction, and preserves its cosine
coercivity by unitary conjugation. The theorem
`add_mul_norm_canonical_corrections_sub_le_two_mul_norm_sub` retains
unequal endpoint coercivity bounds. The generic donor
`Submodule.norm_diagBlock_le` (and its subtraction form) proves
contractivity of the **accepted upstream** diagonal-block operation
over either scalar field, without dimension or completeness assumptions.
The new proof consumes the upstream block API directly and introduces
no parallel diagonal-block definition or polar implementation.

Focused build passed (8,056 jobs), and the full default build passed
(21,271 jobs), with warnings treated as errors. These are exact
consequences of the compiled Schatten classification and the classical
polar perturbation argument; historical first priority is not claimed.
The most useful next step is an explicit identification with the polar
factor of `diagBlock(A)`, followed by a formally verified two-dimensional
equality example for optimality of the constant.

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

## General operator-ideal membership and `p>=2` ideal attainment

The preceding algebraic route is now compiled in
`Geometry/Polar/DirectRotationIdeal.lean`.
`exists_nonacuteDirectRotation_displacement_factor` proves the literal
bounded factorization `I-R=(P_K-P_L) B` for every completed rotation.
`gauge_nonacuteDirectRotation_ne_top_iff_projection_sub` proves, for
**every accepted operator-ideal family**, that the completed rotation's
displacement has finite gauge iff the projection difference does. Both
fields, arbitrary Hilbert dimension and nonacute defects are included.
No finite-rank or compactness assumption is used in this equivalence.

`CompactDefects.finiteDimensional_crossedDefects_of_compact_projection_sub`
embeds the two crossed defects into the `+1` and `-1` eigenspaces of a
compact projection difference and proves their finite dimensionality.
Thus numeric finrank balance is meaningful for general Schatten pairs,
not only finite-rank pairs.

`SchattenFeasibility.exists_schatten_transport_of_projection_sub_ne_top_of_defect_balance`
constructs a Schatten-displacement transporter from a general Schatten
projection difference and finite defect balance, for every finite `p>=1`
over both fields. This is a sufficient-condition theorem for general
infinite-rank projection differences; its converse is still pending.

`SchattenCanonical.exists_unitary_minimizing_schatten_transport_of_projection_sub_ne_top`
now proves **actual general Schatten-ideal attainment for finite `p>=2`**
in complex Hilbert space: `P_K-P_L in S_p` and finite crossed-defect
balance produce a finite-cost unitary minimizing against every ambient
competitor. The projection difference may have infinite rank and no
separability is assumed. Focused builds passed (7,006; 6,960; 7,600 jobs).

Still open: general compact/ideal necessity of defect balance, exact
general ideal attainment at `1<=p<2`, and the infinite-dimensional
all-optimizer classification. These classical membership/feasibility
lemmas do not independently establish historical novelty; their role is
to justify the claimed ambient scope of the optimization theory.

## General compact and Schatten feasibility iff

`Submodule.finite_crossedDefect_balance_of_compact_transport` now proves
necessity in **general Hilbert dimension with infinite-rank projection
difference**. The actual rectangular projection `P_L|K` is a compact
perturbation of `U|K`, hence Fredholm of index zero by accepted Tau Ceti
theorems. Its kernel and adjoint kernel identify with the two crossed
defects. Their finite dimensionality and equality follow from the
accepted index and cokernel--adjoint-kernel APIs. No separability is used.

`DirectRotationIdeal.compact_transport_iff_compact_projection_sub_and_defect_balance`
therefore gives the full compact restricted-unitary feasibility iff.
`SchattenFeasibility.schatten_transport_iff_projection_sub_ne_top_and_defect_balance`
gives the corresponding **general** Schatten feasibility iff for every
finite real `p>=1`, over both fields: precisely `P_K-P_L in S_p` and
finite crossed-defect balance. The infinite-cost imbalance theorem no
longer needs finite rank of the projection difference.

The superseded finite-rank-only compact target-correction module has
been deleted; its history remains in commit `2408c0867`. The weaker
Schatten sufficiency and finite-rank feasibility declarations have also
been replaced by the general iff, with no compatibility facade. The
separate finite-rank **unitary-group** criterion remains, since it
constructs a finite-rank reference with an explicit rank bound and has
finite-section consumers. Focused general build passed (7,554 jobs).

The central remaining optimization obligation is now sharply isolated:
at `1<=p<2`, a general balanced Schatten pair has a finite-cost canonical
reference and the exact universal angle lower bound, but an attainer
realizing that angle sum in infinite rank has not been constructed.
For `1<p<2` this should be a finite modification on the supercritical
spectral sector; for `p=1` infinitely many nonzero angles can require
modification. Infinite-dimensional all-optimizer classification remains
separate. The feasibility/index mathematics itself is classical.

## Correct infinite-dimensional domain for the smoothed cost

`ContinuousLinearMap.charbonnierCost` is the extended spectral sum of
`sqrt(tau^2+s_n(T)^2)-tau`, with the baseline removed inside each
summand. For every positive `tau`,
`charbonnierCost_ne_top_iff_schatten_two` proves that this sum is finite
**exactly on the Hilbert--Schmidt ideal**, over both fields and in
arbitrary Hilbert dimensions. The two compiled comparison inequalities
bound it above by `Gauge_2(T)^2/(2*tau)` and below by
`Gauge_2(T)^2/(sqrt(tau^2+norm(T)^2)+tau)`, including infinite values.
No duplicate operator-ideal norm is introduced.

`CharbonnierFeasibility.charbonnier_transport_iff_schatten_two_and_defect_balance`
therefore proves the exact finite-cost transport-feasibility criterion:
the projection difference is Hilbert--Schmidt and the finite crossed
defects are balanced. This is **not** a minimum-attainment theorem, and
does not require trace-class projection difference. Focused builds
passed (5,754 and 7,110 jobs). These domain facts are classical analytic
consequences; historical novelty is not asserted.

`CharbonnierLimit.lowerSemicontinuous_charbonnierCost` proves joint
lower semicontinuity in the scale and operator norm. At zero scale,
`charbonnierCost_zero` identifies the cost with the accepted nuclear
gauge. `tendsto_charbonnierCost_zero` proves convergence to that gauge
along **every eventually nonnegative scale tending to zero**, for any
bounded operator, including operators whose nuclear gauge is infinite.
The proof uses lower semicontinuity and the nuclear upper bound, not a
trace-class domination assumption. Thus an operator can have finite
cost at every positive scale while its costs diverge as the scale
vanishes. Focused build passed (5,756 jobs). This is an analytic limit
theorem for the objective; it does not yet justify exchanging a limit
with minimization over an infinite-dimensional transport fiber.

## Universal quantitative ideal comparison

`exists_nonacuteDirectRotation_displacement_factor` has been strengthened
in place: its bounded right factor now has norm at most `sqrt 2`.
The proof estimates `(I+R)` below by `sqrt 2` from unitarity and the
nonnegative real part of the completed rotation. No finite-dimensional
spectral enumeration or compactness is used.

`gauge_nonacuteDirectRotation_le_sqrt_two_mul_projection_sub` bounds
every accepted ideal gauge of `I-R` by `sqrt 2` times the gauge of the
projection difference. Consequently,
`gauge_nonacuteDirectRotation_le_sqrt_two_mul_transport` bounds the
completed rotation by `sqrt 2` times **every ambient transporter**, over
both fields and including infinite costs. This extends the existing
finite acute comparison to arbitrary Hilbert dimension and nonacute
pairs. Focused build passed (7,072 jobs). Existing finite sharpness
witnesses remain in `SharpDisplacement` / `SharpDisplacementLimit`;
the quantitative comparison itself is not a new historical-priority claim.

## Unrestricted Hilbert-space smoothed lower bound and finite-pair attainment

`CharbonnierGlobalLowerBound.sine_smoothedPhaseMinimum_sum_le_transport`
proves the intrinsic extended sum of the **exact smoothed scalar angle
minima** is a lower bound for every complex unitary transporter in
arbitrary Hilbert dimension. No reference, separability, finite-rank,
finite-cost or block-form hypothesis is imposed. Infinite values are
included. The finite-cost branch uses the correct Hilbert--Schmidt
domain. Compact unitary truncation now explicitly gives pointwise
displacement singular-value domination; the smoothed objective decreases
termwise. Finite partial angle sums pass to the limit by operator-norm
continuity, including zero, critical and right angles.

`SmoothedAngleContinuity.continuousOn_smoothedPhaseMinimum_angle`
proves continuity on the closed principal-angle interval by a fixed
compact scalar-phase minimization. `weightedPhaseCost_ge_radial_gap`
and `smoothedPhaseCost_nonneg` justify nonnegativity without excluding
exceptional angles. `CharbonnierFinite` proves exact finite-sum and
orthogonal-zero-extension identities for the native infinite cost.

`CharbonnierFiniteRankAttainment.exists_unitary_minimizing_charbonnier_transport_of_finite_rank_projection_sub`
proves **actual exact attainment against all ambient competitors** when
the projection difference has finite rank and its crossed defects are
balanced. It constructs a finite-rank, finite-cost unitary attaining
the intrinsic angle sum. The source and target subspaces may have
infinite rank and corank, and the ambient space may be nonseparable.
A reference-based version is also compiled. Focused build passed
(7,210 jobs).

This closes the same finite-projection-difference Hilbert-space scope
as the Schatten result for the smoothed penalty. It does not close
general infinite-rank Hilbert--Schmidt attainment or all-optimizer
classification. The targeted literature searches still require a
theorem-level priority review; formal verification is not historical
novelty evidence.

## Hilbert-space commuting-unitary correction applications

`OperatorIdealFamily.gauge_unitary_sub_eq_displacement` identifies the
literal correction distance with relative-unitary displacement in every
accepted ideal family. `gauge_projection_image_sub_eq_commutator`
identifies the actual commutator cost with the image projection gap,
and `gauge_commutator_le_unitary_correction` gives a lower certificate
for every commuting unitary. These statements hold over both fields,
in arbitrary Hilbert dimension, including infinite costs.

`CommutingCorrection.exists_commuting_unitary_with_ideal_certificate`
constructs an actual correction whose distance is between the
commutator gauge and `sqrt 2` times that gauge. It requires an isometric
identification of the image/source crossed defects, allows infinite
defects, and assumes neither compactness nor finite rank.

`SchattenCommutingCorrection.schatten_commuting_correction_iff_commutator_and_defect_balance`
is the exact finite-cost feasibility iff for every finite `p>=1`, over
both fields. A Schatten commutator alone does not remove the pair-index
obstruction. `exists_nearest_schatten_commuting_unitary` gives **actual
global nearest commuting-unitary attainment** in complex Hilbert space
at `p>=2`, assuming commutator membership and finite defect balance.
`exists_nearest_schatten_commuting_unitary_of_commutator_norm_lt_one`
removes the balance hypothesis when the commutator operator norm is
strictly below one: both crossed defects then vanish. Every commuting
ambient competitor is included; no block restriction is present.
Focused build passed (7,560 jobs). No uniqueness or experimental,
physical, or statistical claim follows from these application theorems.

## Additional precise classical precedents checked

Dou--Shi--Cui--Du,
[arXiv:1705.05870v1](https://arxiv.org/html/1705.05870v1), Theorem 3.1
classifies unitaries **simultaneously interchanging** two projections
under crossed-defect balance. Theorem 4.3 gives all completed direct
rotations and attributes their existence criterion to Davis--Kahan
Proposition 3.2. Remark 4.4 describes their uniqueness when both defects
vanish and their defect-unitary freedom otherwise. Theorem 4.5 proves
operator-norm displacement minimality in generic position. These are
exact precedents for the underlying geometry, not new DKPS results.
They do not classify Schatten `1<p<2` displacement minimizers or the
smoothed penalty. Their two-sided interchange constraint must not be
confused with unrestricted one-way unitary equivalence. Historical
priority of the new optimization extensions remains under review.

## Quantitative finite sector for positive-angle phase transitions

`finrank_eigenSpan_mul_cutoff_rpow_le_schatten_rpow` proves for compact
self-adjoint operators over both fields that a spectral band bounded
below by `c>0` satisfies `dim(band)*c^p <= Gauge_p(A)^p`, for every
finite real `p>=1`. The multiplicative extended-valued form avoids
division conventions and needs neither separability nor an ambient
eigenbasis.

`FiniteSpectralCutoff.finite_sine_spectral_cutoff` constructs the actual
band `M = eigenSpan(|P_K-P_L|, (c,infinity))`. It is finite-dimensional,
reduces both projections, and leaves a complementary projection
difference with operator norm at most `c`.
`sine_spectral_cutoff_isReducing_nonacuteDirectRotation` proves that
every completed canonical rotation also reduces this finite band.
`finrank_sine_spectral_cutoff_mul_rpow_le_schatten_projection_sub`
gives the explicit bound
`dim(M)*c^p <= Gauge_p(P_K-P_L)^p`. Focused builds passed (5,786 and
7,088 jobs).

This makes the finite-sector reduction quantitative for every positive
critical angle (Schatten `1<p<2` and positive smoothing scale). It is
not yet the theorem that an optimizer differs from direct rotation by
finite rank: the complementary subcritical trace identity and the
global cost decomposition still need proofs. At `p=1` the critical
angle is zero, so this finite-sector argument cannot be used to assert
finite-rank correction. The nuclear endpoint must be treated separately.

## Actual finite-block phase corrections in an infinite-rank transport fiber

`Submodule.exists_transport_replacing_finite_block` is a reusable
construction over both fields. Given an actual ambient transporter, a
finite source-reducing invariant block, and any transport of the actual
restricted pair, it replaces precisely that block, preserves the
entire complementary action, and bounds the update rank by the block
dimension. No compactness, Schatten or finite ambient dimension is
assumed.

`SchattenFiniteCorrection.exists_schatten_phase_correction_on_finite_block`
constructs exact finite phase optimizers inside an actual balanced
Schatten transport fiber for every finite exponent `p>=1`. It proves
that the ambient corrected unitary retains finite Schatten cost, while
its tail equals the chosen completed canonical rotation.
`exists_schatten_phase_correction_on_sine_cutoff` applies this to every
positive sine cutoff at `1<p<2`: the restriction is globally minimal
among all finite-block transporters, with the native singular-value
power sum as objective. The full update has rank at most the cutoff
dimension. Focused builds passed (6,376 and 7,386 jobs).

**The remaining general attainment obligation is now cost identification,
not feasibility or construction.** For the candidate at the critical
sine cutoff, prove (1) additive spectral cost decomposition across its
finite reducing block and infinite complementary tail, and (2) the
canonical subcritical tail's Schatten power equals the sum of scalar
phase minima of its directed-sine singular values. The already compiled
unrestricted lower bound then certifies global optimality. Exact angle
sum decomposition must also respect multiplicities and zero padding.
These trace identities are not yet Lean-verified here. The cutoff
construction is explicitly **not** presented as a global minimizer.

The accepted decreasing-merge theorem for block singular values is
available in Tau Ceti, but no infinite spectral-penalty sum additivity
API was found in the installed sources. Arbitrary noncompact merges
can hide entries, so an unqualified zero-preserving-penalty additivity
claim would be false. Compact blocks (or correctly justified monotone
penalties) are the appropriate setting. Do not silently extrapolate
the finite-dimensional block-sum theorem.

## Infinite spectral trace and native block-cost additivity

The preceding generic block-sum gap is now closed in the following
precise form. `ContinuousLinearMap.tsum_singularValue_penalty_eq_tsum_eigenspace`
groups the spectral penalty of a compact positive operator by its
positive-eigenvalue multiplicities. It permits **every** nonnegative
zero-preserving penalty, with no continuity, monotonicity or summability
assumption, and handles infinite-dimensional kernels exactly. It uses
the existing compact spectral multiplicity theorem, not an assumed
ambient eigenbasis. `EigenspaceBlockSum` extracts the actual algebraic
eigenspace equivalence from the accepted finite block proof and removes
its finite-ambient restriction; finite multiplicities suffice.

`CompactBlockTrace.tsum_singularValue_penalty_withLpProdMap` proves
exact additive penalty sums for arbitrary **compact rectangular**
orthogonal blocks, over both fields and in arbitrary Hilbert dimensions.
The passage from positive to arbitrary blocks consumes accepted modulus
and block singular-value identities.

`OperatorIdealFamily.gauge_schatten_rpow_withLpProdMap` then proves
**exact native Schatten-power additivity for all bounded rectangular
blocks**, for every finite real `p>=1`, including infinite costs and
without a compactness hypothesis. Infinite-cost cases use accepted
compression dominance, not an invalid noncompact multiplicity count.
`ContinuousLinearMap.charbonnierCost_withLpProdMap` proves the analogous
extended Charbonnier-cost identity at every positive smoothing scale,
again for **all bounded** blocks. Its infinite cases use the correct
Hilbert--Schmidt domain and the native `p=2` block identity.

Focused builds passed (5,544; 5,668; 6,410; 6,510 jobs). These are
classical trace-ideal identities, not independent novelty claims.
Next connect these identities to actual projection-reducing cutoffs
via the canonical orthogonal decomposition. The subcritical tail's
exact scalar-phase trace identification remains a separate obligation
before asserting general `1<p<2` or smoothed attainment.

## Actual reducing trace identities and cost-decreasing phase correction

`ReducingTrace.eq_orthogonal_block_of_isReducing` uses the canonical
orthogonal decomposition to identify an operator with its two actual
compressed blocks, with no dimension or compactness hypothesis.
`singularValue_eq_orthogonal_block_of_isReducing` preserves the entire
native singular sequence. The resulting native Schatten-power and
Charbonnier-cost identities split the **actual** reducing operator,
including infinite values. The compact zero-preserving arbitrary
penalty version is also proved.

`gauge_schatten_unitary_displacement_rpow_eq_block_add_tail` identifies
the full cost of a finite unitary replacement with its new block cost
plus the unchanged reference-tail cost. Both
`SchattenFiniteCorrection` construction theorems have been strengthened
in place with this full ambient cost identity. The sine-cutoff theorem
now also proves that the constructed ambient phase correction **never
increases the full Schatten objective** at `1<p<2`. This follows from
finite-block global optimality and exact tail cancellation; it does
not assume global optimality of the tail. Focused build passed for the
reducing trace API (6,548 jobs) and its strengthened transport consumer
(7,420 jobs).

`Submodule.tsum_sine_penalty_eq_add_of_isReducing` splits every
zero-preserving penalty of the intrinsic directed sine into those of
the actual restricted projection pairs. Compact projection difference,
common reduction, and actual orthogonal projections on the restricted
pairs are explicit hypotheses. Both fields, infinite-dimensional
blocks, kernels and divergent costs are covered. It uses the exact
factorization `(I-P_L)P_K=(P_K-P_L)P_K`, and does not assume an ambient
principal-plane decomposition. Focused build passed (6,560 jobs).

**Updated strongest remaining obstruction:** the block-cost and
intrinsic-angle decompositions above supersede their earlier pending
status. For general balanced Schatten pairs at `1<p<2`, what remains
is the exact scalar-phase trace identity for the canonical
**subcritical infinite tail** (and identification of its compressed
rotation with the canonical rotation of the actual restricted pair).
Together with the constructed optimized finite sector, the two
compiled decompositions and the unrestricted angle lower bound, this
would certify general infinite-rank global attainment. Do not claim
that theorem before the tail identity compiles. At `p=1`, infinitely
many positive angles can need modification, so a separate infinite
phase construction remains necessary. General smoothed attainment,
all-optimizer classification, and unrestricted infinite real matching
remain open beyond the scopes explicitly proved above.

## Canonical restriction and the actual infinite cutoff tail

`LinearIsometryEquiv.exists_restriction_of_reducing` constructs the
actual unitary restriction and inverse on any orthogonally complemented
reducing subspace. It needs neither finite dimension nor ambient
completeness. In infinite dimension, reduction rather than mere
invariance is essential to surjectivity; the proof projects the ambient
inverse image and uses commutation with the subspace projection.

`CanonicalRestriction.nonacuteDirectRotation_diagonal_compressions_isPositive`
proves operator positivity of both canonical diagonal compressions over
both fields. `nonacuteDirectRotation_restriction_eq_canonicalPolarFactor_of_acute`
identifies every actual unitary restriction with the canonical polar
factor of the restricted acute pair. Its hypotheses permit infinite
restricted dimension and arbitrary ambient right-angle completions.
`exists_canonical_restriction_of_acute_reducing_pair` constructs this
restriction with its actual forward and inverse actions.

`CanonicalCutoffTail.exists_canonical_tail_of_finite_sine_cutoff` now
closes the previously pending **geometric** tail obligation. For compact
projection difference and `0<c<1`, the actual complement of the finite
sine sector carries a canonical unitary restriction, and its actual
restricted projection gap is at most `c`. Both fields and nonseparable
fixed directions are included. Completeness supplies the restricted
orthogonal projections; these are not extra mathematical hypotheses.
Focused builds passed (5,174 and 7,096 jobs).

The remaining general Schatten attainment gap is now the **objective**
identity on that subcritical infinite tail. A promising route avoids
building a complete principal-plane enumeration: construct compatible
finite reducing unitary truncations, use the existing finite canonical
cost identity on each actual restricted pair, and pass both inequalities
using lower semicontinuity and nonnegative spectral partial sums. All
historical-novelty claims remain separate from these classical
restriction and polar-uniqueness lemmas.

## Exact canonical spectral cost in infinite rank

`schatten_nonacuteDirectRotation_rpow_eq_canonical_sine_sum` now proves
that the native Schatten displacement power of a completed canonical
rotation is exactly

`∑' j, ENNReal.ofReal (phasePower p.toReal (arcsin (SV_j (K.sinThetaMap L))) 0)`.

The hypotheses are: complex complete Hilbert space of arbitrary dimension,
finite exponent `p>=1`, compact projection difference, uniform acuteness,
and an actual crossed-defect completion. Schatten membership is **not**
assumed: both sides may be infinite. The theorem does not itself assert
canonical optimality below two. The focused build passed (7,396 jobs).

The proof uses `exists_finite_canonical_approximation`, whose finite
supports reduce **both original projections** and retain the actual
canonical rotation. The key commutation is between the source projection
and the displacement **modulus**, rather than the rotation. The native
finite-section cost theorem is
`schatten_canonical_restriction_rpow_eq_sine_sum`; the passage to limits is
`OperatorIdealFamily.gauge_schatten_rpow_eq_tsum_of_dominated_approximation`.
The latter includes divergent costs and requires explicit domination
of both approximating costs. It is not an unjustified exchange of an
infinite sum and a norm limit.

The next proof obligation is now scalar: on a tail of gap at most
`sin (criticalAngle p)`, replace each canonical phase cost by its exact
`phaseMinimum`. Then combine the already compiled actual cost/angle
splittings and finite-block attainer to obtain unrestricted infinite-rank
attainment at `1<p<2`. The nuclear endpoint still requires a separate
infinite modification construction. No historical novelty claim is
made for the classical canonical spectral cost identity.

## General infinite-rank complex attainment is now compiled

The previous subcritical-tail obligation is closed by
`schatten_canonical_cutoff_tail_rpow_eq_phaseMinimum_sum`. The theorem
identifies the actual compressed ambient displacement, rather than
an independently chosen model tail. Its hypotheses are compact
projection difference, `1<p<2`, and `0<c<1` with
`c<=sin (criticalAngle p)`. Infinite tail rank and divergent costs are
allowed in this identity.

`exists_schatten_minimizer_by_finite_correction` now proves global
attainment at every such cutoff. Given a Schatten projection difference
and an actual crossed-defect completion `J`, it constructs an ambient
unitary `U` with all of the following:

- `K.map U.toLinearMap = L`;
- finite native Schatten displacement cost;
- exact power cost equal to the intrinsic ambient `phaseMinimum` sum;
- minimality against **every** ambient complex unitary transporter;
- agreement with `nonacuteDirectRotation K L J` on the entire cutoff tail;
- update rank at most the finite sine-cutoff dimension.

`SchattenPhaseTransition.exists_unitary_minimizing_schatten_transport_of_projection_sub_ne_top`
removes the supplied `J`: native Schatten membership of the projection
difference and equality of its finite crossed-defect dimensions suffice.
It chooses a positive cutoff below the critical sine value. The complex
Hilbert space can be nonseparable and both projections can have infinite
rank and corank. The focused attainment build passed (7,466 jobs).

This is now an **actual unrestricted infinite-rank minimum theorem**,
not only a lower bound, finite-rank-pair theorem, or prescribed-block
optimization. It remains distinct from classifying every infinite-rank
optimizer. The nuclear endpoint, general infinite-rank smoothed
attainment, and unrestricted infinite real matching are not covered.
Historical priority of the exact optimized value and finite-correction
phenomenon still requires theorem-level literature review; Lean verifies
mathematics, not priority. Paper and visualization edits remain delegated
to the separate paper agent at the user's request.

## Consequences: critical finite budget and nearest commuting operators

`exists_schatten_minimizer_with_critical_rank_budget` chooses the **exact**
critical sine cutoff, rather than an arbitrary smaller cutoff. For each
completed direct rotation `R`, it gives a global optimizer `U` and a
natural number `n` with

`rank (R-U) <= n` and
`n * (sin (criticalAngle p))^p <= gauge_p(P_K-P_L)^p`.

The supported sector is the strict sine band above the critical value;
critical eigenspaces are left in the canonical tail. The numerical
budget follows from the compiled cutoff count, with no claim that the
bound is the smallest update rank for every pair.

The native real-exponent declaration
`InfiniteDimensional.exists_unitary_minimizing_schatten_transport_of_projection_sub_ne_top`
now covers **every finite `p>1`**. It has moved from
`SchattenCanonical.lean` into `SchattenGlobalAttainment.lean`; the old
`p>=2`-only existence proof was removed, not retained as a bridge. The
stronger fixed-canonical comparison for `p>=2` stays in its original
module. The earlier handoff paragraph naming `SchattenCanonical` records
that previous checkpoint, not the present declaration's source home or
full scope.

`exists_nearest_schatten_commuting_unitary` and its
`...of_commutator_norm_lt_one` version now cover **every finite `p>1`**,
replacing their former `p>=2` hypotheses. Commutator Schatten membership
and crossed-defect balance yield a global nearest unitary preserving
the prescribed subspace. Operator-norm commutator less than one removes
the balance condition. The comparisons include every ambient commuting
unitary.

`exists_nearest_schatten_commuting_unitary_eq_sine_phaseMinimum_sum`
additionally gives the **exact** nearest-distance power for `1<p<2`,
as the intrinsic angle sum of the image/source pair. This is a literal
operator correction theorem, with neither finite ambient dimension nor
finite-rank commutator assumed. Focused builds passed (7,872 jobs).
These consequences assert no numerical performance, physical
implementability, or statistical guarantee.

The strongest remaining optimizer-classification obligation is to show
that **every** infinite-rank minimizer has the finite active phase data
and canonical inactive action, and to transfer the finite multiplicity
and right-defect parameter classification. The exact infinite-rank
canonical-optimality iff and uniqueness theorem have not yet been
assembled. A useful next seam is an exact canonical cost theorem for an
actual **nonacute finite restriction**: right-angle completion data need
not agree with an independently chosen finite completion, so do not
identify these operators by acute polar uniqueness. Their displacement
Gram operators may instead be compared through the restricted cosine.
The nuclear endpoint and general infinite smoothed attainment need
separate constructions, and the unrestricted real infinite matching
problem remains outside the compiled endpoints here.

A fresh narrow search again found the direct finite-matrix predecessor,
[Bolotnikov--Li--Rodman (2001)](https://journals.uwyo.edu/index.php/ela/article/download/117/117/117),
which explicitly poses the constrained unitary-nearness problem. Negative
search results do not establish priority. The exact optimized Schatten
classification and its ideal extension remain **historically provisional**
pending the broader theorem-level comparison; the completed Lean proof
is independent evidence of correctness, not evidence of historical novelty.

## Infinite optimizer classification: canonical-tail iff and Hilbert gradient

The full classification of **every** infinite-dimensional optimizer is
still pending. The following compiled results now close two precise
parts of its proof rather than assuming that an attaining example
classifies all minimizers.

`exists_schatten_minimizing_finite_restriction` proves that every actual
finite source-reducing sector invariant under a **finite-cost** ambient
global minimizer carries a global minimizer of its restricted pair.
Both scalar fields and arbitrary ambient Hilbert dimension are allowed.
The finite-cost condition permits cancellation of the unchanged tail;
no cancellation of infinite extended costs is used.
`schatten_minimal_iff_restriction_of_minimizing_reference_tail` gives
the corresponding iff when the complementary action agrees with a
known global minimizing reference.

`schatten_minimal_iff_finite_restriction_of_canonical_tail` applies that
iff to every positive subcritical sine cutoff. Its competitor `U` is
explicitly assumed to agree with the chosen ambient completed rotation
on the tail. Unitarity then forces the retained sector to reduce `U`,
using the reference tail's actual inverse. Competing ambient transports
remain unrestricted.

`schatten_minimal_iff_cutoff_phase_and_defect_of_canonical_tail` gives
the full finite compatible phase-projection and reflecting right-defect
parameters of the actual restricted unitary. Repeated, unequal, zero,
critical and right angles retain the existing finite theorem's scope.
This is a classification **within the canonical-tail family**. It does
not prove that every global optimizer belongs to that family. Focused
classification build passed (7,976 jobs).

`SchattenGradientHilbert` proves operator-norm continuity of the phase
gradient on all Hilbert-space unitaries for `p>1`, compatibility with
actual unitary restrictions, and compactness of the gradient whenever
`U-I` is compact. The last proof uses finite unitary approximations,
exact zero extension of their gradients, and closedness of compact
operators. It assumes neither finite dimension nor separability.

`SchattenGradientKernelHilbert` proves the continuous radial factorization
of `U-U*` through the phase gradient for `1<p<2`; the multiplier contains
`|z-1|^(2-p)` and is zero at identity. Hence every vector in the gradient
kernel has identical forward and inverse unitary actions. The theorem
`exists_selfAdjoint_unitary_restriction_schatten_gradient_kernel`
constructs the actual self-adjoint unitary on the full, possibly
infinite kernel. It assumes **no minimality** and therefore retains,
rather than excludes, possible `-1` directions. Focused build passed
(6,754 jobs).

`OperatorIdealFamily.tendsto_gauge_of_tendsto_gauge_sub_zero` supplies
extended ideal-cost continuity, including an infinite limit cost. The
projection exponential formula in `Projection/Exponential.lean` supplies
finite-support phase variations without a global eigenbasis.

The precise missing analytic step is **Hilbert-space constrained
stationarity**: for a finite-cost global minimizer and `1<p<2`, show
`J_K G(U) J_K = -G(U)`, where `G` is the phase gradient. The existing
finite trace-variation theorem alone does not prove it in infinite
dimension. A concrete route is to approximate `U` in Schatten gauge by
finite-rank unitary perturbations; for each rank-one self-adjoint
direction, finite-support phase variations have derivatives given by
`re inner x (G(U(t)) x)`. Gradient continuity on compact parameter sets
provides locally uniform convergence of these derivatives, while ideal
cost continuity gives pointwise convergence of costs. Mathlib's
`hasDerivAt_of_tendstoUniformlyOn` can then transfer the derivative.
Vanishing rank-one variations in `K` and `Kperp` gives stationarity.

Once stationarity is proved, paired nonzero gradient sectors are finite
and source-reducing; the restriction theorem can apply the complete
finite classification on each pair. The kernel reflection still needs
its optimizing `-1` sector excluded. These steps must establish the
canonical inactive action before dropping the explicit tail hypothesis
from the cutoff classification. Paper and visualization files are
unchanged; historical novelty has not been upgraded by these lemmas.

## Hilbert-space stationarity is now compiled

`hasDerivAt_schatten_unitary_rankOne_variation` proves the derivative
of the actual native Schatten displacement power (converted to a real
finite cost) along every unit-vector phase direction, at every real
time. The exponent is any finite `p>1`; the unitary displacement need
only belong to `S_p`. Neither finite rank nor separability is assumed.
The proof passes finite-rank derivatives to the limit using native
ideal convergence and locally uniform gradient pairings, including
crossings through identity. Focused build passed (6,832 jobs).

`gradient_reflection_conjugate_eq_neg_of_schatten_minimal` now proves
`J_K * G(U) * J_K = -G(U)` for every finite-cost global minimizer on an
arbitrary complex Hilbert space, at every finite `p>1`. Rank-one feasible
variations give the two vanishing diagonal quadratic forms;
self-adjoint polarization proves that both diagonal compressions vanish.
Only the finite-cost variation curves are converted to real costs: the
argument does **not** reinterpret infinite extended cost as a real zero.
Focused stationarity build passed (6,838 jobs).

Correction to the earlier proposed kernel step: an optimizing right-angle
reflection legitimately has eigenvalue `-1`. The classification must
retain and classify this finite reflecting defect sector. It must not
exclude every `-1` direction. The proved kernel theorem deliberately
allows them. Stationarity makes the full gradient kernel source-reducing;
its compact-displacement self-adjoint unitary action has a finite
negative sector. Saturating that sector under the source projection
isolates a finite reducing reflection block, with fixed complement.
The finite optimizer classification should then identify its right-angle
and fixed geometry.

The next exact obligation is now geometric/spectral rather than
variational: use stationarity to prove that each positive gradient-modulus
cutoff is a finite common reducing block of the projection pair and
transporter. Its actual restriction is optimal by the restriction theorem
and hence has the compiled finite phase/defect normal form. Assemble
these restrictions with the finite reflecting kernel sector to force
canonical action on all inactive principal-angle sectors. Only then can
the explicit tail hypothesis be removed from the cutoff classification.
The unrestricted every-optimizer iff is still not claimed.

## Every optimizer now has classified finite gradient sectors

`exists_minimizing_restriction_on_gradient_cutoff` proves that for every
finite-cost global optimizer at any finite `p>1` and every `eps>0`, the
actual sector `eigenSpan |G(U)| (Ioi eps)` is finite-dimensional, reduces
both projections and `U`, and carries the actual forward/inverse unitary
restriction. That restriction minimizes against every finite unitary
transporter of its restricted pair. The gradient on the complementary
sector has norm at most `eps`. This bounds the **gradient** tail, not
the displacement tail; near `-1` they are different.

`exists_phase_and_defect_on_gradient_cutoff_of_schatten_minimal` gives
the complete compatible finite phase-projection/right-defect data on
all these sectors for `1<p<2`. These are unconditional necessary
statements about every ambient optimizer: no supplied block invariance,
cosine commutation, canonical-tail action, or finite ambient dimension.
Focused build passed (7,526 jobs).

The reusable field-general algebraic lemma
`commute_starProjection_modulus_of_reflection_conjugate_eq_neg` proves
that reflection-odd self-adjoint operators have modulus commuting with
the source projection. Applying it to the proved stationarity identity
makes the finite gradient cutoffs source-reducing; actual restriction
and transport then give target reduction and finite optimality.

Remaining assembly obligation: isolate a finite source-reducing support
of the negative part of the zero-gradient kernel reflection, classify
that actual block by finite optimality, and retain identity on its fixed
complement. Then combine the classified gradient sectors with the kernel
sector to force canonical inactive action. The positive-gradient normal
forms alone are not yet the unrestricted every-optimizer iff.


## The complete zero-gradient kernel now has a finite optimizing support

`exists_finite_reflecting_support_on_gradient_kernel_of_schatten_minimal`
now proves that every finite-cost complex Schatten optimizer (`1<p<2`)
has an actual self-adjoint unitary restriction on its entire gradient
kernel. This restriction is globally optimal among **all** transporters
of the restricted pair. Its displacement is finite rank. Saturating the
displacement range by the source projection produces a finite reducing
support carrying a finite global optimizer; the rest of the full kernel
is fixed pointwise. No separability or finite kernel dimension is assumed.
The kernel core's finite optimality invokes the complete finite
phase/defect classification without excluding legitimate `-1` directions.
Focused build passed (7,534 jobs).

Reusable ingredients: `exists_schatten_minimizing_reducing_restriction`
now treats arbitrary infinite reducing blocks using exact finite-cost
tail cancellation; `exists_transport_replacing_reducing_block` gives
actual arbitrary-block replacements. The finite versions specialize
these statements and retain their weaker invariance hypotheses.
`exists_rank_displacement_le_of_isSelfAdjoint` uses accepted Tau Ceti
compact-eigenspace finiteness at eigenvalue `2`.

Next assembly: positive gradient cutoffs and the reflection kernel
exhaust the Hilbert space. Prove sine-angle commutation globally using
finite optimizer commutation on positive cutoffs and the existing
`commute_sinAngleOperator_of_selfAdjoint_transport` on the kernel.
Then positive sine cutoffs are finite actual minimizing restrictions;
zero-angle directions are fixed by restriction optimality. Finite
canonical uniqueness on subcritical sine bands should force canonical
action on the infinite inactive tail. The final unconditional
canonical-tail/finite-phase iff remains open; do not report it as proved.
Paper and visualization files remain untouched.


## Every complex infinite-dimensional optimizer is now classified (`1<p<2`)

The final assembly is compiled. The earlier open assembly obligations in
this chronological record are superseded by these results:

- `commute_sinAngleOperator_of_schatten_minimal`: every finite-cost
  global optimizer commutes with the intrinsic principal-sine operator.
  Unequal angles cannot mix, including zero and right-angle spaces.
- `eq_canonicalPolarFactor_of_schatten_minimal_of_gap_le_critical`:
  canonical uniqueness in arbitrary Hilbert dimension whenever the
  projection gap is at most `sin (criticalAngle p)`. The threshold is
  closed, including all repeated and zero-angle directions.
- `apply_eq_nonacuteDirectRotation_on_inactive_tail_of_schatten_minimal`:
  every global optimizer is canonical on the full complement of any
  strict sine cutoff `Ioi c`, where `0<c<1` and `c≤sin(criticalAngle p)`.
  This is now a conclusion; no supplied tail or block assumption remains.
- `schatten_transport_isMin_iff_canonical_tail_phase_and_defect_complex`:
  the complete iff for **every ambient unitary transporter**, including
  competitors of infinite cost. Hypotheses: complex complete Hilbert
  space (no separability needed), finite `1<p<2`, native Schatten
  projection difference, and an actual crossed-defect unitary completion.
  Optimality is equivalent to canonical inactive-tail action plus the
  explicit compatible finite phase-projection / reflecting right-defect
  normal form. The candidate is **not** assumed to have finite cost;
  both directions prove the required finiteness. At the exact critical
  sine cutoff all nonuniqueness is confined to a finite strictly active
  sector. The finite theorem covers all angle multiplicities and
  endpoint degeneracies. Focused classification build: 8,016 jobs.

The proof uses the full kernel and all finite positive-gradient cutoffs
to establish sine commutation by compact spectral completeness, then
switches to the intrinsic sine cutoffs. Infinite reducing restriction
optimality and finite canonical uniqueness identify the infinite
inactive tail. The general sine restriction theorem now works for
arbitrary orthogonally complemented common reducing subspaces, rather
than requiring finite ambient dimension. Common source and common
orthogonal directions are fixed, using a field-general restriction
lemma valid at every real finite exponent `p≥1` once sine commutation
is known.

This closes the unrestricted complex **Schatten `1<p<2` optimizer-set**
classification under the stated ideal/index feasibility assumptions.
It does not classify nuclear, Charbonnier, real orthogonal, or all
`p≥2` equality cases. It does not by itself formalize the topology or
dimensions of the resulting parameter spaces, or prove historical
novelty. The manuscript and visualizations remain assigned to another
agent and have not been edited. Next useful consequences: every-optimizer
critical rank budget (previously only an attaining optimizer had this
certificate), intrinsic uniqueness iff the strict active sector is
empty, and a topology/dimension theorem after removing redundant
finite phase parameters.


## Every-optimizer rank certificate and build checkpoint

The complete classification was committed as `aeb6384f1` after a full
default build passed all 21,233 jobs with warnings treated as errors.

`schatten_minimizer_has_critical_rank_budget` strengthens the older
existence-only rank certificate to **every** global optimizer. Write
`c=sin(criticalAngle p)` and `M=eigenSpan |P-Q| (Ioi c)`. For every
optimizer `U` and every completed direct rotation `R`,

```
rank(R-U) ≤ finrank M,
(finrank M) * c^p ≤ gauge_p(P-Q)^p.
```

The operator update is supported on the same intrinsic strictly active
sector for every optimizer. No finite-cost hypothesis is imposed on
`U`; comparison with the existing finite-cost attaining transporter
proves it. Focused rank build passed (8,018 jobs).

The finite multiplicity and parameter-topology results already exist in
`SchattenMultiplicityParameters.lean` and `SchattenParameterTopology.lean`.
An infinite optimizer-space homeomorphism and corresponding compactness
and multiplicity-space topology can now be obtained by identifying this
fixed finite core with the complete ambient optimizer set. That
homeomorphism has **not** yet been formalized. The next proof should use
the continuous orthogonal extension and actual compression inverse,
then compose the existing finite parameter homeomorphisms; no new
variational argument is needed. Nuclear / smoothed / real classification
and `p≥2` equality cases remain distinct workstreams.


## Every nearest commuting correction and its commutator certificates

`SchattenCorrectionClassification.schatten_correction_isMin_iff_canonical_tail_phase_and_defect_complex`
now transfers the complete arbitrary-Hilbert-space `1<p<2` optimizer
classification to **every** nearest unitary commuting with a prescribed
orthogonal projection. Assumptions: native Schatten commutator and an
actual image/source crossed-defect completion; all ambient commuting
unitaries are competitors. Neither finite candidate distance nor angle
block preservation is assumed. The relative correction has canonical
inactive action and precisely the finite compatible phase/reflection data.

`schatten_nearest_commuting_unitary_has_critical_rank_budget` proves
`rank(R*A-C) ≤ dim M` for **every** nearest correction `C`, with
`dim M * sin(criticalAngle p)^p ≤ gauge_p([A,P])^p`. Here `R` is any
completed canonical image/source rotation and `M` is the same intrinsic
strictly active sector for all corrections. This is a certificate for the
additional optimization beyond the canonical correction, not a claim
that the complete correction of the input has finite rank.

`SchattenCorrectionUniqueness.exists_unique_nearest_schatten_commuting_unitary_of_commutator_le_critical`
gives a directly checkable sufficient condition for unique optimal
correction, without a separate index hypothesis:
`[A,P] ∈ S_p` and `norm([A,P]) ≤ sin(criticalAngle p)`.
The accompanying equality theorem identifies **every** nearest correction
with `canonicalPolarFactor(AK,K) * A`. The closed threshold includes
critical, repeated and zero angles and arbitrary fixed ambient directions.
The existing `sin_criticalAngle` lemma supplies the algebraic form
`2*sqrt(p-1)/p`. It was moved unchanged from `SchattenCommutatorCutoff`
to the earlier scalar `SchattenPhaseCriticalAngle` module, preserving
its name and stronger `p>1` scope so infinite consumers need no finite
optimizer-theory import. No duplicate identity is retained.
These results do not yet assert a necessary-and-sufficient uniqueness
criterion in infinite dimension. Focused application build: 8,030 jobs.

The reusable native ideal-gauge comparison equivalence
`OperatorIdealFamily.gauge_correction_isMin_iff_transport_isMin` works
over both scalar fields in arbitrary complete Hilbert dimension, for
every accepted ideal gauge including infinite costs. The correspondence
is classical: no independent historical novelty is claimed for the
change of variables or for these application corollaries. No empirical,
numerical-performance or physical-implementation guarantee is inferred.
The manuscript and visualizations remain untouched.


## Two-level self-adjoint symmetry correction: compiled application

Checkpoint `ddbef2d43` contains the nearest-correction classification,
closed-threshold uniqueness and every-correction commutator rank budget.
Its full default build passed 21,239 jobs with warnings as errors.

`TwoLevelSymmetryCorrection.exists_unique_nearest_schatten_two_level_symmetry`
now proves the following deterministic operator theorem on every complete
complex Hilbert space. For a closed subspace projection `P`, real
`energy` and positive `gap`, let `H = gap * P + energy * I`.
For finite `1<p<2`, if `[A,H] ∈ S_p` and

```
norm([A,H]) ≤ gap * (2*sqrt(p-1)/p),
```

then `H` is self-adjoint and there is a unique Schatten-nearest ambient
unitary commuting exactly with `H`. All ambient exact unitary symmetries
are competitors, including those at infinite distance. The projection
may have infinite rank and corank; even trivial eigenspaces are allowed.
No independent defect-index assumption is needed. Focused build: 8,032 jobs.

The proof is explicit: `[B,H]=gap*[B,P]`, so the commutants coincide.
The inverse-gap scalar identity transfers native Schatten membership;
the same identity in operator norm transfers the residual bound to the
closed projection-commutator threshold. The already proved arbitrary-
Hilbert-space nearest-correction theorem then supplies existence and
uniqueness. This is an exact nearness consequence, not a claim of physical
implementability, a numerical algorithm with certified floating-point
input, or independent historical novelty for two-level symmetry rounding.
The manuscript and visualization files were not edited.

The supplied expanded historical review is now recorded at the top of
`papers/dk_formalization_journal/MATHEMATICAL_NOVELTY_REVIEW_2026-10-24.md`
(commit `4cdd5ed01`), including source-specific distinctions, precise
priority limitations, and the corrected infinite-dimensional frontier.
The author-hosted Appendix B PDF lead returned HTTP 503 in this pass;
printed-edition authentication remains pending. No authors were contacted.

Next substantive obligations for the active broader campaign: (1) the
infinite optimizer-space compression/extension homeomorphism, composing
the existing finite multiplicity homeomorphisms; (2) necessity, as well as
sufficiency, of the infinite-dimensional uniqueness threshold; (3)
quantitative stability and certified approximation from inexact spectral
input. All are distinct from the now closed every-optimizer and
nearest-correction classification. The nuclear, real infinite-dimensional
and full infinite Charbonnier classifications remain separate research
streams. Do not infer these endpoints from the complex `1<p<2` results.


## Infinite optimizer topology: finite cutoff homeomorphism and compactness

`SchattenOptimizerTopology.exists_schatten_finite_cutoff_optimizer_homeomorph`
proves that the full native Schatten optimizer set on any complete complex
Hilbert space is homeomorphic, in the accepted operator-norm topology, to
the actual finite optimizer set on `eigenSpan |P-Q| (Ioi c)`. Assumptions:
finite `1<p<2`, native Schatten projection difference, an actual balanced
crossed-defect completion, `0<c<1` and `c≤sin(criticalAngle p)`.
The theorem proves the restricted source/target rank balance, actual head
action, canonical complementary action, and exact equality of operator-
norm differences between ambient and restricted optimizer pairs. All
ambient optimizers are included; finite cost and block preservation are
not baked into the new native set `schattenHilbertTransportMinimizers`.

`isCompact_schattenHilbertTransportMinimizers` consequently proves compactness
of the **entire** optimizer family in operator norm, even for infinite-rank
pairs and nonseparable fixed directions. This is compactness of the exact
optimizer set for fixed data. It does not assert compactness of arbitrary
near-minimizing sequences or continuity under varying projection data.
Focused topology build passed (8,038 jobs), with warnings as errors.

The reusable field-general `LinearIsometryEquiv.exists_reference_tail_homeomorph`
works for arbitrary orthogonally complemented reducing sectors, even when
both sectors are infinite-dimensional. It supplies actual restriction and
extension coordinates and exact operator difference norms. The accepted
Tau Ceti operator-norm topology is used directly. Orthogonal zero extension
norm equality is obtained from the existing singular-value identity at zero.
The existing private finite-head/ideal-tail cost lemma was moved into
`ContinuousLinearMap.gauge_schatten_displacement_ne_top_of_finite_restriction_and_ideal_tail`
and generalized over both fields; the optimizer classification consumes it
without retaining a duplicate. The finite optimizer set now has its direct
membership simplification lemma for downstream use.

Next unblocked step: compose this exact finite-cutoff homeomorphism with
`exists_schatten_multiplicity_parameter_homeomorph`. This should transfer
independent projection factors and crossed-defect coordinates, locally
constant rank labels and positive separation of distinct rank sectors to
the full infinite-dimensional optimizer family. Formal Grassmannian
connected components and manifold dimensions remain separate obligations.
No first-publication priority is inferred from these topological consequences.
The manuscript and visualizations remain untouched.


## Full Hilbert multiplicity topology, rank labels and exact isolated counts

Checkpoint `39261e8a2` contains the exact finite-cutoff homeomorphism and
operator-norm compactness, after a full 21,245-job default build.

`SchattenMultiplicityTopology.exists_schatten_hilbert_multiplicity_parameter_homeomorph`
now proves the unconditional existence of an operator-norm homeomorphism
from the product of the actual finite active canonical multiplicity
projection factors and the finite crossed-defect unitary factor to the
**entire** native Hilbert-space optimizer set. Hypotheses are exactly the
proved complex `1<p<2` ideal/index assumptions, with any `0<c<1` below or
at the critical sine. The finite restricted source/target rank equality
is proved, not supplied. All repeated, zero, critical, right and arbitrary
fixed ambient directions retain their established scope. No finite-rank
projection-pair or separability assumption is added.

`exists_schatten_hilbert_multiplicity_coordinates_of_homeomorph` transfers
both locally constant projection-rank labels and uniform fixed-pair positive
operator-norm separation of different rank labels. Its inputs are exactly
the finite optimizer homeomorphism and difference-norm identity supplied
by the preceding cutoff theorem. It is stated as a reusable transfer
between an arbitrary finite optimizer carrier and the full Hilbert optimizer
set. The unconditional coordinate theorem constructs its homeomorphism
through this transfer. Thus the label and separation statements require
no additional geometric hypothesis about the infinite-dimensional pair.

`schatten_hilbert_optimizer_count_and_discrete_of_simple_active_angles`
proves the exact count `Nat.card(all ambient optimizers) = 2^s` and
discreteness of the operator-norm optimizer topology whenever the finite
active canonical multiplicity factors have dimension one and the right
defect is zero. Here `s` is the number of distinct active rotation angles.
Infinite inactive multiplicities are unrestricted. Focused module build:
8,040 jobs with warnings as errors.

Implementation note: keeping the nested dependent coordinate types folded
is necessary in this proof. Eager `dsimp only` on the full coordinate
signature produced an internal free-variable error; introducing a
reusable composition theorem and preserving the dependent lets compiles
without disabling linters or increasing heartbeat limits. This does not
alter the mathematical scope. The previous chronological statements
calling infinite multiplicity homeomorphisms open are superseded.

Exact remaining mathematical obligations: (1) prove the converse of the
infinite uniqueness threshold, using the finite optimizer homeomorphism
and the finite canonical/uniqueness iff, then reassemble the projection
gap from its two reducing blocks; (2) prove connectedness and manifold
dimension of the rank-stratified projection factors to obtain component
counts and dimensions; (3) obtain quantitative near-minimizer or varying-
data stability and certified approximation. Compactness and rank separation
here concern exact optimizers of fixed data and do not imply those stronger
stability assertions. No new historical-priority claim is made. The paper
and visualization files remain assigned separately and unchanged.

## Infinite Charbonnier closed-threshold rigidity and canonical tails

The native finite-cost complex Charbonnier theory now includes
`eq_canonicalPolarFactor_of_charbonnier_minimal_of_gap_le_critical_complex` and
`apply_eq_nonacuteDirectRotation_on_inactive_tail_of_charbonnier_minimal_complex`.
The first proves canonical uniqueness through the closed critical gap;
the second proves canonical action on the entire complementary sine-cutoff
tail of every global optimizer. Both hold on arbitrary complete complex
Hilbert spaces, without separability or finite-rank assumptions. The
stationarity and angle-preservation theorems supply the reducing structure;
it is not imposed on the optimizer. Compact spectral completeness includes
the whole zero-angle kernel. Finite native cost remains an essential
hypothesis; the extended all-infinite-cost problem has different optimizers.

The tail statement assumes native Hilbert--Schmidt projection difference,
an actual crossed-defect isometry, and any positive cutoff below one and
at most the critical sine. Its restricted native finiteness is proved by
Hilbert--Schmidt compression and the quadratic Charbonnier ideal equivalence,
without treating Charbonnier cost itself as an ideal norm. Focused builds
passed (7,364 and 7,366 jobs respectively). Next: combine tail necessity,
finite-block cost additivity and the finite phase/defect iff to classify
every infinite-dimensional optimizer under the finite-cost feasibility
conditions. Historical novelty remains a separate priority question.

## Complete infinite Charbonnier optimizer iff and uniform correction rank

`CharbonnierOptimizerClassification.charbonnier_transport_isMin_iff_canonical_tail_phase_and_defect_complex`
now classifies every ambient minimizing complex unitary, without candidate
finite-cost, separability, finite-rank-pair or prescribed-block assumptions.
For positive smoothing scale, native Hilbert--Schmidt projection difference,
an actual crossed-defect equivalence, and any cutoff in `(0,1)` below or at
the critical sine, the iff requires exactly canonical complementary action
and a finite actual restriction satisfying the complete finite smoothed
phase/defect formula. The relative factor is `R.trans V.symm`; the phase
factor is the weighted factor with weights `smoothingRadius tau` and its
inverse. The actual right-defect equivalence is unique for each optimizer;
the phase projection vanishes on the cosine kernel. Unequal, repeated,
zero, critical and right principal angles retain the finite theorem's scope.

`charbonnier_minimal_iff_canonical_tail_finite_minimal_complex` gives the
underlying exact unrestricted finite reduction. The reusable either-field
`TauCeti.charbonnier_minimal_iff_restriction_of_minimizing_reference_tail`
proves equivalence by native trace additivity and finite-tail cancellation.

`CharbonnierOptimizerRank.charbonnier_minimizer_has_critical_rank_budget_complex`
proves, for **every** global optimizer U and every completed rotation R,
`rank(R-U) <= dim M` for the strictly supercritical sine sector M, with
`dim M * sin(theta_c)^2 <= ||P-Q||_HS^2`. Thus only a uniformly bounded
finite-dimensional sector can change; the critical sector is canonical.
Focused classification and rank builds passed (7,438 and 7,440 jobs).

The complementary regime is separately explicit in
`charbonnier_all_transport_costs_eq_top_iff` and
`charbonnier_minimal_of_infinite_cost_regime`: if HS membership fails or
crossed-defect finranks differ, every feasible ambient transporter has
cost infinity and is an extended-cost global minimizer. The universal
cost statement allows an empty fiber; the optimizer statement requires
an actual feasible transporter. No stationarity or finite-block
classification is asserted in this regime. Both results are field-generic.

Next unblocked consequences: establish an operator-norm homeomorphism
between the full Hilbert optimizer family and its finite cutoff family,
then transfer compactness, exact uniqueness iff, and multiplicity topology.
The previous paragraphs marking the full smoothed optimizer iff open are
superseded. Historical priority is not inferred from formal verification.
The paper and visualization files remain untouched.

## October 27: full Charbonnier optimizer topology and exact uniqueness

`CharbonnierOptimizerTopology.exists_charbonnier_finite_cutoff_optimizer_homeomorph_complex`
identifies the entire ambient Hilbert optimizer family with the actual
finite active-cutoff optimizer family, by an operator-norm homeomorphism
that preserves pairwise operator-norm differences exactly. Its hypotheses
are the positive-scale HS projection difference and actual defect equivalence,
with any positive cutoff below one and at most the critical sine.
`isCompact_charbonnierHilbertTransportMinimizers_complex` proves operator-norm
compactness of the full family, with all multiplicities and defects.

`CharbonnierUniquenessThreshold.charbonnierHilbertTransport_unique_minimizer_iff_complex`
removes **all** standing compactness, ideal-membership and index assumptions:
for any orthogonally complemented pair on a complete complex Hilbert space,
there is exactly one native-cost global minimizing ambient unitary iff
`P-Q` is Hilbert--Schmidt and the full projection gap is at most
`sin(smoothedCriticalAngle tau)`. Equality at the threshold is included.
The gap bound automatically eliminates crossed defects. The preliminary
`..._iff_projectionGap_of_defectEquiv` transfers finite uniqueness through
the cutoff homeomorphism and recovers the entire gap by a reducing norm
maximum, rather than assuming that finite cutoffs exhaust operator norm.

The reusable either-field
`TauCeti.charbonnierCost_displacement_ne_top_of_unique_transport`
proves unique optimality forces finite cost even without projection or
compactness assumptions: otherwise a transporter and its composition
with negation both minimize; uniqueness forces the ambient space to be
zero, contradicting infinite cost. This also covers the zero-space edge.
These are native extended-objective statements, not only ideal-restricted
competitor statements. The paper and visualizations remain untouched.

## October 27: full smoothed multiplicity topology and exact isolated counts

`CharbonnierMultiplicityTopology.exists_charbonnier_hilbert_multiplicity_parameter_homeomorph_complex`
identifies the entire Hilbert optimizer family with the product of one
orthogonal-projection factor on each actual finite active canonical
multiplicity space and an independent finite crossed-defect unitary factor.
This includes possible mixing within equal-angle sectors; unequal angles
retain the proved no-mixing constraint. The index and multiplicity spaces
are the finite weighted-rotation ones with weights `smoothingRadius tau`
and its inverse. No principal frame is prescribed to ambient competitors.

`exists_charbonnier_hilbert_multiplicity_coordinates_of_homeomorph_complex`
transfers locally constant projection-rank labels and a uniform positive
operator-norm separation of different rank labels, for fixed pair and
positive smoothing scale. The preceding unconditional homeomorphism
supplies its exact norm-preserving transfer input. These results do not
imply near-minimizer coercivity or varying-data stability.

`charbonnier_hilbert_optimizer_count_and_discrete_of_simple_active_angles_complex`
proves exactly `2^s` ambient global optimizers and discreteness of their
operator-norm topology when all active multiplicity factors have dimension
one and there is no right-angle defect. Infinite inactive multiplicities
are unrestricted. Focused build passed (7,478 jobs). Formal connected
components and manifold dimensions of higher-rank projection factors
remain separate obligations; no such dimension assertion is implied here.
Next independent application: transfer native Charbonnier transport to
nearest projection-commuting unitaries, with an unconditional HS commutator
and critical norm uniqueness certificate. No historical novelty claim is
inferred from the transfer or the existing finite topology.

## October 27: native smoothed projection-symmetry correction

`CharbonnierCommutingCorrection.existsUnique_nearest_charbonnier_commuting_unitary_iff_complex`
proves, for an arbitrary unitary A and orthogonally complemented K on any
complete complex Hilbert space, that a unique Charbonnier-nearest unitary
commuting with P_K exists iff `[A,P_K]` is Hilbert--Schmidt and its operator
norm is at most the smoothed critical sine. No standing compactness,
candidate finite-distance, rank-balance or separability hypothesis is used.
`eq_canonical_correction_of_charbonnier_minimal_of_commutator_le_critical_complex`
identifies **every** minimizing correction under that certificate as
`canonicalPolarFactor(AK,K) * A`.

`exists_nearest_charbonnier_commuting_unitary_complex` gives exact finite-cost
attainment and the full intrinsic minimum sum for a Hilbert--Schmidt
commutator and balanced image/source crossed defects. Its competitors are
all ambient commuting unitaries. The balance hypothesis matters above the
critical gap; it is automatically eliminated by the small-gap certificate.
`charbonnier_nearest_commuting_unitary_has_critical_rank_budget_complex`
proves every nearest correction differs from each completed canonical
correction by rank at most the actual strictly-supercritical sine-sector
dimension, with the dimension controlled by the squared HS commutator
gauge divided by the squared critical sine.

The reusable field-generic donor
`ForTauCeti/Analysis/InnerProductSpace/Projection/CharbonnierCorrection.lean`
proves invariance of native smoothed trace under arbitrary isometric
changes of domain/codomain, exact equality of correction and relative
transport cost, and both minimality and unique-minimality correspondences.
The cost keeps extended values; it is never treated as an operator-ideal
norm. The approximation-number isometry theorem is consumed directly
from accepted TauCeti. These approximation consequences make no assertion
about computational performance, physical realizability or noisy data.

Next consequential research seam: infinite-dimensional local minima.
The global optimizer iff is proved, but the new stationarity and reducing
restriction endpoints currently assume global minimality. To prove that
finite-cost local minima are global, one must first descend **local**
minimality to actual finite reducing sectors (with a stated operator-norm
or ideal topology), including the zero-gradient reflection kernel, then
use finite landscape rigidity and native trace limits. The existing
global restriction lemma alone does not discharge this obligation.
Infinite nuclear and real full-optimizer classifications remain separate
open extensions; the positive critical sine used here is unavailable at
the nuclear endpoint. Higher-rank projection-factor connectedness and
manifold dimensions, and dimension-independent near-minimizer estimates,
are also not claimed. Paper and visualization updates remain external.

## Final API scope and validation boundary

All newly introduced fixed-complex-field theorem names in this wave now
carry `_complex`, including the closed-threshold rigidity, canonical-tail,
rank, topology, multiplicity and exact uniqueness endpoints. The generic
either-field cost, feasibility and correction-transfer lemmas retain their
unqualified names. Consumers and the preceding handoff references were
updated together; a whole-repository exact-name search found no remaining
references to the former theorem names. No paper census claims or existing
Challenge endpoints depended on the renamed declarations.

Focused renamed-consumer build passed (7,490 jobs). The required static
name-drift script still reports the same 23 pre-existing findings involving
historical migration destinations or accepted upstream APIs, with no new
Charbonnier or smoothed names among its findings. This scanner failure is
not being presented as a passing check; compiler validation of the default
and separate Challenge targets is the independent evidence. No scanner
logic or unrelated migration records were changed.

Final compiler evidence after the scope renames: full default `lake build`
passed 21,321 jobs (`/tmp/charbonnier-final-full.log`); the separately required
`lake build Challenge` passed 19,755 jobs
(`/tmp/charbonnier-final-challenge.log`). Both were preceded by
`lake exe cache get`. The static-scanner caveat above remains unchanged.

## October 27: local restriction and native local stationarity

`TauCeti.exists_charbonnier_locally_minimizing_reducing_restriction`
now descends native finite-cost local optimality in operator norm to an
actual reducing sector, over either scalar field. Both retained and
complementary sectors may be infinite-dimensional. The actual restricted
unitary is feasible, has finite native cost, and is locally minimizing;
continuous fixed-tail extension and finite tail cancellation prove this.
`exists_charbonnier_locally_minimizing_finite_restriction` needs only
forward invariance on a finite source-reducing sector.

`CharbonnierStationarity.gradient_reflection_conjugate_eq_neg_of_charbonnier_isLocalMinOn_complex`
now proves the ambient constrained stationarity identity for finite-cost
operator-norm **local** minima. Native rank-one variations remain finite
for every parameter, so converting the local ENNReal inequality to real
first variation is justified. No continuity of the infinite native cost
in operator norm is assumed. The existing global stationarity APIs now
specialize the stronger local theorems; the underlying proofs are not
duplicated. Focused local restriction/stationarity build passed 6,922 jobs.

The whole infinite local-to-global theorem is not yet proved at this
checkpoint. Next: transfer native finite-sector local optimality to the
finite CLM landscape theorem, prove local optimizers preserve the sine
operator using positive gradient cutoffs and the whole gradient kernel,
and establish canonical zero/closed-subcritical action before applying
the complete global optimizer iff. The topology is operator norm, not
an unspecified Schatten topology. Paper and visualization files untouched.

## Native finite landscape transfer and local angle preservation

`SmoothedNativeLocalGlobal.smoothed_isMin_of_charbonnier_isLocalMinOn_complex`
and `charbonnier_isMin_of_isLocalMinOn_finite_complex` connect actual
operator-norm unitary local minima of the native extended trace to the
complete finite real landscape theorem, including all angle endpoints.
The proof uses the accepted operator-norm embedding and its exact
`map_nhdsWithin_eq`, plus the nonnegative finite cost identity. Giving the
implicit competitor explicitly in the final `IsMinOn` application avoids
expansion of singular-value constructions during representation inference;
no heartbeat increase was needed.

`CharbonnierGradientCutoff.exists_charbonnier_minimizing_restriction_on_gradient_cutoff_of_isLocalMinOn_complex`
now extracts an actual finite **global** optimizer on every positive
gradient-modulus cutoff of a finite-cost ambient local minimum. The whole
zero-gradient kernel is retained. With its algebraic self-adjoint kernel
restriction, compact spectral completeness proves
`CharbonnierOptimizerAngles.commute_sinAngleOperator_of_charbonnier_isLocalMinOn_complex`:
every finite-cost operator-norm local minimum preserves the intrinsic
principal-sine operator. The previous global endpoints specialize these
stronger local results, without duplicate underlying proofs.
Focused finite-transfer/local-cutoff/angle build passed 7,556 jobs.

Still open at this checkpoint: local fixed common directions and canonical
inactive tails. Local angle preservation alone does not identify action
on the zero-angle sector. The next proof must retain the finite reflecting
support of the full zero-gradient kernel and apply finite local-to-global
rigidity, before concluding any infinite local-to-global theorem.

## Hilbert Charbonnier finite-cost local-to-global, and its sharp scope

`CharbonnierLocalFixed.eq_one_of_charbonnier_isLocalMinOn_self_transport_complex`
proves identity is the only finite-cost operator-norm local minimum for
self-transport. The proof retains the entire zero-gradient kernel,
uses compactness of its self-adjoint displacement to obtain a finite
source-reducing reflecting support, and applies finite landscape rigidity
there and on every positive gradient cutoff. This discharges the singular
kernel obstruction rather than assuming away zero displacement or fixed
ambient directions. The same argument on the zero-angle restriction gives
`apply_eq_self_of_projections_eq_of_charbonnier_isLocalMinOn_complex`.

Closed-threshold canonical rigidity and canonical inactive-tail necessity
now hold for finite-cost **local** minima as
`eq_canonicalPolarFactor_of_charbonnier_isLocalMinOn_of_gap_le_critical_complex`
and
`apply_eq_nonacuteDirectRotation_on_inactive_tail_of_charbonnier_isLocalMinOn_complex`.
Their old global APIs specialize these stronger results.

`CharbonnierLocalGlobal.charbonnier_isMin_of_isLocalMinOn_complex`
proves every finite-cost operator-norm local minimum is globally minimizing
against all ambient complex unitary transports, on any complete Hilbert
space. No separate compactness, ideal, index, prescribed-block or
separability assumption is imposed: native finite feasibility supplies
HS projection difference and balanced defects. The companion
`charbonnier_isLocalMinOn_iff_isMinOn_of_finite_cost_complex` is the exact
local/global iff on the finite-cost part of the fiber. All zero, repeated,
critical and right angles remain included.

The finite-cost qualifier is essential in operator norm. The either-field
donor `CharbonnierInfiniteLocal.isLocalMin_charbonnierCost_of_not_isCompactOperator`
proves every noncompact unitary displacement lies on an open native
infinite-cost plateau. The closedness of compact operators, not continuity
of the infinite trace, proves this. The explicit theorem
`neg_isLocalMinOn_not_isMinOn_charbonnier_self_transport` shows negative
identity is an infinite-cost local minimum but not a global minimum for
self-transport of **any** subspace in an infinite-dimensional real or
complex Hilbert space; identity has cost zero. This refutes an unrestricted
infinite-dimensional no-spurious-local-minima assertion. Focused endpoint
build passed 7,634 jobs. Paper and visualizations remain untouched.

Next mathematical refinement: determine whether the remaining infinite-cost
local minima are exactly these noncompact plateaus when finite transport
is feasible. The missing lemma is density, in operator norm and within the
exact transport fiber, of finite-cost finite-rank updates of a fixed
finite-cost reference near every compact-displacement transporter. The
existing compact-unitary approximation preserves all commutants, so this
is an unblocked route to a complete (extended-cost) landscape iff.

## Complete native extended-cost local landscape

`CharbonnierLocalGlobal.charbonnier_isLocalMinOn_iff_global_or_noncompact_complex`
now classifies **every** operator-norm local minimum, including infinite
cost, with no standing feasibility, ideal or index assumptions:
for a feasible ambient complex transporter U, local optimality iff
U is globally optimal **or** `1-U` is noncompact. Noncompact displacements
lie on open infinite-cost plateaus. When finite cost is infeasible, every
feasible transporter is already an infinite-cost global minimum. Thus the
statement covers both feasibility regimes and does not misidentify the
infinite plateaus as finite-cost traps.

The missing compact infinite-cost case is discharged constructively.
`TauCeti.exists_compact_transport_finite_update_sequence` proves operator-norm
density of finite-rank updates of R near U in an exact bounded-operator
transport fiber whenever `U-R` is compact. Neither unitary itself need be
near identity; source and target bounded operators need not be projections,
and both scalar fields are included. Accepted compact unitary approximation
preserves the full commutant, hence preserves the exact target.

`exists_charbonnier_transport_finite_update_sequence` then approximates every
compact-displacement transporter in a finitely feasible fiber by actual
finite-cost finite-rank updates of a chosen finite-cost reference.
`charbonnierCost_displacement_ne_top_of_isLocalMinOn_of_compact` proves, over
both fields, that compact-displacement local minima in such a fiber must
have finite cost. The proof needs no native trace continuity or convergence
of the objective values: eventual local comparison with any of the finite
approximants suffices. Combined with the finite-cost complex landscape,
this yields the unconditional exact local/global/noncompact iff above.
Paper and visualizations remain untouched; no historical-priority claim is
inferred from the formal landscape result.

## Complete local landscape for nearest symmetry correction

The field-generic donor
`TauCeti.charbonnier_correction_isLocalMinOn_iff_transport_isLocalMinOn`
now transfers actual operator-norm local minimality between nearest
projection-commuting correction and relative subspace transport. The
candidate is feasible, the maps are continuous inverses on actual unitary
groups, and all native extended costs and nearby ambient competitors are
retained. No finite-cost or positive-smoothing assumption is needed for
this algebraic/topological correspondence itself.

For positive smoothing on any complete complex Hilbert space,
`CharbonnierCommutingCorrection.charbonnier_correction_isLocalMinOn_iff_global_or_noncompact_complex`
classifies every locally nearest commuting correction C of input A:
local optimality iff global optimality or noncompactness of `A-C`.
The latter points lie on open infinite-cost plateaus. The correspondence
between compactness of `A-C` and of the relative displacement is proved
by the two actual unitary factorizations, not by treating Charbonnier cost
as an ideal gauge.
`charbonnier_correction_isMin_of_isLocalMinOn_of_finite_cost_complex`
then proves every finite-cost local correction is globally nearest among
all ambient commuting unitaries. No standing index or commutator-ideal
condition is assumed in either landscape endpoint. Focused application
build passed 7,682 jobs. No algorithmic convergence, experimental, physical
implementation or statistical guarantee is claimed.

The completed complex smoothed frontier now includes exact global values
and attainment; every optimizer and its topology; exact uniqueness;
finite-rank correction budgets; every operator-norm local minimum,
including the complete extended-cost obstruction; and the corresponding
nearest symmetry-correction landscape. All statements retain their exact
ideal/index conditions where those are needed for finite attainment.
Historical priority and formal verification remain separate questions.
Paper and visualization files remain untouched.

Next substantive theorem: extend the finite-cost Hilbert local-to-global
argument to strict Schatten exponents `1<p<2`, preserving the full
zero-gradient kernel and handling singular displacement values through
the existing native rank-one first variation. The new compact-relative
transport density and plateau arguments are field-generic foundations
for its extended-cost landscape, but they do not by themselves prove
its finite-cost local-to-global implication. Infinite nuclear and real
optimizer classifications, projection-factor connectedness/manifold
dimensions, and quantitative varying-data/near-minimizer stability remain
open and are not implied by this smoothed closure.

Final compiler evidence for the complete landscape/application wave:
full default `lake build` passed 21,333 jobs
(`/tmp/charbonnier-local-final-full.log`), and separate `lake build Challenge`
passed 19,755 jobs (`/tmp/charbonnier-local-final-challenge.log`). Each build
was preceded by `lake exe cache get`. All preceding focused endpoints
were accepted without increasing heartbeat limits or disabling linters.

## Strict Schatten local-landscape campaign: analytic and restriction seams

`TauCeti.exists_schatten_locally_minimizing_reducing_restriction` and its
finite specialization now descend operator-norm local minimality of the
native Schatten gauge to actual reducing sectors over either scalar
field, for every finite real exponent at least one. Both sectors can be
infinite. The proof uses exact additivity of the positive powered gauge,
finite tail cancellation and strict monotonicity of that positive power.
Restricted native cost is proved finite.

`SchattenStationarity.gradient_reflection_conjugate_eq_neg_of_schatten_isLocalMinOn_complex`
now proves native finite-cost local stationarity for every `p>1` in
arbitrary complete complex Hilbert dimension. The rank-one curve remains
in the exact transport fiber and has finite native cost at every
parameter; the proved native first variation includes zero displacement.
The existing global APIs now specialize the local identities.

`SchattenNativeLocalGlobal.schatten_power_isMin_of_isLocalMinOn_complex`
and `schatten_isMin_of_isLocalMinOn_finite_complex` transfer native local
optimality in the actual operator-norm unitary group to the complete
finite real landscape for `1<p<2`, including all angle degeneracies.
The accepted embedding's exact neighborhood image is used. Focused
restriction/stationarity and finite-transfer builds passed 6,908 and
7,390 jobs respectively. The infinite local-to-global result is not yet
claimed: the next dependency is local finite gradient cutoffs, preserving
the existing global cutoff API's broader `p>1` scope rather than silently
adding a `p<2` hypothesis to it. Paper and visualizations untouched.

## Strict Schatten local spectral reduction and no mixing

`SchattenGradientCutoff.exists_locally_minimizing_restriction_on_gradient_cutoff_complex`
extracts actual finite locally minimizing restrictions, with finite native
cost, for every positive gradient cutoff of every finite-cost ambient
operator-norm local minimum at `p>1`. Actual forward/inverse actions,
source/target reduction and the complementary gradient bound are proved.
The established global cutoff API retains its full `p>1` scope, using
ambient global minimality to promote its restriction independently of
any strict-exponent finite landscape theorem.

For `1<p<2`, the new endpoint
`exists_minimizing_restriction_on_gradient_cutoff_of_isLocalMinOn_complex`
promotes those native local restrictions to finite global minima.
`SchattenOptimizerAngles.commute_sinAngleOperator_of_schatten_isLocalMinOn_complex`
then proves every finite-cost Hilbert local minimum preserves the entire
principal-sine operator. Its proof uses compact spectral completeness
and the actual self-adjoint transport on the whole zero-gradient kernel;
no invertibility of displacement or simplicity of angles is assumed.
The old global angle-preservation theorem specializes the stronger local
rigidity. Focused cutoff/angle builds passed 7,538 and 7,546 jobs.

The remaining strict-exponent local-to-global obstruction is action on
common zero-angle directions, followed by closed-threshold inactive-tail
rigidity. Compact reflection support and the finite native landscape are
available to discharge it; none of those infinite conclusions is inferred
from no mixing alone. Paper and visualization files remain untouched.

## Hilbert strict Schatten finite-cost local-to-global

`SchattenLocalFixed.eq_one_of_schatten_isLocalMinOn_self_transport_complex`
proves identity is the only finite-cost operator-norm self-transport
local minimum for `1<p<2`. The proof retains the entire gradient kernel,
uses its actual self-adjoint restriction and compact reflecting support,
and applies the finite native landscape on that support and on all
positive gradient cutoffs. This yields
`apply_eq_self_of_projections_eq_of_schatten_isLocalMinOn_complex` for
all common-source and common-orthogonal directions in arbitrary dimension.

The closed critical regime and entire inactive tail are now rigid for
finite-cost **local** minima via
`eq_canonicalPolarFactor_of_schatten_isLocalMinOn_of_gap_le_critical_complex`
and
`apply_eq_nonacuteDirectRotation_on_inactive_tail_of_schatten_isLocalMinOn_complex`.
Their existing global endpoints specialize these stronger results.
The exact closed cutoff is still `cos(theta_c)=(2-p)/p`.

`SchattenLocalGlobal.schatten_isMin_of_isLocalMinOn_complex` now proves
every finite-cost operator-norm local minimum is globally minimizing
over all ambient complex unitary transporters, including infinite-cost
competitors, for `1<p<2` on any complete Hilbert space. There is no
standing separability, finite-rank, simple-angle, prescribed-tail or
index assumption: finite native feasibility supplies the projection
ideal and defect balance. The companion
`schatten_isLocalMinOn_iff_isMinOn_of_finite_cost_complex` is the exact
local/global iff on the finite-cost part of the fiber. Focused fixed,
canonical-tail and final endpoint builds passed 7,548, 8,024 and 8,030
jobs respectively. Historical priority remains independent of compilation.

Still to close at this checkpoint: classify infinite-cost local minima.
The existing compact-relative transport approximation is enough to
prove that, within a finitely feasible fiber, compact-displacement local
minima cannot have infinite Schatten cost. Noncompact displacements
instead give open infinite-cost plateaus. The intended unconditional
landscape is local iff global or noncompact displacement; the finite-cost
implication alone does not yet establish this equivalence. Paper and
visualization files remain untouched.

## Complete strict Schatten extended-cost landscape

`SchattenLocalGlobal.schatten_isLocalMinOn_iff_global_or_noncompact_complex`
now classifies every operator-norm local minimum for `1<p<2` on an
arbitrary complete complex Hilbert space: a feasible U is locally
minimizing iff it is globally minimizing or `1-U` is noncompact.
There are no standing ideal, index, finite-cost, rank, simple-angle or
separability assumptions on the pair/candidate. In the absence of finite
feasibility every feasible transporter is globally minimizing at infinity;
otherwise noncompact displacements are exactly the additional infinite-cost
local minima. The finite-cost local-to-global proof is used only after
finite cost is justified, not on an infinite objective value.

The general field-generic endpoint
`TauCeti.exists_schatten_transport_finite_update_sequence_of_compact`
constructs native finite-cost finite-rank updates of any Schatten reference
near every compact-relative transporter, in the exact bounded-operator
conjugacy fiber, for every finite real exponent `p>=1`. Neither arbitrary
source nor target bounded operator needs to be a projection. The competitor
may have infinite Schatten cost; convergence is operator norm, not a
claim of Schatten convergence to an infinite-cost point. The smoothed
density theorem now directly consumes this result at exponent two and
the native Charbonnier/HS domain equivalence, retiring its duplicate
finite-update gauge argument.

`SchattenLocalTopology.gauge_schatten_displacement_ne_top_of_isLocalMinOn_of_compact`
proves compact-displacement local minima have finite cost whenever their
fiber has a finite reference, over both fields and for every finite real
exponent at least one. Noncompact points instead lie on open infinite-cost
plateaus by `isLocalMin_schatten_of_not_isCompactOperator`.
`neg_isLocalMinOn_not_isMinOn_schatten_self_transport` gives an explicit
nonglobal local minimum of infinite cost at negative identity in every
infinite-dimensional real or complex Hilbert space, for any self-transport
subspace and every such exponent. These general topological ingredients
do not assert finite-cost local-to-global over the real field or at the
nuclear endpoint. Paper and visualizations untouched; no first-priority
claim is inferred from compilation.

## Complete strict Schatten local symmetry-correction landscape

The field-generic operator-ideal endpoint
`TauCeti.OperatorIdealFamily.gauge_correction_isLocalMinOn_iff_transport_isLocalMinOn`
now transfers actual operator-norm local optimality between nearest
projection-commuting correction and relative subspace transport. It
preserves every accepted ideal gauge, including infinite values and all
nearby ambient competitors. Its hypothesis is feasibility of the actual
candidate, not ideal membership or finite dimension.

`SchattenCorrectionLocalGlobal.schatten_correction_isLocalMinOn_iff_global_or_noncompact_complex`
proves the complete strict-exponent correction landscape: for a commuting
candidate C of unitary input A, local optimality iff global optimality or
noncompactness of `A-C`. No commutator-ideal, index or finite candidate
cost is assumed. `schatten_correction_isMin_of_isLocalMinOn_of_finite_cost_complex`
proves every finite-cost local correction is globally nearest, comparing
against all ambient commuting unitaries including infinite-cost rivals.

`eq_canonical_correction_of_schatten_isLocalMinOn_of_compact_of_commutator_le_critical_complex`
identifies every **compact** locally nearest correction as
`canonicalPolarFactor(AK,K) * A` when the actual commutator is Schatten
and its operator norm is at most the critical sine. Candidate Schatten
membership, finite distance and index balance are conclusions rather
than standing assumptions. The compact hypothesis is needed to exclude
the proved noncompact infinite-cost local plateaus. Critical equality,
zero and repeated angles and arbitrary ambient dimension are retained.
Focused application build passed 8,048 jobs. These approximation theorems
do not claim convergence of an algorithm, computational performance,
physical implementation or statistical guarantees.

The completed strict complex Hilbert frontier now includes every global
optimizer and its topology, exact uniqueness, finite-rank correction
budgets, every operator-norm local minimum (including infinite costs),
and the corresponding nearest symmetry-correction landscape. The generic
compact-relative finite-update theorem simultaneously strengthens the
smoothed density proof and supplies foundations at other finite exponents.
Historical novelty remains a separate priority question; none of these
compiler results by itself establishes historical priority. Paper and
visualization files remain untouched.

Most consequential remaining mathematical directions: exact trace-class
attainment and every-optimizer classification for genuinely infinite-rank
projection pairs (the positive critical cutoff disappears at `p=1`);
real-field unrestricted strict-exponent optimization and its determinant
components; topology beyond the already proved projection-factor
homeomorphisms (connected components/manifold dimensions); and sharp
varying-data or near-minimizer stability. The completed complex local
proof does not establish a real local-to-global theorem, a nuclear
nonsmooth landscape theorem, or a uniform quantitative solver guarantee.
Resume from these exact scope boundaries rather than treating those
extensions as compiled consequences of the strict/smoothed theory.

Final compiler evidence for this strict-exponent local-landscape wave:
full default `lake build` passed 21,345 jobs
(`/tmp/schatten-local-final-full.log`); separate `lake build Challenge`
passed 19,755 jobs (`/tmp/schatten-local-final-challenge.log`). Each build
was preceded by `lake exe cache get`. Existing public global signatures
and names were preserved; new fixed-complex endpoints carry `_complex`.
No heartbeat limits or lint settings were relaxed. Earlier chronological
paragraphs identifying these strict local-to-global and extended-cost
landscape results as open are superseded by the endpoints above.

## Nuclear infinite-rank campaign: exact modulus-split cost

`ContinuousLinearMap.gauge_schatten_rpow_add_of_selfAdjoint_mul_eq_zero`
now proves exact native Schatten-power additivity for self-adjoint
operators with zero product, over either field, without compactness or
finite-cost assumptions. The proof identifies the actual reducing
kernel/complement sectors and consumes the established block trace API.

`gauge_schatten_rpow_modulus_add_of_unitary_odd` proves that if unitary
conjugation negates a self-adjoint A, its two modulus splits have equal
cost and orthogonal supports, with
`||2 A||_p^p = 2 || |A|+A ||_p^p` for every finite real `p>=1`.
`gauge_nuclear_modulus_add_of_unitary_odd` gives the exact endpoint identity
`|| |A|+A ||_1 = ||A||_1`. Infinite values and arbitrary ambient kernels
are included. Unitary conjugation of the modulus is proved using the
existing Gram-conjugation/modulus API, rather than a new spectral basis.

Next: apply the identity to the self-adjoint imaginary part of completed
direct rotation, whose modulus is the projection sine operator. The
candidate `R (C + i S)` should be an explicit global nuclear attainer.
The exact infinite-rank attainment theorem is not yet claimed at this
foundation checkpoint. Paper and visualizations remain untouched.


## Exact infinite-rank complex nuclear attainment — 27 October 2026

The trace-class endpoint now has an explicit global optimizer, with no
finite-rank reference and no separability assumption. In
`DavisKahan/Geometry/Polar/NuclearPhase.lean`, let R be completed direct
rotation for any actual isometric identification D of the crossed defects,
C the intrinsic cosine and S the intrinsic sine. Then
`nuclearPhaseRotation_complex K L D = R (C + i S)` is an actual unitary
transporting K onto L. The compiled theorem
`gauge_nuclear_nuclearPhaseRotation_complex` proves its literal native
nuclear displacement equals `||P_K-P_L||_1`, even when this value is infinite.
`nuclearPhaseRotation_isMin_complex` compares it with **every** ambient
unitary transporter, using the universal projection-difference lower bound.
Zero, repeated and right angles and fixed ambient directions are included.

The proof identifies `A=-i(R-C)` as self-adjoint, with `|A|=S`, and
source reflection conjugating A to -A. The exact factorization
`I-R(C+iS)=-i R(A+S)` reduces the cost to the previously compiled odd
modulus-split identity. It does not construct an infinite eigenbasis or
assume a finite strictly active sector at the nuclear endpoint.

In `SchattenNuclearEndpoint.lean`,
`exists_unitary_minimizing_nuclear_transport_complex` assumes precisely
that `P_K-P_L` has finite native nuclear gauge and the finite crossed-defect
dimensions agree. It constructs the identification D and proves existence,
finite cost, exact value `||P_K-P_L||_1` and unrestricted global minimality.
`exists_finite_nuclear_minimizer_iff_complex` makes those two conditions
necessary and sufficient for existence of a finite-cost global minimizer.
The necessity consumes the existing restricted-unitary feasibility theorem;
this work does not claim discovery of the classical index obstruction.
The older finite-rank-reference theorem and all existing public signatures
are retained.

Focused endpoint build passed 7,456 jobs; the full default build passed
21,351 jobs (`/tmp/nuclear-attainment-full.log`). Both were preceded by
`lake exe cache get`, with warnings treated as errors. No manuscript or
visualization is changed; historical priority remains separate from
compilation. The supplied historical review is already committed as
`e5e80e52f`, with its qualified negative-search conclusions intact.

Next exact obligations: classify **every** infinite-rank nuclear optimizer
(the explicit common-branch phase proves attainment, not exhaustiveness);
prove the balanced-pair identity between the ambient nuclear projection
difference and twice the directed nuclear sine if exposing that intrinsic
value; determine whether a nuclear optimizer can differ from canonical
rotation by finite rank for genuinely infinite-rank pairs. The strict-exponent
finite-active-cutoff proof cannot be reused at p=1 because its critical
angle is zero. The new explicit construction supplies the missing endpoint
attainer without claiming these remaining structural statements.


## Nuclear correction certificate and exact phase-update rank — 27 October 2026

`NuclearCommutingCorrection.lean` proves
`exists_nearest_nuclear_commuting_unitary_complex`: for a unitary A and
orthogonally complemented K in any complete complex Hilbert space, a
trace-class commutator `[A,P_K]` and balanced crossed defects of `(AK,K)`
give an actual unitary C commuting with P_K, at finite nuclear distance,
with exact globally minimal cost `||A-C||_1 = ||[A,P_K]||_1`. All ambient
commuting unitaries are competitors. The construction composes A with
the explicit nuclear phase transport of its image back to K.

`exists_finite_nearest_nuclear_commuting_unitary_iff_complex` proves the
commutator-ideal and defect conditions are also necessary. The theorem
`exists_nearest_nuclear_commuting_unitary_of_commutator_norm_lt_one_complex`
removes the separate defect hypothesis when the actual commutator operator
norm is strictly below one. The exact nuclear value is a certificate,
not a claim about a numerical algorithm or computational performance.
This application is a proved consequence of the new attainment theorem;
no separate fundamental-priority claim is made for the change of variables.

In `NuclearPhase.lean`,
`cosine_add_i_sine_apply_eq_self_iff_complex` identifies the fixed vectors
of the phase with exactly the vectors on which the projections agree.
`rank_nuclearPhaseRotation_sub_directRotation_complex` then proves, as
an exact cardinal rank identity and without compactness,
`rank(W-R) = rank(P_K-P_L)`. Thus the explicit nuclear phase correction
is finite rank exactly for finite-rank projection difference. For
genuinely infinite-rank pairs this construction cannot be described by
the strict-exponent finite-active correction theorem. This does **not**
prove that every nuclear optimizer must have infinite-rank correction;
that universal classification remains open.

Focused geometry build passed 7,134 jobs; focused application build
passed 7,888 jobs. Full default build passed 21,353 jobs
(`/tmp/nuclear-consequences-full.log`), preceded by `lake exe cache get`.
The historical review remains archived without promoting its reported
source inspections to independent primary-edition authentication.
Paper and visualization files remain untouched.

## Intrinsic infinite-rank nuclear value — 27 October 2026

`ContinuousLinearMap.gauge_schatten_rpow_eq_twice_of_selfAdjoint_offDiagonal`
(in `ForTauCeti/Analysis/OperatorIdeal/OffDiagonalTrace.lean`) proves
`||A||_p^p = 2 ||A P||_p^p` for a self-adjoint A, star projection P,
and exact off-diagonal equation `A P=(I-P) A`, over either field and
any finite real p>=1. No compactness, summability or separability is
assumed, and extended infinite costs are included. The proof splits
|A| into orthogonal self-adjoint blocks, matches their costs by adjoint
invariance, and uses the accepted pointwise-norm approximation-number API.

`gauge_schatten_projection_sub_rpow_eq_twice_sine_complex` now proves
`||P_K-P_L||_p^p = 2 ||sinThetaMap(K,L)||_p^p` for every actual isometric
crossed-defect identification, again without compactness or finite cost.
The completed rotation's self-adjoint imaginary part is exactly off
diagonal relative to K, with modulus the intrinsic sine; this identifies
both sides with the generic off-diagonal formula.

In `SchattenNuclearEndpoint.lean`,
`gauge_nuclear_projection_sub_eq_twice_sine_complex` derives the identity
from native nuclear projection difference and balanced defect finranks.
`exists_unitary_minimizing_nuclear_transport_eq_phaseMinimum_sum_complex`
then gives an unrestricted finite-cost global attainer at the literal
infinite angle sum, with no finite-rank reference. This closes the value
identification left open in the previous checkpoint. It does not classify
every nuclear optimizer. The donor identity is classical spectral geometry;
its compilation does not establish independent historical priority.

Focused donor build passed 6,554 jobs; geometry passed 7,136 jobs;
endpoint passed 7,458 jobs. Full default build passed 21,355 jobs
(`/tmp/nuclear-angle-full.log`), after `lake exe cache get`. Paper and visualization files remain untouched.


## Complete nuclear uniqueness criterion — 27 October 2026

`NuclearSignedPhases.lean` constructs the opposite explicit optimal
phase `negativeNuclearPhaseRotation_complex = R(C-iS)`. It is source-
reflection conjugate to the adjoint of the positive phase. Native
nuclear cost is therefore exactly the same projection-difference
value, even at infinity, and the unitary transports the actual pair.
`norm_nuclearPhaseRotation_sub_negative_complex` proves the exact
separation of these two global optimizers is `2 ||P_K-P_L||` in operator
norm, including fixed vectors and right angles.

`NuclearUniqueness.nuclear_transport_unique_minimizer_iff_complex`
proves the full endpoint criterion, for **arbitrary** orthogonally
complemented pairs in a complete complex Hilbert space: a unique global
native extended nuclear optimizer exists iff K=L. No trace-class,
balance, separability or transport-feasibility assumption is imposed.
Finite-cost uniqueness forces the two opposite optimal phases to agree,
and their separation forces the projection gap to vanish. For an
infinite-cost optimum, the negative of any transporter is another
optimizer; equality can occur only in the zero space, also with K=L.
For K=L the unique optimizer is identity by definiteness of the gauge.

`existsUnique_nearest_nuclear_commuting_unitary_iff_complex` transfers
the result to exact symmetry correction: there is a unique globally
nearest nuclear commuting unitary iff the input A already commutes
with P_K. This is the zero critical-threshold endpoint of the strict-
Schatten uniqueness theory, and explains intrinsic nonuniqueness of
nuclear alignment as soon as a correction is needed. It does not
classify all nonunique optimizer families or establish their topology.

Focused signed-phase build passed 7,138 jobs; uniqueness passed 7,462;
the application passed 7,894. Full default build passed 21,359 jobs
(`/tmp/nuclear-signed-full.log`), preceded by `lake exe cache get`. Manuscript and visualization files remain untouched; historical
priority is not inferred from Lean verification.


## Every finite nuclear optimizer: exact dual certificate — 27 October 2026

`NuclearOptimizerCertificate.lean` closes the nonsmooth finite equality
case without taking derivatives at vanishing displacement. The theorem
`nuclear_eq_sine_sum_iff_certificate_complex` applies even to competitors
that only contract the paired basis vectors and satisfy the paired
imaginary-diagonal constraint. Equality with `sum 2 sin(theta_i)` is
**equivalent** to fixation of all fixed basis directions and positivity
of `V* (R-Z)`. Here V has phases i,-i on each strictly positive angle
and identity on the fixed directions. Right angles are included. Zero
principal angles are represented in the fixed sector, avoiding the
undefined zero-denominator endpoint of the smoothed dual formula.

`exists_paired_nuclear_optimizer_certificate_complex` constructs a
single paired basis and actual unitary V from **every** finite-dimensional
equal-rank complex pair, then proves the criterion simultaneously for
**every** ambient unitary transporter T. With canonical R and
`Z=T* R`, global minimality over all ambient competitors is equivalent to
fixed common directions plus positivity of the literal dual displacement
`V* (R-T*R)`. The basis and dual do not depend on the candidate. No
simple-angle, acuteness, positive-displacement or block-preservation
hypothesis is imposed on T. This is a complete equality certificate;
it is not yet a Grassmannian parametrization of its solutions.

`nuclear_minimizer_apply_eq_self_of_projections_eq_complex` proves every
such finite global nuclear optimizer fixes **every** x with
`P_K x=P_L x`. The paired canonical eigenvectors of positive angle are
orthogonal to such x; expansion in the paired basis reduces x to the
fixed sector already forced by the certificate. This is an exact
all-competitor theorem, not a property only of the explicit phase family.

Focused build passed 7,310 jobs before import minimization. Full default
build passed 21,361 jobs (`/tmp/nuclear-certificate-full.log`), preceded
by `lake exe cache get`, with warnings treated as errors. The proof consumes existing
paired rotation bases, trace support and the nuclear trace/positivity
equality theorem, extending the smoothed certificate's method to the
nonsmooth endpoint while retaining its distinct zero-angle treatment.
Manuscript and visualization files remain untouched.

### Exact remaining analytic obligation for infinite nuclear classification

General native trace-class attainment, intrinsic value and uniqueness
are compiled. To lift the complete certificate, prove the trace-class
version of unitary trace-support equality: for a trace-class bounded
operator X and a fixed unitary V on an arbitrary complete complex
Hilbert space, equality of the real trace of `V* X` with the native
nuclear gauge is equivalent to positivity of `V* X`. Definitions,
absolute summability, nonseparable kernels and equality must all be
justified; the current `NuclearTrace.lean` certificate is finite dimensional.
An alternative is to derive the same equality from all finite paired
compressions, using native Ky Fan support bounds and their nonnegative
slacks. The new finite certificate deliberately accepts contractions,
so compressed competitors need not be unitary or preserve the section.

After that equality lift, the finite positive-slack argument should force
fixation of the common sector and a positive dual displacement for every
finite-cost infinite optimizer. The remaining algebra must then prove
preservation of each cosine sector, extract self-adjoint-unitary phase
choices on the positive acute multiplicity spaces, and treat the finite
right-angle sector separately. Do not infer these necessities merely
from the existence of signed attaining phases. At the nuclear endpoint
there can be infinitely many active angle sectors; the strict-exponent
finite-active-cutoff theorem does not establish the desired classification.

## Infinite nuclear trace equality is compiled — 27 October 2026

The analytic equality lemma named in the preceding checkpoint is now
proved. `ForTauCeti/Analysis/InnerProductSpace/HilbertSchmidt/Trace.lean`
proves absolute summability and the norm support bound for diagonal
traces of Hilbert–Schmidt products, over either field and arbitrary
Hilbert-basis cardinality. Its rigidity theorem
`eq_of_re_tsum_inner_comp_eq_hilbertSchmidtEnergy` forces Y=H when a
self-adjoint Hilbert–Schmidt H and a no-larger-energy Y saturate the
real diagonal trace of Y H. The proof uses the accepted square-summable
column representation and equality in Hilbert-space Cauchy–Schwarz.

`ForTauCeti/Analysis/OperatorIdeal/Nuclear/Trace.lean` proves the exact
native Gram-energy identity and constructs a square-root polar
factorization A=Y H with H positive, H^2=|A|, energy(H)=||A||_1,
and energy(Y)<=energy(H). This holds even at infinite cost. For finite
native nuclear gauge, both factors are Hilbert–Schmidt and every
Hilbert-basis diagonal is absolutely summable.

The endpoint
`ContinuousLinearMap.re_tsum_inner_eq_nuclearENorm_iff_isPositive_complex`
proves, for every trace-class A and every Hilbert basis b,
`Re(sum_i <b_i,A b_i>) = nuclearENorm(A).toReal` iff A is positive.
`re_tsum_inner_unitary_comp_eq_nuclearENorm_iff_isPositive_complex`
gives the same equivalence after an arbitrary actual unitary change
of target coordinates, with the original native nuclear cost. Neither
separability nor finite rank is assumed. These are convergent diagonal
series, not Mathlib's algebraic infinite-dimensional LinearMap.trace.

Focused generic Hilbert–Schmidt build passed 5,576 jobs; focused nuclear
trace build passed 6,662 jobs. Full default build passed 21,365 jobs
(`/tmp/nuclear-trace-full.log`), preceded by `lake exe cache get`. This is a classical trace-ideal foundation, not a historical
first-discovery claim. Manuscript and visualization files are untouched.

Next, prove basis independence/cyclic identities for these diagonal
trace series and construct the infinite transport dual from the polar
quarter turn of R-C, completed by identity on its kernel. The completed
trace-equality lemma alone does not yet prove calibration of that dual
against every transporter, the fixed-direction necessity, or the
remaining phase/multiplicity classification. The older statement that
the trace-support equality itself is open is superseded.

## Basis-independent nuclear trace and exact fixed-sector slack — 27 October 2026

The trace foundation now includes a basis-independent scalar
`ContinuousLinearMap.nuclearTrace`, with its complex trace-class
properties proved from absolutely convergent diagonal sums. Additivity,
scalar homogeneity, adjoint conjugation, bounded-factor cyclicity,
unitary-conjugation invariance, zero trace of unitary-odd operators,
and faithfulness on positive operators are compiled in
`ForTauCeti/Analysis/OperatorIdeal/Nuclear/Trace.lean`. All properties
retain native trace-class hypotheses. The definition does not assert
an operator-norm continuous trace on all bounded operators.

The generic Hilbert–Schmidt foundation proves full scalar basis
independence and cyclicity over either field. Polarization of three
accepted Hilbert–Schmidt energies gives real-part invariance; applying
it to every scalar multiple determines the scalar trace. Thus the
argument avoids an unjustified interchange of conditionally convergent
series and applies to arbitrary Hilbert-basis cardinalities.

`two_mul_re_nuclearTrace_unitary_projection_defect_complex` proves the
exact quantitative identity
`2 Re tr((I-Z)Q) = ||(I-Z)Q||_HS^2` for every actual unitary Z and star
projection Q, assuming only `(I-Z)Q` is trace class. In particular Q
need not be finite rank, and Z-I need not be trace class globally.
`re_nuclearTrace_unitary_projection_defect_nonneg_and_eq_zero_iff_complex`
proves its real trace is nonnegative, with equality precisely when Z
fixes the entire projected sector. This supplies both the sign and
rigidity of the nuclear transport dual's common-direction defect.

The square-root trace proof now consumes the accepted Tau Ceti
`polarFactor` and `factorThru` norm estimate directly, removing its
initial use of the local `polarPartial` donor representation.
`ForTauCeti/Analysis/InnerProductSpace/Polar/Symmetry.lean` supplies the
missing negation and unitary-conjugation symmetries of that accepted
factor. A skew-adjoint polar factor, completed by identity on its
kernel, is proved unitary over either field in arbitrary dimension.
This is the intended actual nuclear transport dual.

Focused nuclear trace build passed (6,664 jobs in the joint build);
focused canonical polar symmetry build passed 6,296 jobs. Full default
build passed 21,369 jobs (`/tmp/nuclear-trace-cyclic-full.log`), preceded
by `lake exe cache get`. These are classical trace and
polar foundations; their formal verification alone establishes no
historical novelty. Paper and visualizations remain untouched.

Next actual transport theorem: let B=R-C and complete B.polarFactor
by identity on ker B to the unitary V. For relative Z=T*R, prove
`V*(R-Z) = S + Q(I-Z) + (B.polarFactor)*(C-Z)`, where the last factor
uses the adjoint polar phase and Q is the kernel projection. Its last
term is odd under source reflection, hence has zero nuclear trace.
The exact defect identity above should then characterize every finite-
cost Hilbert nuclear optimizer by fixation of the common sector and
positivity of the actual dual displacement. Calibration, the iff and
the subsequent phase/multiplicity parametrization are not yet claimed.


## Full-space algebraic nuclear dual — 27 October 2026

`Geometry/Polar/NuclearDual.lean` constructs the actual unitary
`nuclearTransportDual` in an arbitrary complete RCLike Hilbert space,
assuming orthogonally complemented K,L and an actual isometric
identification of their crossed defect spaces. No finite dimension,
compactness or trace assumption is used. The skew part B=R-C has kernel
exactly ker(P_K-P_L); its accepted polar factor F is odd under source
reflection. The dual is V=F+P_ker(B). The cosine fixes this entire kernel.

`nuclearTransportDual_adjoint_mul_displacement` proves for every bounded Z:
`V*(R-Z) = S + Q(I-Z) + F*(C-Z)`, where stars on V and F mean adjoints,
S=|P_K-P_L| and Q is the kernel projection. This is the algebraic
calibration identity, not yet its trace-class optimizer iff.

Importing this accepted polar API together with the existing geometry
exposed a duplicate `modulus_adjoint` declaration. The redundant donor
proof is retired and its two internal consumers use accepted TauCeti
polar theorems. No public alias or compatibility layer is introduced.
The name-drift scanner retains its 23 unrelated pre-existing findings.

Focused dual build passed 7,010 jobs. Full default build passed 21,371
jobs (`/tmp/nuclear-dual-full.log`), preceded by `lake exe cache get`.
Explicit Challenge validation follows this entry. Next: show the last term in the identity
has zero nuclear trace for Z=T*R, prove quantitative trace calibration,
and deduce the exact all-ambient nuclear optimizer certificate. The
phase/multiplicity parametrization beyond that certificate remains open.
Paper and visualization files are unchanged.


## Every Hilbert nuclear optimizer: exact certificate — 27 October 2026

`Geometry/Polar/NuclearOptimizerCertificate.lean` now compiles the
previously missing trace calibration and all-ambient optimizer iff.
Assume E is any complete complex Hilbert space, K,L admit orthogonal
projections, the native nuclear norm of P_K-P_L is finite, and an actual
isometric equivalence D of crossed defects is supplied. There is no
finite-rank, separability, acute-angle or invariant-block hypothesis.

* `nuclearTransportDual_trace_calibration_complex`: for every actual
  unitary Z commuting with source reflection, with trace-class R-Z,
  `Re tr(V*(R-Z)) = ||P_K-P_L||_1 + ||(I-Z)Q||_HS^2/2`.
  Here R is completed direct rotation, B=R-C, Q=P_ker(B), V is the
  actual nuclear dual, and the star on V denotes its adjoint.
  The proof establishes trace-class membership of every summand;
  the reflection-odd summand has zero absolutely convergent trace.
* `nuclear_eq_projection_sub_iff_relative_certificate_complex`:
  the native nuclear norm of R-Z equals the sine minimum exactly
  when `(I-Z)Q=0` and `V*(R-Z)` is positive.
* `nuclear_isMin_iff_certificate_complex`: for every transporter T,
  global minimality among **all** ambient unitary transporters is
  equivalent to trace-class I-T, fixation of every vector x with
  P_K x=P_L x, and positivity of `V*(R-T*R)`. Stars again denote
  adjoints. Competitors of infinite native cost are included in
  the quantified optimization; the certificate necessarily excludes
  their being minimizers because the explicit phase attainer is finite.
* `nuclear_minimizer_apply_eq_self_of_projections_eq_complex`:
  every optimizer fixes that entire sector. This extends the previous
  finite-dimensional rigidity theorem, including infinite ambient
  directions and arbitrary projection multiplicities.

This is a complete necessary-and-sufficient operator certificate for
**every** nuclear optimizer. It is not yet an explicit phase/Grassmannian
parametrization of the nuclear optimizer families. In particular the
p=1 moving sector can be infinite rank, so the strict-exponent finite
active-correction reduction cannot be reused without a new argument.
The exact remaining structural step is to solve the positive dual
constraint together with transporter unitarity on that moving sector,
and determine possible mixing between unequal angles and right defects.
No historical-first claim follows from compiler acceptance.

The full-space dual checkpoint passed the explicit Challenge build
(19,757 jobs; `/tmp/nuclear-dual-challenge.log`). The focused optimizer
certificate build passed 7,172 jobs, preceded by `lake exe cache get`.
Full default build with the registered endpoint passed 21,373 jobs
(`/tmp/nuclear-certificate-full.log`), preceded by `lake exe cache get`.
Papers and visualizations remain untouched.


## Quantitative nuclear fixed-sector stability — 27 October 2026

`nuclearTransportDual_fixed_sector_gap_complex` turns the exact trace
calibration into a cost-excess bound for every finite-cost relative
competitor commuting with source reflection. Its transporter-facing
consequence, `nuclear_transport_fixed_sector_gap_complex`, compiles in
`Geometry/Polar/NuclearStability.lean`. With the same complete-complex,
trace-class-projection-difference and actual crossed-defect hypotheses,
for **every** ambient transporter T with finite native nuclear cost:

`||(I-T) Q||_HS^2 <= 2 (||I-T||_1 - ||P_K-P_L||_1)`.

Here Q projects onto ker(R-C), already proved exactly equal to
ker(P_K-P_L). Thus the theorem controls motion on the entire common
sector by excess above the unrestricted global minimum. The sector
may be infinite dimensional; no principal-plane preservation or finite-
rank correction is assumed. The proof consumes the accepted TauCeti
Hilbert–Schmidt isometry API to identify the relative defect with
literal T displacement. It does not assert closeness to a particular
optimizer on the moving sector, or uniqueness of a nuclear optimizer.
Historical priority for this quantitative consequence is not established.

Focused stability build passed 7,176 jobs after `lake exe cache get`.
The registered full default build passed 21,375 jobs
(`/tmp/nuclear-stability-full.log`), preceded by `lake exe cache get`. The moving-sector solution
of the positive certificate, described above, remains the strongest
precise structural obligation; the strict-exponent finite active-sector
argument does not establish it at the nuclear endpoint.


## Positive-unitary-average structure for nuclear parametrization — 27 October 2026

The next algebraic step is now isolated and proved in the generic donor
`InnerProductSpace/UnitaryPositiveAverage.lean`, over either RCLike field
in arbitrary complete Hilbert dimension. For unitaries U,W and a positive
C with `U+W=C+C`:

* `TauCeti.ContinuousLinearMap.unitary_positive_average_structure`
  proves both summands commute with C and `C(U-W*)=0`.
* `unitary_eq_adjoint_of_positive_average_injective` gives `U=W*`
  under injectivity of C, without assuming a bounded inverse or gap.
* `unitary_positive_average_adjoint_on_support` gives the same equality
  on ker(C)-orthogonal without assuming injectivity globally.

The proof first obtains the two identities `UC=CW*`, `W*C=CU`,
then commutation with C squared, and applies the existing positive
square-root commutation lemma. It explicitly retains the kernel
exception: if C=0 the only sum constraint is W=-U, which does not
in general make the two unitaries adjoints.

This targets the next structural transport reduction. In paired source/
complement coordinates the positive certificate should imply that the
two relative unitary blocks have positive average equal to the cosine.
The compiled average theorem will then eliminate unequal-cosine mixing
and identify adjoint phases away from the right-angle sector. **That
coordinate/block reduction from the actual transporter certificate is
not yet formalized or claimed here.** It remains the precise next
mathematical obligation before an explicit nuclear phase/Grassmannian
parametrization. The elementary donor lemma is not itself a novelty claim
or an accepted TauCeti submission target; future promotion requires
roadmap ownership rather than inferring it from this intended use.

Focused donor build passed 6,272 jobs. Full default build passed 21,377
jobs (`/tmp/unitary-average-full.log`), including the final TauCeti-owned
names. All builds were preceded by `lake exe cache get`. Paper and visualization
updates remain assigned elsewhere.


## Nuclear optimizers cannot mix unequal principal angles — 27 October 2026

The previously isolated average-reduction obstruction is now closed,
without choosing a principal-plane basis. In
`Geometry/Polar/NuclearOptimizerStructure.lean`, for any actual unitary
Z that fixes ker(R-C), self-adjointness of `V*(R-Z)` forces

`Z + V* Z* V = C+C`.

Here C is the intrinsic cosine and V is the actual completed nuclear
dual. `nuclearTransportDual_relative_positive_average` is generic over
RCLike and needs no trace assumption and no source-reflection
commutation assumption. The proof uses the new characteristic dual
identities: R fixes the skew-kernel projection, `V+V*=2Q`, and V
commutes with R. The latter follows from equivariance of the accepted
polar factor under unitary conjugation; the reusable generic
`ContinuousLinearMap.commute_unitary_polarFactor` is added to its
existing symmetry donor.

`nuclearTransportDual_relative_cosine_structure` applies the positive-
average lemma and proves Z commutes with C. It also proves
`Z(Vx)=V(Zx)` for every x in ker(C)-orthogonal. Thus the right-angle
exception is carried explicitly, without assuming C invertible.

`nuclear_minimizer_comm_cosine_complex` and
`nuclear_minimizer_comm_sinAngleOperator_complex` now prove that **every**
unrestricted ambient nuclear optimizer commutes with the intrinsic
cosine and sine. Their exact hypotheses are: arbitrary complete complex
Hilbert space, orthogonally complemented K,L, finite native nuclear
projection difference, an actual isometric identification of crossed
defects, a transporter T, and global minimality against every ambient
unitary transporter. No invariant-block hypothesis, finite rank,
separability, or acute-angle assumption is imposed. This rules out
mixing between unequal principal angles; equal-angle mixing and
right-angle families still require explicit parametrization.

Focused structure build passed 7,176 jobs. The registered full default
build passed 21,379 jobs (`/tmp/nuclear-structure-full.log`), with
`lake exe cache get` before each build.
The next mathematical step is to extract the real part of Z on the
positive-cosine support, then identify its self-adjoint imaginary
part as a signed square root of the sine square. Existing Mathlib
`realPart`, `imaginaryPart`, and the normal-operator square identity
should be consumed rather than replaced by new definitions. The
right-angle kernel must be treated separately throughout.
Paper and visualization files remain untouched. No historical priority
claim is inferred from these compiler results.


## Signed sine roots and a Hermitian all-optimizer certificate — 27 October 2026

`Geometry/Polar/NuclearSignedRoot.lean` strengthens the optimizer theory
beyond the preceding spectral-preservation checkpoint. The generic
`nuclearTransportDual_signed_sine_structure` assumes an actual relative
unitary Z, fixation `(I-Z)Q=0` of the full skew-kernel sector, and
self-adjointness of its calibrated displacement. It proves, for
`A=V*(Z-C)`, with stars denoting adjoints:

* A is self-adjoint;
* `|A|=S` and `A*A=S*S`;
* `V*(R-Z)=S-A`.

No inverse cosine, finite rank, trace assumption, source-reflection
commutation, or restriction on right angles is used in this algebraic
RCLike theorem. The proof derives the weighted identity
`C(Z+Z*)=2 C*C` from the positive average and computes the exact
Gram operator of Z-C. Accepted polar and positive-square-root APIs
identify its modulus. This preserves the right-angle exception rather
than falsely replacing the weighted identity by `Z+Z*=2C` globally.

`nuclearTransportDual_isPositive_of_isSelfAdjoint` then proves that the
self-adjoint displacement is automatically positive: `S-A=|A|-A` is
twice the negative part of A. The proof consumes Mathlib's existing
`CFC.abs_sub_self` and positive-part API. Furthermore,
`nuclearTransportDual_displacement_finite_of_isSelfAdjoint` proves that
finite native nuclear projection difference already forces finite
native nuclear R-Z under these structural conditions, over either
field. It does not require separately testing the displacement ideal.

The transporter-facing endpoint
`nuclear_isMin_iff_hermitian_certificate_complex` quantifies over **every**
ambient transporter T. On any complete complex Hilbert space, assuming
orthogonally complemented K,L, an actual isometric equivalence of crossed
defects, and finite native nuclear P_K-P_L, global optimality is exactly:
T fixes every x with P_K x=P_L x, and `V*(R-T*R)` is self-adjoint.
**Neither positivity nor finite displacement is an extra condition on
that right-hand side.** Both follow, including on infinite-dimensional
fixed sectors and arbitrary right-angle multiplicities.

Focused signed-root build passed 7,178 jobs. The registered full default
build passed 21,381 jobs (`/tmp/nuclear-signed-root-full.log`), with
`lake exe cache get` before each build. No
historical-first claim is made for classical unitary/absolute-value
algebra; the novel-priority question concerns the full transport
classification in its exact scope, separately from verification.

Next strongest structural step: turn the signed sine into independent
parameters. A candidate complete parametrization is self-adjoint A
with `|A|=S`, source-reflection oddness, and commutation with `V*C`;
construct `Z=C+V*A`, then T=R Z*. Necessity of the last commutation
and oddness, unitarity and transport of the construction, automatic
trace-class cost, and the two inverse identities all still require
formal proof. Only after that may one claim an explicit signed-root
parametrization, and only after spectral decomposition may one identify
its Grassmannian factors and unrestricted right-defect unitary factors.
This candidate replaces the older coordinate-block obstruction with a
precise basis-free theorem target. Paper and visualizations are unchanged.


## Constructing all admissible signed-root optimizers — 27 October 2026

`Geometry/Polar/NuclearRootConstruction.lean` closes the construction
half of the proposed parameter theorem. Over an arbitrary complete
RCLike Hilbert space, let C,S,R,V be the existing canonical cosine,
sine, completed rotation and completed nuclear dual. An independent
parameter A satisfies:

1. A is self-adjoint;
2. its native modulus is S;
3. A commutes with V C;
4. source-reflection conjugation negates A.

`signed_sine_root_kernel_and_cosine` proves A annihilates the entire
common-sector projection on both sides, commutes with C, and squares
to S squared. `signed_sine_relative_mem_unitary` proves `C+VA` is
unitary using only conditions 1–3; no inverse cosine is used, so right
angles are included. `nuclearSignedSineRelative` is that actual unitary.
`nuclearSignedSineRelative_map` uses condition 4 to prove source
preservation. `nuclearSignedSineTransport` constructs `T=R(C+VA)*`,
and its map theorem proves K maps exactly to L.

The literal relative-unitary identity and
`nuclearSignedSineTransport_extract_root` show that extraction returns
the exact original A. The dual displacement is exactly S-A.
`nuclearSignedSineTransport_isMin_complex` proves this T minimizes over
**all ambient** complex unitary transporters when P_K-P_L has finite
native nuclear norm. It uses the actual crossed-defect equivalence D;
no finite dimension, rank, separability or angle-block restriction is
assumed. Finite displacement is a consequence of the Hermitian
certificate. The construction/map/inverse algebra is RCLike-generic;
the unrestricted minimizing endpoint here is complex only.

New characteristic dual APIs prove its cosine commutation, common-
projection fixation, and exact reflection conjugation with the full
common projection retained. Focused construction build passed 7,180
jobs. The registered full default build passed 21,383 jobs
(`/tmp/nuclear-construction-full.log`), with cache retrieval before
each build.

Remaining direction: for an arbitrary global complex optimizer, its
extracted signed root already has conditions 1–2. Prove conditions
3–4 and that reconstruction returns the exact original transporter.
That will establish the complete signed-root parametrization. Its
subsequent conversion into Grassmannian factors and right-defect unitary
factors still requires spectral decomposition; no such topology claim
is made at this checkpoint. Papers and visualizations are unchanged.


## Complete infinite-dimensional signed-root parametrization — 27 October 2026

`Geometry/Polar/NuclearRootClassification.lean` closes the previously
recorded reverse direction. The independent set
`nuclearSignedSineParameters K L D` consists exactly of bounded A with:
self-adjointness, `|A|=S`, commutation with `V C`, and source-reflection
oddness. The actual optimizer set `nuclearTransportOptimizers K L`
contains the literal transport constraint and comparison against every
ambient unitary transporter. Its definition requires no complement or
finite-cost condition; the classification theorem carries the needed
projection and ideal hypotheses explicitly.

`nuclearSignedSineEquivOptimizers_complex` is a compiled **bijection**
between those two sets. Its forward map is the explicit constructed
unitary `T=R(C+VA)*`. Its inverse is the exact formula
`A=V*(T*R-C)`, where every star denotes adjoint. Both inverse identities
are compiled, with characteristic APIs for the literal forward relative
coefficient and inverse root. This is more than a positivity certificate:
the parameter conditions contain no transport or optimization predicate,
and every admissible independent parameter produces an optimizer.

Hypotheses: arbitrary complete complex Hilbert space; orthogonally
complemented K,L; an actual isometric equivalence D of crossed defects;
and finite native nuclear norm of P_K-P_L. There is no separability,
finite rank, acuteness or invariant-block restriction. Zero angles,
common ambient directions, repeated angles and right defects are all
included. Every optimizer is covered, including unrestricted ambient
mixing before the theorem deduces its necessary structure.

The new necessity lemmas are RCLike-generic: the extracted signed root
commutes with `V C` (without dividing by C), and it is reflection odd
when the relative unitary preserves the source. Reconstruction of the
original transporter from its relative coefficient is also generic.
Only the unrestricted optimizer bijection is asserted over the complex
field; it does not solve the unrestricted real nuclear minimum by
assuming the complex value is always real-attainable.

Focused classification build passed 7,182 jobs. The registered full
default build passed 21,385 jobs (`/tmp/nuclear-classification-full.log`),
preceded by `lake exe cache get`.

The complete signed-root parametrization is now proved. It has **not**
yet been decomposed into spectral Grassmannian factors and arbitrary
right-defect unitary factors, so no dimension or topology formula is
claimed from the algebraic bijection alone. The next useful consequence
is to test and prove isometry of this parametrization on pairwise
differences for symmetric ideal gauges. Then reduce the independent
root conditions on each positive-angle spectral sector and on the
right-defect sector. Historical priority remains a separate review;
no first-discovery claim is inferred from these compiler results.
Papers and visualizations remain untouched.

# Paper context: established claims, boundaries, and editorial decisions

**As of:** 25 October 2026
**Current research source:** the complete unrestricted finite-dimensional
complex Schatten `1<p<2` optimizer classification, its exact value,
local-to-global theorem, canonical and uniqueness thresholds, normalized
phase/defect parameters, and multiplicity-space operator-norm homeomorphism.
The full Charbonnier optimizer set for `tau>0` now also has unique normalized
phase/defect parameters, an independent finite multiplicity-space product
and its operator-norm homeomorphism. Both theories include every zero,
critical, repeated, fixed and right-angle direction. Both optimizer sets
are compact, their active rank labels are locally constant, and different
rank sectors have fixed-pair positive separation. Simple active factors
with zero right defect give exactly `2^s` isolated optimizers. The subspace
rank-stratification equivalences are algebraic. Sector connectedness,
component counts, manifold dimensions, smoothed local-to-global,
unrestricted real matching and operator-ideal optimization remain open.
The local Charbonnier analysis now supplies actual first variations,
source-reflection stationarity, paired two-phase gradient blocks and the
sharp gradient bound; second-variation exclusions remain to be proved.
**Manuscript and teaching-deck update source:** `427169ce38b5` (25 October
2026), incorporating the completed full complex optimizer classification,
local-to-global theorem, normalized parameter bijection and exact counts.
**Earlier integration source:** `521572a2500c` (24 October 2026, 15:48
incremental source patch, reconstructed against base `642de34df29a`).
The original source-result audit remains anchored to its reviewed Lean
statements. The later mathematical extensions do not change its 29 rows.
Earlier chronological status entries below are dated historical records;
current proof scope is summarized first.
**Paper:** *Formalizing Davis--Kahan Perturbation Theory and Exact Spectral Subspace Transport*
**Scope of this record:** working context for authors and future manuscript agents. This is deliberately **not** an appendix or a source of text to paste into the paper.

The Yu--Wang--Samworth source-version audit and manuscript fragments are in
`../yws_formalization_conference/`; this paper covers Davis--Kahan.

Start here when updating `paper.tex`. The fact that an assertion appears in an old draft, a development note, or a prior agent's answer does not make it current. Follow the evidence links below and preserve differences between source claims, Lean-verified statements, and mathematical arguments outside Lean.

## Actual Charbonnier stationarity and two-phase gradient blocks (25 October)

`SmoothedUnitaryVariation.lean` proves
`smoothedDisplacementCost_eq_re_trace_cfc` for every finite complex normal
operator and `hasDerivAt_smoothed_unitary_right_variation_at` for the literal
singular-value Charbonnier objective, at every time along every Hermitian
unitary exponential variation. The differentiability hypothesis is only
`tau>0`; there is no nonzero-displacement, simple-spectrum or invertibility
assumption on `I-U`. The phase symbol is
`smoothedPhaseDerivative tau z = z.im/sqrt(tau^2+||z-1||^2)` and the actual
self-adjoint gradient is its normal functional calculus.

`SmoothedStationarity.lean` proves
`re_trace_gradient_mul_eq_zero_of_isLocalMinOn_transports` and
`gradient_reflection_conjugate_eq_neg_of_isLocalMinOn_transports`: at every
actual constrained local minimum, source reflection negates the gradient.
The trace-annihilation theorem allows general supplied conjugacy data
`P,Q`; the reflection theorem requires `P` an orthogonal projection.
`SmoothedGradientPairing.lean` derives the actual source-reflection isometry
between opposite gradient eigenspaces and commutation of `G^2` with **both**
transported projections. No prescribed blocks are supplied by the caller.

`SmoothedGradientSpectrum.lean` proves the exact scalar deficit
`eta^-2-g_tau(z)^2 = (Re(z)-eta^-2)^2/(tau^2+||z-1||^2)` on the unit circle.
Consequences include `abs_smoothedPhaseDerivative_le`, its exact equality
criterion, an actual scalar attaining phase, `norm_smoothedUnitaryGradient_le`
and norm equality in the presence of an actual critical-phase eigenvector.
The operator norm bound itself allows arbitrary complete complex Hilbert
spaces; no infinite-dimensional trace or ideal optimum follows.

The same module proves the quadratic relation on **every** gradient level,
its two explicit complex candidates, and
`smoothed_gradient_eigenspace_two_phase_representation`: the actual unitary
restriction on each actual gradient eigenspace is affine in an actual
orthogonal projection. It includes zero levels, coalescing candidates,
repeated phases and empty eigenspaces, without any minimizing hypothesis.
`smoothed_gradient_kernel_reflection_representation` specializes to the
actual reflection `I-2*S` on the actual gradient kernel. It does **not** yet
show that local optimality permits only fixed/right blocks there.

For any real `g`, the Lean candidates use total `Real.sqrt`; the formal
scalar theorem asserts containment of every genuine unit-circle solution,
not admissibility of both candidates for arbitrary `g`. The manuscript
restricts their displayed radical formulas to `|g|<=eta^-1`, where all
radicands are nonnegative. Every actual gradient eigenvalue satisfies that
bound. No false converse or unproved root multiplicity claim is introduced.

The donor `CharbonnierSpectralTrace.lean` supplies the global scalar tangent
support and its continuous field, plus normal spectral-trace differentiation.
`UnitarySpectralVariation.lean` gives a common first-variation theorem for
scalar supporting fields continuous on the unit circle. Both the new
Charbonnier result and the existing Schatten trace-pairing theorem consume
it; the displaced private Schatten eigenbasis proof is removed. The common
theorem does not include the nuclear endpoint's singularity at identity.
These are classical variational ingredients, with no independent historical
novelty claim. The manuscript includes
`prop:smoothed-local-spectral-structure` as a proved necessary-structure result.

An independent six-dimensional test included repeated eigenvalue `1`,
eigenvalue `-1`, both critical phases and another phase. The trace-pairing
first variation agreed with a central finite difference to `1.57e-10`;
the scalar deficit residual was `6.66e-16`, and the gradient norm attained
`eta^-1=0.7094810050208546` to numerical precision. Separately, 36 projected
unitary-descent starts over three pairs at `tau=0.1,0.7,2` produced final
cost gaps at most `2.49e-9`. The `tau=0.1` run hit the iteration cap with
nonzero gradient, so neither convergence nor local-to-global follows.
These are diagnostics, not proofs or statistical guarantees.

Validation: the focused first-variation, stationarity, gradient-spectrum
and pairing modules passed, including the migrated Schatten stationarity
consumer. Then `lake build DavisKahan.All ForTauCeti` passed (10,485 jobs;
`/tmp/smoothed-stationarity-final-build.log`). Each build was preceded by
`lake exe cache get`. The journal passed pdfLaTeX, BibTeX and two further
pdfLaTeX passes to a 58-page PDF at
`/tmp/dk-smoothed-stationarity-paper/dk-smoothed-stationarity.pdf`, with no
warnings, overfull boxes, unresolved references or duplicate labels in the
final log. `git diff --check` passed. The 29-result source inventory and
unrelated submodules are unchanged.

### Exact remaining local-to-global obligations

The ambient first variation, actual stationarity, paired reducing squared-
gradient spaces, two-phase restrictions and zero-kernel reflection are now
compiled. The next useful lemma is the **actual two-phase second variation**:
use the analytic extension
`(tau^2+2-z-z^-1)^(-1/2)*(z-z^-1)/(2*i)` of the phase symbol, then consume
`hasDerivAt_cfc_of_affine_projection` as in
`ForTauCeti/Analysis/InnerProductSpace/SchattenTwoPhaseVariation.lean`.
For `tau>0` its unit-circle radicand is at least `tau^2>0`, including at
`z=1`, so no displacement endpoint should be assumed away.

Use that derivative to prove the paired-projection overlap exclusion on
submaximal levels, treat the maximal/coalesced level, and prove descent
for every nonoptimal zero-gradient reflection block. Then assemble the
actual local block costs and the exact global value. The existing global
optimizer iff cannot be applied to a merely stationary transporter.
Smoothed local-to-global, real matching, component dimensions and ideal
optimization remain open; the scope of the active research goal is unchanged.

## Complete effective Charbonnier coordinates and topology (25 October)

The remaining finite complex Charbonnier multiplicity-product obligation
is closed. For every `tau>0`, finite equal-rank pair and **all ambient
unitary competitors**, `SmoothedParameterNormalization.lean` proves
`smoothed_transport_isMin_iff_unique_normalized_phase_and_defect_complex`
and `exists_smoothed_normalized_parameter_equiv`: each optimizer has
exactly one normalized phase projection and independent defect unitary.
Both actual defect actions, the weighted **left-relative** equation
`C*(T.adjoint*R)`, and a fixed-pair uniform Lipschitz inverse phase estimate
are retained. No cosine-preservation hypothesis is imposed on competitors.

`SmoothedMultiplicityParameters.lean` proves
`exists_smoothed_multiplicity_parameter_equiv`, the rank-stratified
subspace equivalence `nonempty_smoothed_rank_stratified_parameter_equiv`,
and the Boolean/simple-active exact count endpoints. Every actual active
multiplicity space contributes an **independent arbitrary projection**;
the crossed-defect unitary is also arbitrary and independent. Active angles
satisfy `0<theta<pi/2`, `a*cos(theta)<b` and have a nonzero actual canonical
eigenspace, with `a=smoothingRadius(tau)>1`, `b=a^-1`. Inactive multiplicities
are unrestricted. Zero, exactly critical, fixed and right-angle directions
contribute no redundant phase parameter after normalization.

`SmoothedParameterTopology.lean` proves
`exists_smoothed_normalized_parameter_homeomorph` and
`exists_smoothed_multiplicity_parameter_homeomorph`. The latter also proves
local constancy of every inverse rank coordinate and `k>0` such that
different ranks on any active factor imply `1 <= k*||T-S||`, even when
defect parameters vary. The constant is not claimed sharp or uniform
through a phase transition. `isCompact_smoothedTransportMinimizers` proves
compactness, and the discrete-topology endpoint proves isolation in the
simple-active/no-right-defect case, where the exact count is `2^s`.

`SmoothedPhaseWeight.lean` proves the weighted coefficient
`2*i*c*sqrt(1-min(1,a*c/b)^2)` at a principal cosine `c`, its exact zero
criterion for `c>0`, and its vanishing at `c=0`.
`weightedPhaseWeight_orthogonal_ker_eq_paired_eigenspace_sum` and
`weightedNormalizedPhaseProjections_eq_paired_projection_space` identify
the effective phase space with exactly the paired actual active sum for
general `0<b<a`, before specialization to Charbonnier. The existing
complete canonical frame proves an intrinsic subspace equality; it does
not restrict the frame of competing optimizers.

The shared donor `Projection/KernelSupport.lean` adds normalization of a
commuting projection without changing weighted action, and kernel
annihilation for supported self-adjoint maps. `Projection/UnitaryTransport.lean`
adds the left-relative recovery estimate, allowing an infinite ambient
Hilbert space with finite effective input space. These are classical facts,
with no independent novelty or operator-ideal minimization claim. The
accepted Tau Ceti operator-norm topology is consumed directly.

The checked manuscript includes `thm:smoothed-effective-coordinates`.
The homeomorphism uses projection carriers; rank-stratified subspaces
remain an algebraic description. No connected-component count, manifold
dimension, `tau=0` optimizer classification, smoothed local-to-global,
real matching or ideal optimization is promoted by this result.

An independent nine-dimensional diagnostic at `tau=0.7` combined an
active angle `1.3` of multiplicity two, the exactly critical angle
`1.043309577432877`, a fixed direction and a one-dimensional right defect.
Rank-zero/one/two choices, complex mixing in the repeated eigenspace and
independent defect phases attained the predicted cost (largest numerical
cost residual zero; transport residual `2.86e-16`). One hundred unrestricted
random feasible competitors had larger costs (minimum sampled gap `1.35113`).
These diagnose the construction and imply no experimental guarantee.

Validation: the focused Charbonnier normalization, multiplicity and topology
modules passed, followed by `lake build DavisKahan.All ForTauCeti`
(10,473 jobs; `/tmp/smoothed-multiplicity-final-build.log`). Every Lean
build was preceded by `lake exe cache get`. The journal passed pdfLaTeX,
BibTeX and two further pdfLaTeX passes, producing a 56-page PDF at
`/tmp/dk-smoothed-multiplicity-paper/dk-smoothed-multiplicity.pdf`; the final
log has no warnings, overfull boxes, unresolved references or duplicate labels.
`git diff --check` passed. The original 29-result inventory and unrelated
submodules are unchanged. The editorial changes in `4759b700f` are preserved;
its older-snapshot status paragraphs are supplemented by these newer endpoints.

### Exact next obligations

For both complex penalties, prove path connectedness of each fixed-rank
complex projection space and of each balanced defect identification space,
then combine with the homeomorphisms and compiled clopen rank labels to
identify connected components. Manifold dimensions remain separate.

The actual smoothed gradient/stationarity reduction and two-phase spectral
blocks are now compiled in the newer entry above. The remaining analytic
step is a two-phase second variation, followed by overlap exclusion and
classification of the local zero-gradient reflection blocks. Smoothed
local-to-global is still open. Real matching and the Schatten/Charbonnier
ideal extensions retain their previously recorded obligations.

## Operator norm optimizer topology and separated rank sectors (25 October)

`SchattenParameterTopology.lean` proves
`exists_schatten_normalized_parameter_homeomorph` and
`exists_schatten_multiplicity_parameter_homeomorph`. These strengthen the
previous algebraic equivalences to genuine Lean `Homeomorph`s for the
**complete** finite complex ambient optimizer set, at finite `1<p<2`
and equal subspace ranks. The actual phase restrictions, both independent
right-defect actions and cosine-weighted phase equation remain conclusions.
Zero, critical, repeated and right angles require no exceptions or new
competitor hypotheses. All topologies use the accepted scoped Tau Ceti
operator-norm topology on linear isometry equivalences and the usual
operator-norm subspace topology on continuous linear maps.

The multiplicity theorem also proves that each actual projection rank
coordinate is locally constant and gives `k>0` such that different ranks
on any active factor imply `1 <= k*||T-S||`. This is a uniform positive
separation of different rank sectors for the **fixed** pair and exponent,
even when both defect unitaries vary. No sharp constant or uniformity as
the pair approaches a phase transition is claimed. Continuous optimizer
families on connected parameter spaces have constant rank labels, and
finite intersections of fixed-rank fibers are clopen. These follow from
the compiled `IsLocallyConstant` conclusions and Mathlib's fiber and
preconnected-space theorems. Connectedness of each whole rank sector,
exact component counts and manifold dimensions are not proved here.

`isCompact_schattenTransportMinimizers` proves operator-norm compactness.
`discreteTopology_schattenTransportMinimizers_of_simple_active_angles`
proves isolation of every optimizer when the active multiplicities are
one and the right defect is zero; the previously compiled exact count
is `2^s`. Inactive multiplicities remain unrestricted.

`Projection/ParameterTopology.lean` proves compactness of orthogonal
projection spaces and a homeomorphism for the joint supported paired
projection family. It also proves that idempotents at norm distance less
than one have equal rank (self-adjointness unnecessary), local constancy
of projection rank, and contraction of differences under invariant
restriction without finite dimension. `LinearIsometryEquivCompact.lean`
proves compactness of finite-dimensional isometric-identification spaces,
including empty and zero-dimensional cases, and continuity of rectangular
inversion. It consumes the accepted Tau Ceti topology directly. These
are classical ingredients, with no separate historical novelty claim.

The proof uses a compact-target closed graph argument and the existing
geometric uniqueness theorem. An explicit finite-sum extension formula
was unnecessary. The manuscript states the projection-product
homeomorphism in `thm:schatten-optimizer-topology`; the older subspace
rank-stratification equivalence remains algebraic. No new analytic
topology on Mathlib's `Module.Grassmannian` is introduced.

Validation: the focused topology module passed, followed by
`lake build DavisKahan.All ForTauCeti` (10,465 jobs;
`/tmp/schatten-topology-final-build.log`). Every Lean build was preceded
by `lake exe cache get`. The journal passed pdfLaTeX/BibTeX and two
further pdfLaTeX passes, producing a 55-page PDF at
`/tmp/dk-schatten-topology-paper/dk-schatten-topology.pdf`; the final log
has no warnings, overfull boxes, unresolved references or duplicate labels.
`git diff --check` passed. No source-result inventory, checker or unrelated
submodule was changed.

An independent eight-dimensional diagnostic combined a repeated active
angle (`p=1.5`, `theta=1.43`, multiplicity two), continuously varying
rank-one complex projections, rank-zero/two endpoints and a two-dimensional
independent right defect. The largest objective residual was `5.33e-15`
and transport residual `7.95e-16`. The rank-zero/rank-one distance was
`1.961572796758968`, matching `2*sin(optimalPhase)` in this block model.
This supports the diagnostic construction only; the general homeomorphism
and separation results are proved by Lean.

## Publication-facing claims at `427169ce` (25 October)

The journal abstract, contribution list, related work and conclusion may now
state **complete all-angle finite complex Schatten `1<p<2` optimizer
classification** in addition to its exact minimum. The complete classification
is already proved in `schatten_transport_verified.tex` and backed by
`SchattenNonacuteClassification.lean`, `SchattenParameterNormalization.lean`,
`SchattenMultiplicityParameters.lean` and
`SchattenPhaseDefectAttainment.lean`. All constrained local minima are global
by `SchattenLocalGlobal.lean` and `SchattenCorrectionLocalGlobal.lean`.
The multiplicity factors are *Grassmannian sets* (rank-stratified subspaces),
with a separate unitary defect identification; a homeomorphism and manifold
dimension theorem do not follow from the compiled set-level equivalence.
Simple active angle factors with no right defect give exactly `2^s`
minimizers. The all-angle Charbonnier minimizer classification in
`smoothed_transport_verified.tex` is likewise compiled; smoothed local-to-global
is not an established theorem. Do not promote the real matching, field-gap,
or infinite-dimensional Schatten-ideal extensions. Historical first-publication
priority is still under review. The public Manim deck `novelty-tour` now
explains binary phase choices, multiplicity-space continuum, and the
local-to-global statement, preserving the paper's source/target colors.

## Finite multiplicity-space coordinates and exact optimizer counts (25 October)

`SchattenMultiplicityParameters.lean` proves
`exists_schatten_multiplicity_parameter_equiv`: every finite complex
`1<p<2` optimizer corresponds bijectively to **independent arbitrary
orthogonal projections on every actual active multiplicity space**, plus
an arbitrary independent crossed-defect unitary. An active angle satisfies
`0<theta<pi/2`, `criticalAngle(p)<theta`, and has a nonzero actual canonical
rotation eigenspace at `exp(i*theta)`. Equal angles are grouped into that
one whole eigenspace. The theorem retains the actual phase restrictions,
both defect actions and cosine-weighted formula. It compares against all
ambient unitary transports, with no prescribed competitor frame.

`finite_schattenActiveRotationAngles` proves that there are finitely many
nontrivial factors. The support identification
`schattenPhaseWeight_orthogonal_ker_eq_paired_eigenspace_sum` proves that
the kernel complement of `C*(F-F.adjoint)` is **exactly** the sum of those
positive canonical eigenspaces and their reflected copies. The proof uses
the accepted complete canonical frame only to prove this intrinsic
subspace equality, not as a restriction on optimizer parameters. Zero,
critical, right and fixed directions are excluded from this effective
phase space by exact vanishing of the phase weight.

`nonempty_schatten_rank_stratified_parameter_equiv` replaces each projection
factor by the disjoint union, over `r=0,...,dim(N_theta)`, of all subspaces
of `N_theta` with dimension `r`. This is the **algebraic** finite product
of complex Grassmannian sets predicted by the research draft. The rank
strata are implemented by `Submodule` plus exact `Module.finrank`, with no
manifold or topological structure asserted. Mathlib's existing
`Module.Grassmannian` uses finite-projective quotient rank; it is a
different representation and was not duplicated or relabeled here.

`nonempty_schatten_boolean_parameter_equiv` proves that one Boolean per
active angle suffices when every active eigenspace has dimension one;
the defect unitary remains independent. The exact endpoint
`natCard_schattenTransportMinimizers_of_simple_active_angles` proves that
there are **exactly `2^s` ambient global optimizers** when those active
multiplicities are one and the source right defect has finrank zero.
Equal subspace ranks make the target right defect zero as well. Inactive
multiplicities are unrestricted. This is an exact count of the complete
optimizer set, beyond an independently constructed sign-family lower bound.

The donor `PairedProjectionFamily.lean` proves joint supported extension
and an actual projection-space `Equiv` for arbitrary distinct,
nonconjugate unit-circle eigenvalues of a unitary reversed by an
involution. The prescribed spaces are its actual eigenspaces. It also
proves `IsStarProjection.restrict_invariant`, for complete invariant
subspaces without finite ambient dimension. `Projection/FiniteParameters.lean`
supplies the projection/range and rank-stratification equivalences and the
two-element one-dimensional projection space. These are classical linear
algebra, with no separate historical novelty claim.

The manuscript includes Theorem `thm:schatten-multiplicity-parameters`
and Corollary `cor:schatten-simple-active-count`. Independent diagnostics
at `p=1.5` produced four distinct transports for two simple supercritical
angles (minimum pairwise distance `1.74034`) and checked four complex
rank-one choices in a repeated active angle space (largest cost/commutation
residual `3.55e-15`). These are diagnostics, not proofs. The exclusion of
conjugate coincidences is necessary in the donor: indexing both members
of one pair would permit inconsistent zero/identity prescriptions that
cannot commute with the reversing involution.

### Exact next proof obligations

The algebraic multiplicity factorization and operator-norm projection-product
homeomorphism are now compiled. Connected components require path
connectedness of the fixed-rank complex projection spaces and the balanced
defect identification space. The expected component count is
`product_theta (dim(N_theta)+1)` and the expected real stratum dimension
is `d^2 + sum_theta 2*r_theta*(m_theta-r_theta)`; neither is a compiled
endpoint. Installed Mathlib's local path connectedness of C*-unitary groups
alone does not establish the required global finite-dimensional result.

The Charbonnier multiplicity classification and topology are now compiled
in the later proof layer summarized at the beginning of this record.
Its relative-phase convention remains opposite to the pure Schatten
convention. Real matching, smoothed local-to-global and ideal optimization
remain open under their previously recorded hypotheses.
Historical priority of the nonlinear transport classification is still
provisional; the Grassmannian and projection ingredients are classical.

Validation: every Lean build was preceded by `lake exe cache get`.
The paired-family, finite projection-parameter and full multiplicity targets
passed, followed by `lake build DavisKahan.All ForTauCeti` (10,457 jobs;
`/tmp/schatten-multiplicity-final-build.log`). The journal passed
pdfLaTeX/BibTeX and two further pdfLaTeX passes, producing a 54-page PDF
under `/tmp/dk-schatten-multiplicity-paper/`; its final log has no warnings,
overfull boxes, unresolved references or duplicate labels.
`git diff --check` passed. The original 29-result source inventory is unchanged.

## Nonredundant complex optimizer parameters and recovery (25 October)

`SchattenParameterNormalization.lean` removes the ineffective freedom in
the complete operator classification. Define `B=C*(F-F.adjoint)`, where
`C` is the intrinsic cosine and `F=schattenPhaseFactor(p,C)`. The set
`schattenNormalizedPhaseProjections` consists of the compatible orthogonal
projections whose ranges lie in `(ker B).orthogonal`.

`schatten_transport_isMin_iff_unique_normalized_phase_and_defect_complex`
proves that **every** feasible finite complex transporter is globally
minimizing iff it has **exactly one** normalized phase/defect pair. All
angle degeneracies remain included. Every raw compatible projection is
normalized by multiplying it with orthogonal projection onto `(ker B).orthogonal`;
`exists_normalized_schatten_phase_projection` proves that this preserves
compatibility and its weighted phase formula.

`exists_schatten_normalized_parameter_equiv` proves an actual Lean `Equiv`
between the normalized projection space times the arbitrary crossed-defect
unitary space and `schattenTransportMinimizers`. It retains both actual
defect actions and the phase formula, and proves a finite constant `L>=0`
with `||P_T-P_S|| <= L*||T-S||` for every pair of optimizers. The pair and
exponent are fixed; no sharp or uniform-in-angle constant is asserted.

The coefficient is compiled exactly in `schattenPhaseWeight_apply_cos`:
on a physical cosine eigenvector it is
`2*i*cos(theta)*sin(optimalPhase(p,theta))`. The zero and one cosine
actions vanish. At each interior angle, the coefficient vanishes iff
`theta<=criticalAngle(p)`, including critical equality, as proved by
`schattenPhaseWeight_apply_eq_zero_iff_le_critical`. Thus the effective
phase space is precisely the supercritical interior part; all right-angle
freedom remains in the independent defect identification.

The supporting donor `Projection/KernelSupport.lean` works over real or
complex Hilbert spaces. Its uniform recovery bound assumes only that the
orthogonal complement of the multiplier's kernel is finite dimensional,
allowing an infinite ambient space. The downstream geometric recovery
theorem is `LinearIsometryEquiv.exists_pos_normalized_split_parameter_recovery`.
These are classical projection and finite-dimensional norm facts, with no
independent historical novelty claim or infinite-dimensional optimum claim.
`commute_cosine_of_commute_nonacuteDirectRotation` now shares the
dimension-free self-adjoint commutation argument; the previous coordinate
frame proof consumes it instead of keeping a duplicate.

The manuscript includes Theorem `thm:schatten-normalized-parameters`.
Six independent numerical mixed-angle diagnostics included zero, repeated
critical and supercritical angles and arbitrary complex right-defect
unitaries for `p=1.2,1.5,1.9`. The largest algebraic residual was
`1.55e-15`, with no recovery-bound violation. These diagnostics are not
proofs; the named endpoints are Lean-verified.

The multiplicity-space and rank-stratum identification is now compiled in
`SchattenMultiplicityParameters.lean`. The `Equiv` above is algebraic.
A homeomorphism, connected components and dimensions are not yet Lean
endpoints. The phase coordinate has a compiled
uniform Lipschitz inverse estimate; continuity of the full forward
phase/defect construction and its Grassmannian coordinates remains to be proved.

The next local extension ingredient is also compiled:
`exists_unique_paired_projection_extension` in
`ForTauCeti/Analysis/InnerProductSpace/PairedProjectionExtension.lean`.
Every orthogonal projection on a finite-dimensional subspace `N` orthogonal
to its reflected copy extends **uniquely** to a compatible ambient
projection supported on `N + J(N)`. The ambient Hilbert space can be
infinite dimensional. The former weaker existence theorem is removed,
and the Charbonnier multiplicity consumer uses the stronger result.
`PairedProjectionFamily.lean` now supplies the joint assembly over all
actual positive canonical rotation eigenspaces; the finite multiplicity
equivalence above consumes it.

Validation: `lake exe cache get` preceded each Lean build. Focused
normalization, kernel-support recovery and unique paired-extension targets
passed, followed by `lake build DavisKahan.All ForTauCeti` (10,449 jobs;
`/tmp/schatten-normalization-final-build.log`). This includes the migrated
Charbonnier consumers. The journal PDF built through pdfLaTeX/BibTeX and
subsequent pdfLaTeX passes, with 53 pages and no warnings, overfull boxes,
unresolved references or duplicate labels in its final log under
`/tmp/dk-schatten-normalized-parameters-paper/`. `git diff --check` passed.
The original 29-result source inventory is unchanged.

## Complete finite complex Schatten optimizer classification (25 October)

`SchattenNonacuteClassification.lean` now proves
`schatten_transport_isMin_iff_phase_and_defect_complex`. For any finite complex
equal-rank pair and any feasible ambient unitary `T`, at finite `1<p<2`,
global minimality is equivalent to the existence of an orthogonal projection
`P` commuting with the chosen completed canonical rotation `R` and source
reflection, together with a crossed-defect unitary `D`, such that

- `C*R.adjoint*T = C*(F*P + F.adjoint*(I-P))`, where `C` is the actual
  intrinsic cosine and `F=schattenPhaseFactor(p,C)`; and
- `T` acts by `D` and `D.symm` on the two actual crossed defects.

This is an unrestricted ambient **iff**, with no prescribed-block, acute,
simple-spectrum or cosine-preservation hypothesis on the competing `T`.
The reference completion in the endpoint is the existing named
`finiteCrossedDefectEquiv`; the independent optimizer defect `D` is arbitrary.
The projection in this earlier operator iff may be redundant on inactive
and right-angle sectors. The normalized extension above removes that
redundancy and proves a bijection.

`SchattenPhaseDefectAttainment.lean` proves
`exists_unique_schatten_transport_from_phase_and_defect_complex`: **every**
compatible phase projection and **every** defect identification occur jointly
in exactly one global optimizer with the prescribed data. Feasibility,
actual defect actions, weighted relative phase, exact principal-angle power
and comparison with all ambient competitors are conclusions. The unweighted
phase construction is `exists_schatten_transport_from_projection_complex`
in `SchattenProjectionAttainment.lean`.

The necessary witness is the intrinsic positive spectral projection
`1_(0,infinity)(Im(C*R.adjoint*T))`, proved by
`schatten_minimizer_positive_phase_projection_mod_kernel_complex`.
`SchattenNonacuteCommutation.lean` establishes whole-space canonical
commutation of `C*R.adjoint*T`, including right angles. It does not assert
whole-space commutation of the unweighted relative phase for arbitrary
right-defect actions.

`SchattenFunctionalPhase.lean` defines the finite spectral factor by the
unit-modulus scalar symbol `exp(i*optimalPhase(p,arccos(c)))`, proves
unitarity and its actual eigenvector actions, including `F(1)=1` and
`F(0)=i`. The right endpoint consumes the existing unique scalar right-angle
minimum. `SchattenFrameAttainment.lean` is the shared in-frame construction;
`SchattenSignedOptimizers.lean` now consumes it while preserving its earlier
public theorem signatures. No one fixed frame is assumed to diagonalize
every projection.

The checked manuscript includes Theorem
`thm:schatten-all-phase-defect-minimizers`. Corollary
`cor:schatten-phase-parameter-distance` uses the generic exact identity
`LinearIsometryEquiv.norm_sub_eq_of_right_relative_split` from
`Projection/UnitaryTransport.lean`. For two **full unweighted** relative-phase
representations it gives `||T-S||=||(F-F.adjoint)*(P-Q)||`. On a single
supercritical interior angle space this coefficient is `2*sin(delta)`.
This is a mathematical sensitivity identity, not an experimental guarantee
or a metric formula for arbitrary redundant right-defect parameters.

`SchattenCorrectionClassification.lean` transfers the complete iff to
literal Schatten-nearest subspace-preserving unitary correction:
`schatten_correction_isMin_iff_phase_and_defect_complex`. For a prescribed
unitary `A` and subspace `K`, the candidate `V` satisfies `V(K)=K`; all
ambient unitary competitors with that same constraint are compared.
Apply the transport classification to `(A(K),K)` and `T=V*A.adjoint`.
The comparison equivalence
`schatten_correction_isMin_iff_transport_power_isMin_complex` proves the
norm-to-power transfer for every positive finite Schatten exponent at
least one, without requiring feasibility of the compared candidate.
The manuscript includes Corollary `cor:schatten-all-nearest-commuting`.
This is a mathematical matrix-correction consequence, with no assertion
about numerical convergence, physical implementation or statistical error.

The phase/defect uniqueness proof is shared with the existing Charbonnier
endpoint through `Geometry/Polar/TransportUniqueness.lean`; the old
smoothed-only home of `transport_eq_of_phase_and_defect_actions_complex`
was removed. The new opposite-convention theorem
`transport_eq_of_right_phase_and_defect_actions_complex` is dimension-free:
only the reference rotation must preserve the cosine. Competing unitaries
need no feasibility, optimality or cosine commutation hypothesis. The two
defect actions also determine their inverse actions. These are classical
geometric statements, with no separate historical novelty claim.

## Intrinsic compatible phase projection on every interior angle space

`SchattenEqualAnglePhases.lean` proves
`relative_phase_add_star_on_angle_of_isLocalMinOn_complex`: for every finite
complex ambient local minimum at `1<p<2`, every supplied canonical defect
completion `R` and every physical `0<theta<pi/2`, the actual relative
unitary `Z=R.adjoint*U` satisfies
`Z*x+Z.adjoint*x = 2*cos(optimalPhase(p,theta))*x` on the **original**
sine eigenspace at `sin(theta)`. Other angles may be zero, critical or
right, and all multiplicities/empty eigenspaces are included.
`relative_phase_unique_projection_on_angle_of_isLocalMinOn_complex`
therefore constructs the actual invariant restriction `V` and its unique
orthogonal projection `P` when `theta>criticalAngle(p)`, with
`V=(cos(delta)-i*sin(delta))*I+2*i*sin(delta)*P`.

`SchattenEqualAngleCompatibility.lean` proves the stronger necessary form
`relative_phase_unique_compatible_projection_on_angle_of_isLocalMinOn_complex`:
the same unique projection commutes with the **actual restricted** canonical
rotation and source reflection. Their unitary restrictions and the optimizer's
relative restriction are all constructed. The proof first establishes
`relative_phase_commutes_canonical_on_angle_of_isLocalMinOn_complex`.
It does not assert whole-space commutation for arbitrary right-defect
completions. The checked manuscript includes Proposition
`prop:schatten-intrinsic-angle-parameter`.

The inactive branch is compiled as
`apply_eq_canonical_on_angle_le_critical_of_isLocalMinOn_complex`:
**every optimizer agrees with canonical rotation on each individual positive
angle space at/below the cutoff**, even when other angles are supercritical
or right. Zero-angle directions remain covered by `SchattenFixedDirections`;
right-angle sectors by the complete defect classification. No strictly
positive Hessian is invoked at critical angles or zero displacement.

The removal of the ambient acuteness hypothesis uses
`SchattenKernelAngles.lean`:
`gradient_kernel_sinAngleOperator_isStarProjection_of_isLocalMinOn_complex`
proves that the restricted intrinsic sine on the actual gradient kernel is
an orthogonal projection. This necessary fact holds for every finite complex
`p>1`, without an upper bound of two. Then
`mem_gradient_kernel_orthogonal_of_sin_eigenvector_of_isLocalMinOn_complex`
puts every sine eigenvector with value different from zero and one in the
orthogonal complement of that kernel. No kernel model is supplied.

The donor lemma
`Submodule.isStarProjection_sinAngleOperator_of_fixed_or_exchange_blocks`
is real/complex, needs no finite ambient dimension and no orthogonality of
the spanning block family. The symmetric-map lemma
`mem_orthogonal_of_eigenvector_of_idempotent_on_subspace` requires no dimension,
completeness or invariant-subspace assumption. The generic scalar-real-part
restriction `exists_restriction_add_star_eq_scalar_complex` allows an infinite
ambient Hilbert space and a finite invariant subspace; both zero- and nonzero-
phase cases consume the same restriction proof. These are classical geometric
and spectral facts, with no independent novelty claim or ideal attainment.

## Exact Schatten uniqueness and nearest commuting-unitary criterion

`SchattenCanonicalUniqueness.lean` proves
`eq_canonicalRotation_of_isLocalMinOn_angles_le_critical_complex`:
for finite complex `1<p<2`, **every ambient local minimum equals canonical
rotation** when all accepted principal angles are at most
`criticalAngle(p)`. It includes critical equality, repeated/zero angles,
empty spaces and arbitrary supplied defect completion. The bound makes
the pair acute. The complete trace identity, tested with the positive part
of `t-cap`, transfers the original bound to every actual paired mean.
The optimal phases vanish; both maps fix the actual gradient kernel.
The generic transfer is
`Submodule.paired_phase_mean_le_of_principalAngles_le_complex`.

`SchattenSignedOptimizers.lean` proves
`exists_schatten_minimizers_with_independent_phases_complex`: one frame
**derived from the input pair** realizes every independent attaining signed
scalar phase, with feasibility, actual eigenvector actions, the exact
principal-angle power and comparison against every ambient competitor.
The right-angle endpoint and empty spaces are included. The signed cost
identity now underlies the original nonnegative-phase identity; it is not
a duplicate cost implementation.

`exists_opposite_schatten_minimizers_complex` constructs two global
optimizers that coincide exactly in the closed canonical regime.
`schatten_transport_unique_minimizer_iff_complex` therefore proves
**unique optimizer iff every accepted angle is at most the critical angle**.
A direct isometric-equivalence formulation is also compiled.
These facts are included in `cor:schatten-unique-minimum` and strengthen
`cor:schatten-canonical-cutoff`.

`SchattenCommutatorCutoff.lean` proves the exact projection-gap cutoff
`2*sqrt(p-1)/p` for canonical optimality and optimizer uniqueness.
`schatten_correction_unique_minimizer_iff_commutator_complex` proves the
application: given any unitary `A` and source projection `P`, the
Schatten-nearest unitary commuting with `P` is unique **iff**
`||AP-PA|| <= 2*sqrt(p-1)/p`, including equality. Its proof is the full
bijection `C -> C*A.adjoint` from correction to transport, preserving the
literal Schatten power and all competitors. The positive power and norm
have the same minimizers. Included in
`cor:schatten-commutator-uniqueness`; no performance or physical claim.

`Projection/GapThreshold.lean` now owns the reusable real/complex closed
angle-bound criterion and unitary-image gap/commutator identity. The latter
holds on arbitrary complete Hilbert spaces with a projected source
subspace. `SmoothedCommutatorCutoff.lean` consumes them directly; the old
private angle-bound proof and complex finite-only commutator proof were
removed. These geometric identities are classical, with no separate
historical novelty claim. The full finite complex Schatten optimizer iff
is now compiled above. Real matching, smoothed local-to-global, parameter
topology and ideal extensions retain their explicit open boundaries.

## Canonical relative phases and acute whole-space commutation

The named canonical-rotation bridge is now compiled. In
`Geometry/Polar/PairedPhase.lean`,
`nonacuteDirectRotation_apply_of_paired_phase_eigenvectors` proves that
**every** completed canonical rotation has phases `theta,-theta` on the
same paired vectors as any feasible transporter with phases `alpha,-beta`
and nonnegative acute mean `theta=(alpha+beta)/2`. It includes zero mean,
needs no finite dimension, and assumes a crossed-defect isometry as input.
It therefore does not infer infinite-dimensional defect balance or ideal
attainment from feasibility alone.

The proof uses two reusable bridges:

- `nonacuteDirectRotation_mul_cosine_eq_canonicalIntertwiner`, in
  `NonacuteCompression.lean`, proves `R*C=QP+(1-Q)(1-P)` over either scalar
  field on any complete Hilbert space with projected subspaces and a
  supplied defect identification. No dimension, gap or closed-range
  hypothesis is used.
- `CosineKernel.cosine_apply_of_sinAngleOperator_eigenvector` recovers the
  physical cosine eigenvalue from a physical sine eigenvector by positivity
  and the intrinsic Pythagorean identity.

`positive_gradient_canonical_relative_phase_basis_of_isLocalMinOn_complex`,
in `SchattenOptimizerPhases.lean`, now retains the optimizer, canonical
rotation and actual relative phase `Z=R^*U` on one complete paired basis.
On each pair `R` has phases `+/-theta_i`, and `Z` has the **same** scalar
`exp(i*eps_i*optimalPhase(p,theta_i))` on both vectors. This applies to every
finite complex ambient local minimum at `1<p<2`, with every defect
completion, all multiplicities, critical angles and arbitrary right-angle
blocks elsewhere. The strengthened Proposition
`prop:schatten-all-signed-phases` is included.

`SchattenCanonicalCommutation.lean` proves
`commute_canonicalRotation_of_isLocalMinOn_acute_transports_complex`:
**every** local or global minimizing transporter commutes with canonical
rotation on the whole ambient space when all principal angles are acute.
Zero and critical angles, repeated angles, arbitrary finite rank and empty
spaces are included. The actual gradient kernel is fixed by both operators;
no supplied spectral frame or kernel restriction is assumed. The checked
manuscript includes Corollary
`cor:schatten-acute-canonical-commutation`.

The supporting theorem
`nonacuteDirectRotation_apply_eq_self_of_projections_eq` proves canonical
fixation wherever `P*x=Q*x`, over arbitrary real/complex complete Hilbert
spaces and every supplied defect completion. These geometric statements
are classical polar/projection mathematics with no separate novelty claim.

### Exact continuation after canonical commutation

The relative scalar-real-part equation, its unique supercritical projection
and its compatibility with canonical rotation and source reflection are
now compiled on every interior angle space, including nonacute ambient pairs.
The earlier necessary-parameter obstruction is closed. Canonical uniqueness,
its converse and independent scalar sign attainment also remain compiled.

### Exact remaining proof obligations and next theorem

The preceding necessary-parameter, compatible-attainment and complete
nonacute ambient iff obligations are now closed. The exact relative phase
orientation is `R.adjoint*T`; older smoothed formulas often use
`T.adjoint*R`. The shared geometry distinguishes these conventions.

The nonredundant parameter bijection and its multiplicity-space
factorization are now compiled in `SchattenParameterNormalization.lean`
and `SchattenMultiplicityParameters.lean`. A compatible projection restricts
to each actual positive canonical rotation eigenspace at `exp(i*theta)`;
source reflection determines its action on the conjugate space. The joint
theorem `exists_unique_unitary_paired_projection_family` realizes every
tuple by projecting onto the sum of its ranges and reflected ranges,
with support on precisely the selected paired sectors. Inactive and
right-angle projection parameters are zero. The complete finite product
and its rank-stratum form are now proved. The exact next topological
obligations are stated at the beginning of this record.

The Grassmannian manifold identification, component dimensions and homeomorphism
remain conventional until their exact coordinate/topology statements are
proved. The generic exact operator-distance identity now supplies the
single-angle metric comparison. Do not infer a formal manifold theorem from
the operator iff or a generic parameter-separation bound.

After these consequences, continue unrestricted real matching from the
actual real gradient blocks and the exact four-dimensional determinant
classes. The full real lower bound and its parity/field-gap refinements are
still open. Infinite-dimensional optimality still needs ideal definitions,
defect-index feasibility, convergence and attainment; the finite spectral
symbol's arbitrary finite-spectrum continuity does not supply these.
Historical priority of the full complex classification remains provisional.

The shared paired-diagonal extension now lives in
`OrthonormalBasis.exists_paired_diagonal_commuting_involution`, in the
real/complex donor `DiagonalUnitary.lean`. Both nonnegative and independently
signed attainment consume it; the old paper-local construction was removed.
This is classical reusable geometry with no separate novelty claim.

Validation: focused frame attainment, spectral factor, arbitrary compatible
projection, joint phase/defect, full nonacute iff and nearest-correction
classification modules passed.
`lake exe cache get` preceded the final
`lake build DavisKahan.All ForTauCeti` (10,445 jobs;
`/tmp/schatten-classification-final-build.log`). All prior Charbonnier
consumers also passed after the geometry migration. The original 29-result
source inventory is unchanged. The manuscript passed pdfLaTeX/BibTeX and
two further pdfLaTeX passes, producing a 53-page PDF under
`/tmp/dk-schatten-full-classification-paper/`; the final LaTeX log has no
warnings, overfull boxes, unresolved references or multiply defined labels.
`git diff --check` passed. Build evidence verifies the formal statements;
historical priority remains provisional.

## Actual signed optimal phases of every pure Schatten optimizer

`SchattenOptimalPhase.lean` now supplies the named scalar function
`optimalPhase p theta`, an attaining phase for `p>=1,theta>=0`, with zero
as its explicitly defined value outside those hypotheses. For positive
acute angles at `1<p<2`, it is the **unique** nonnegative attaining phase.
The compiled API includes:

- `optimalPhase_spec` and `phasePower_eq_phaseMinimum_iff_eq_optimalPhase`;
- `optimalPhase_eq_zero_iff_le_criticalAngle`, including equality;
- `optimalPhase_mem_Ioo_of_supercritical`;
- `chord_pair_eq_minimum_iff_optimalPhase_signs`, a two-way classification
  of every nonnegative attaining phase pair with prescribed acute mean.

The individual bounds `0<alpha_i,beta_i<pi` are now retained in the actual
level basis, the whole positive-gradient basis and the ambient spectral
decomposition. Their public names are unchanged; their conclusions are
stronger, and all registered consumers have been migrated. No principal
phase branch is inferred merely from an exponential eigenvalue.

`SchattenOptimizerPhases.lean` now proves
`positive_gradient_optimal_phase_basis_of_isLocalMinOn_complex`.
For **every ambient finite complex local minimum**, it constructs a
complete orthonormal basis `v_i` of the actual positive-gradient space,
actual acute angles `theta_i` and signs `eps_i=+1` or `-1` satisfying

- `U v_i = exp(i*(theta_i+eps_i*optimalPhase(p,theta_i))) v_i`;
- `U J v_i = exp(i*(-theta_i+eps_i*optimalPhase(p,theta_i))) J v_i`;
- the actual intrinsic sine operator has eigenvalue `sin(theta_i)` on
  both vectors.

Here `J` is the original source reflection. Its image supplies the complete
negative-gradient space through the already compiled spectral decomposition.
The statement includes empty positive spaces, repeated angles/levels,
critical angles and arbitrary zero/right-angle blocks elsewhere. At and
below the threshold the two signed expressions coincide, as the named
phase is zero. The checked manuscript includes Proposition
`prop:schatten-all-signed-phases`.

### Intrinsic bridge at that snapshot, now closed

The newer entry above proves the named canonical action on the same paired
basis, its actual relative phases and acute whole-space commutation.
The remaining step is the intrinsic equal-angle scalar-real-part/projection
equation and converse compatible-projection attainment, with the already
proved arbitrary defect parameter. The existing smoothed projection frame
and signed projection constructions provide a proof model; their pure
Schatten cost certification remains required.

This signed-basis theorem is **necessary structure for every optimizer**.
It does not yet certify the intrinsic phase-projection iff theorem,
Grassmannian topology, the real parity/matching formulas or ideal extensions.
The scalar facts are existing mathematics packaged for the operator
classification; historical priority of the complete transport theorem
remains provisional.

Validation: `lake exe cache get` preceded the focused builds and final
`lake build DavisKahan.All ForTauCeti`, which passed (10,411 jobs;
`/tmp/schatten-signed-phases-final-build.log`). The new named-phase and
optimizer-phase modules have no new warnings. All consumers of the
strengthened decomposition statements pass the aggregate. BibTeX and
repeated pdfLaTeX passes produced
`/tmp/dk-schatten-signed-phases-paper/dk-schatten-signed-phases.pdf`, with no
unresolved references/citations, multiply defined labels or overfull boxes.
`git diff --check` passed.

## Complete pure Schatten right-angle defect parameters

For every finite complex ambient local minimum at `1<p<2`, the whole
intrinsic sine-one space lies in the **actual gradient kernel**. Therefore
the transporter is self-adjoint on the entire crossed-defect sum and
acts by exactly one unitary identification `D` of the source and target
defects, with `D.symm` on the other defect. No acuteness, multiplicity,
supplied block, or complementary-spectrum restriction is imposed.

Compiled in `SchattenRightDefect.lean`:

- `gradient_eq_zero_of_sinAngleOperator_eq_self_of_isLocalMinOn_complex`;
- `selfAdjoint_on_right_defect_of_isLocalMinOn_transports_complex`;
- `exists_unique_defect_equiv_of_isLocalMinOn_transports_complex`.

The converse and independence are now compiled in
`SchattenDefectReplacement.lean`:
`exists_unique_schatten_minimizer_prescribing_defects_complex`.
For **any** such local optimizer and **any** unitary `D` between the
actual defects, it constructs exactly one global optimizer with those
defect actions and the original optimizer's entire action on the
orthogonal complement of the right-angle space. The conclusion includes
the exact scalar principal-angle sum and comparison with **all ambient
unitary competitors**. Zero defects and empty ambient spaces are included.
This classifies the right-defect parameter; it does not parameterize the
remaining positive acute equal-angle action.

Shared compiled ingredients:

- `LinearMap.IsSymmetric.apply_eq_zero_of_eigenvector_of_basis`, in
  `InvariantKernel.lean`, is a finite orthonormal-basis orthogonality
  criterion. It needs neither ambient completeness nor a separate finite
  dimension instance, and its annihilating map need not be symmetric.
- `CosineKernel.lean` identifies sine-one vectors with the kernel of the
  intrinsic cosine, and proves that sine commutation implies cosine
  commutation. Both results hold on arbitrary real/complex complete
  Hilbert spaces with projected subspaces; no ideal conclusion follows.
- `KernelCostSplitting.schatten_transport_split_cosine_kernel` proves the
  actual cost split `cost(T)=cost(Tpos)+2^(p-1)*dim(ker C)` over either
  scalar field, for **every finite `p>=1`**, given feasibility, cosine
  commutation and reflection on that kernel. Its cost-invariance theorem
  handles two transports agreeing on the complement.
- `KernelTransportReplacement.exists_transport_prescribing_defects`
  constructs the actual ambient extension over either scalar field,
  without optimality of the input. The existing Charbonnier replacement
  theorem now consumes this shared geometry; its public statement is
  unchanged.

The checked manuscript includes Proposition
`prop:schatten-all-right-defects`. The scalar right-angle mechanism and
unitary defect geometry are classical: BLR (2001), Lemma 3.3, already
classifies the planar right-angle choices. No independent historical
novelty is claimed for these ingredients. Priority of the complete
angle-dependent transport theory remains provisional.

### Remaining positive-angle parameter theorem

At this snapshot the remaining operator-classification sector was the
positive acute equal-angle action and its converse parameter construction.
The newer entry above now retains the individual phase bounds and proves
the actual signed optimal-phase basis. The intrinsic relative-phase
operator assembly and converse projection-parameter attainment remain.
The right-angle extraction, arbitrary attaining replacement and zero-angle
fixation are closed.

Validation: `lake exe cache get` preceded the focused builds and final
`lake build DavisKahan.All ForTauCeti`, which passed (10,407 jobs;
`/tmp/schatten-right-defect-final-build.log`). The new donor passes strict
ForTauCeti warnings, and the new Schatten modules have no new warnings.
The aggregate also validates the migrated Charbonnier consumers. BibTeX
and repeated pdfLaTeX passes produced
`/tmp/dk-schatten-right-defect-paper/dk-schatten-right-defect.pdf`, with no
unresolved references/citations, multiply defined labels or overfull boxes.
`git diff --check` passed.

## Every pure Schatten optimizer preserves angles and fixes zero angles

The next classification step is now compiled at arbitrary finite complex
rank for `1<p<2`, for **every ambient constrained local minimum** and
therefore every global optimizer:

- `commute_sinAngleOperator_of_isLocalMinOn_transports_complex`, in
  `SchattenOptimizerAngles.lean`, proves `U*|P-Q|=|P-Q|*U` for the original
  source and target projections. The actual paired-gradient eigenbasis
  and actual kernel restriction are derived, not supplied.
- `sinAngleOperator_apply_transport_of_isLocalMinOn_complex` proves the
  eigenvector equation directly;
  `map_sinAngleOperator_eigenspace_of_isLocalMinOn_complex` proves that
  **every** eigenspace of the intrinsic sine operator is mapped onto
  itself. The sine is injective on `[0,pi/2]`, so unequal principal
  angles cannot mix. Empty, repeated, zero and right-angle eigenspaces
  are included. These statements do not yet classify phase operators
  within an equal-angle space.
- `apply_eq_self_of_projections_eq_of_isLocalMinOn_transports_complex`,
  in `SchattenFixedDirections.lean`, proves `U*x=x` whenever `P*x=Q*x`.
  Thus both common source vectors and common orthogonal ambient
  directions are fixed, with no acuteness assumption on the remaining
  pair. The proof constructs the actual reducing zero-angle restriction,
  inherits local minimality, and applies the exact value theorem to the
  coincident restricted pair. Its attained value is zero.

Reusable ingredients:

- `Submodule.commute_sinAngleOperator_of_selfAdjoint_transport`, in
  `Projection/ReflectionTransport.lean`, proves angle preservation by
  any reflecting transporter on a real or complex complete Hilbert
  space. It uses no finite-dimensional or minimization hypothesis:
  reflection conjugation negates the projection difference, so the
  reflection commutes with its squared difference and modulus.
- `Submodule.sinAngleOperator_comap_subtype_apply_of_invariant`, added
  to `Projection/InvariantSubspace.lean`, identifies the actual sine
  restriction on **every vector** for a finite-dimensional reducing
  pair. It extends the already compiled eigenvector identity by the
  positive restricted sine eigenbasis.

The checked manuscript includes Proposition
`prop:schatten-angle-preservation`. These theorems close unequal-angle
mixing and zero-angle rigidity in the full pure Schatten classification.
The newer entry above closes the right-angle defect intertwiner and its
arbitrary attaining replacement. The remaining parameter theorem must
classify phases on each positive acute equal-angle space and prove
attainment of every such phase parameter. No Grassmannian topology,
real matching or ideal-theoretic optimizer claim is promoted by this step.
Historical priority remains provisional; the reflection and restriction
lemmas are classical geometry without a separate novelty claim.

Validation: `lake exe cache get` preceded the focused builds and final
`lake build DavisKahan.All ForTauCeti`, which passed (10,403 jobs;
`/tmp/schatten-optimizer-geometry-final-build.log`). The new donor modules
pass the strict ForTauCeti warning policy; the two new DavisKahan modules
have no new warnings. BibTeX and repeated pdfLaTeX passes produced
`/tmp/dk-schatten-optimizer-geometry-paper/dk-schatten-optimizer-geometry.pdf`
with no unresolved references or citations, multiply defined labels or
overfull boxes. `git diff --check` passed.

### Precise continuation for the remaining parameter classification

On each intrinsic sine eigenspace with `0<s<1`, put `theta=arcsin(s)`
and choose its canonical rotation `R`. For the relative phase `Z=R^*U`,
prove commutation with `R` and the source grading, and prove
`Z+Z^*=2*cos(delta_p(theta))*I`. On the actual paired-gradient basis,
the sine eigenvalue equation fixes `(alpha+beta)/2=theta`; scalar phase
uniqueness should then give `abs((alpha-beta)/2)=delta_p(theta)`.
Assemble these equations on the entire eigenspace. The already compiled
`UnitaryScalarRealPart.lean` projection/involution classification then
supplies the unique projection parameter when `delta>0`, while `delta=0`
forces identity. This step must retain multiplicities and the critical
case rather than assuming simple angles.

At that snapshot the `s=1` task was to prove that the whole right-angle
eigenspace lies in the actual gradient kernel: every positive-gradient paired mean is strictly
acute. The actual restriction is therefore self-adjoint. In source/target
coordinates it should have off-diagonal factors `A,A^*`, with arbitrary
unitary `A` between the defect spaces. Prove the converse attainment
for every such factor. The newer right-defect entry above closes this task.
Combine it with the positive-angle projection parameters and the already
fixed `s=0` sector. The parameter topology and
dimension statements remain beyond these operator identities.

## Full finite complex Schatten local-to-global theorem

The unrestricted no-spurious-local-minima theorem is now Lean-verified.
For **every finite-dimensional complex Hilbert space**, `1<p<2`, equal-rank
subspaces `K,L`, and **every feasible ambient unitary** `U`, local minimality
of `||I-U||_p^p` implies

`||I-U||_p^p = sum_i phaseMinimum(p, principalAngle_i(K,L))`.

Thus every local minimum is global. The norm itself has the same result.
No acute-pair assumption, supplied block model, angle multiplicity
restriction, spectral endpoint exclusion, or restriction on the competing
unitaries is used. Zero and right angles, fixed directions, empty kernels,
and eigenvalues `1,-1` are included.

Compiled endpoints in `SchattenLocalGlobal.lean`:

- `schatten_transport_cost_eq_sum_of_isLocalMinOn_complex`;
- `isMinOn_of_isLocalMinOn_transports_complex`;
- `isMinOn_schatten_of_isLocalMinOn_transports_complex`.

`SchattenCorrectionLocalGlobal.lean` proves the application for any input
unitary `A` and prescribed subspace `K`: every local minimum of `||A-V||_p`
among **all ambient unitaries preserving `K`** is globally nearest. Its
powered version also compiles. The endpoints are
`isMinOn_correction_of_isLocalMinOn_preserving_subspace_complex` and
`isMinOn_schatten_correction_of_isLocalMinOn_preserving_subspace_complex`.
The continuous change of variables is `T=V*A^*`, from correction to
transport of `A(K)` back to `K`. No algorithmic convergence is claimed.

### How the exceptional cost obstruction was closed

Three small reusable donors prove the Frobenius route proposed in the
preceding snapshot:

- `SchattenFrobenius.lean`: the finite singular-value power sum, the bound
  `M^(p-2)*||B||_F^2 <= ||B||_p^p` for singular values bounded by `M`,
  its unitary-displacement specialization `M=2`, and equality for every
  self-adjoint unitary. The lower bound assumes `1<=p<=2`; reflection
  equality holds at every finite Schatten exponent at least one.
- `Projection/FixedRightCompression.lean`: the source-diagonal compression
  of a reflection with a spanning fixed/exchange family is an orthogonal
  projection. This lemma needs no finite ambient dimension or orthogonality
  of the family; it assumes a finite family spanning the entire space.
- `UnitaryTransportFrobenius.lean`: positive source-diagonal compression
  certifies maximal real trace and minimal Frobenius displacement over
  **all** real or complex finite unitary transports of the source. For a
  reflection this certifies global Schatten optimality at `1<=p<=2`.
  `schatten_transport_le_of_fixed_or_exchange_blocks` assembles the
  certificate directly from the family.

Applied to the actual gradient-kernel reflection, the certificate gives
an upper bound by the already constructed attaining kernel transporter;
the existing global lower bound gives the reverse inequality. This proves
kernel cost equality without reindexing its restricted principal-angle
list. The existing cost-deficit identity gives the ambient theorem.
The checked manuscript now includes Lemma
`lem:schatten-reflecting-certificate`, Theorem
`prop:schatten-local-is-global` and Corollary
`cor:schatten-correction-local-global`. The former conditional label
`prop:schatten-local-global-no-minus-one` aliases the stronger theorem.

### Exact next mathematical target

Assemble the **pure Schatten all-optimizer parameters** from the actual
paired gradient eigenbasis and the now completely controlled kernel.
The missing bridge identifies the phase factors on each eigenspace of
its geometric cosine operator: below and at the critical angle only the
canonical factor is permitted; a supercritical acute multiplicity block
has the two scalar optimal phases, hence a unique orthogonal-projection
parameter. Unequal-angle reduction and zero-angle pointwise fixation are
now compiled in the newer entry above. Prove both directions of the
remaining equal-angle operator formula. At right angles,
classify and attain the arbitrary defect-space unitary intertwiner;
zero angles and fixed ambient directions are now proved fixed. The
remaining parameter assembly statements remain conventional, not compiled endpoints.

The all-local-minima result proved here is **complex, finite-dimensional,
`1<p<2`**. It does not establish a real local landscape, the real matching
formula, Charbonnier local-to-global optimality, the nuclear local landscape,
or operator-ideal feasibility, convergence, classification or attainment.
The generic real/complex certificate is useful for those directions but
supplies none of those missing statements by itself. Historical priority
of the constrained landscape theorem remains provisional; the trace and
bounded-power comparisons are classical.

Validation: `lake exe cache get` preceded the focused builds of all five
new modules and the final `lake build DavisKahan.All ForTauCeti`, which
passed (10,397 jobs; `/tmp/schatten-local-global-final-build.log`). The
existing complex trace-defect wrapper now consumes the generic real/complex
Frobenius identity, and its smoothed consumers passed the aggregate build.
BibTeX and repeated pdfLaTeX passes produced
`/tmp/dk-schatten-local-global-paper/dk-schatten-local-global.pdf`, with no
unresolved references or citations, multiply defined labels or overfull
boxes. `git diff --check` passed.

## Complete reflecting-kernel geometry after `276828432`

The missing **planar normal form and its application to actual invariant
planes** are now compiled. No real reflecting matrix, basis, orthogonal
decomposition, or restricted source operator is supplied at the ambient
endpoint. Let `P` be an orthogonal projection, `T` an ambient unitary,
and `N` any common invariant complex plane on which `T^2=I`.
If `T` is a local minimum against **all ambient feasible unitaries**, then
`T` fixes `N` pointwise or `T(P(T(x)))=x-P(x)` for every `x` in `N`.
This is a necessary condition for every finite Schatten exponent `p>1`.
It includes zero and full source restrictions and the identity and
negative identity cases.

- `PlanarReflection.exists_source_reflection_coordinates`, in
  `ForTauCeti/Analysis/InnerProductSpace/PlanarReflection.lean`, constructs
  the actual coordinate isometry for a nonconstant source projection and
  a self-adjoint unitary other than `+I,-I`. It gives `P=diag(1,0)` and
  `R=[[-d,-k],[-k,d]]` in the same coordinates, with `d^2+k^2=1`, `k>=0`.
  `exists_diagonal_conjugate_real_reflection` proves the diagonal gauge
  lemma, including a vanishing off-diagonal coefficient. The source basis
  comes directly from Mathlib's ordered symmetric eigenbasis.
- `eq_one_or_conjugate_eq_one_sub_of_isLocalMinOn_reflecting_plane_complex`,
  in `SchattenReflectingPlanes.lean`,
  proves the whole-plane alternative for every source projection.
  `conjugate_eq_one_sub_of_isLocalMinOn_reflecting_plane_complex`
  gives its nonidentity, nonconstant-source branch.
- `fixes_or_exchanges_source_complement_on_invariant_plane_of_isLocalMinOn_complex`
  is the unrestricted **ambient** endpoint. Only the actual restriction
  is assumed involutive; all other ambient eigenvalues are unrestricted.
  Its conclusion concerns the original operators on actual vectors.
- `eq_one_of_isLocalMinOn_selfAdjoint_commuting_complex` and
  `fixes_invariant_subspace_of_isLocalMinOn_involutive_commuting_complex`
  exclude every nonidentity source-commuting reflecting block, in any
  finite dimension and for every finite `p>=1`. The source operator in
  these two statements need only be self-adjoint. Thus the nuclear
  endpoint is included in the commuting-block exclusion, not in the
  noncommuting-plane classification.
- `SchattenTransportRestriction.lean` now constructs actual unitary
  restrictions and their inherited local minima in
  `exists_isLocalMinOn_restriction_of_invariant`, over real or complex
  scalars. It assumes common invariance and a self-adjoint source.
  `isLocalMinOn_transport_of_conj_linearIsometryEquiv` handles arbitrary
  coordinate changes and arbitrary source operators. Both use the
  existing finite Schatten additivity and isometry invariance APIs.
- `fixes_or_exchanges_source_complement_on_small_invariant_block_of_isLocalMinOn_complex`
  includes every actual block of dimension at most two. Its exchange
  alternative explicitly forces dimension two. The dimension-one step
  consumes `ContinuousLinearMap.commute_of_finrank_le_one`, proved over
  arbitrary `RCLike` scalars with no inner-product or completeness
  assumption.
- `exists_fixed_or_right_orthogonal_blocks_of_isLocalMinOn_reflection_complex`
  constructs a **complete orthogonal family** for a reflecting local
  minimum from its source and negative-phase projections. Every nonzero
  block is fixed or exchanges its source and complement; all have
  dimension at most two.
- `gradient_kernel_fixed_or_right_blocks_of_isLocalMinOn_transports_complex`
  derives that family on the **actual gradient kernel of every ambient
  local minimum**, at arbitrary rank. The unitary restriction, restricted
  source projection, negative-phase projection and family are constructed.
  No supplied model, frame, prescribed pairing, gap, or positive-angle
  hypothesis is assumed. This holds for every finite complex Schatten
  exponent `p>1`, including an empty kernel and arbitrary remaining
  ambient eigenvalues.

The checked manuscript includes Proposition
`prop:schatten-intrinsic-reflecting-plane` and Corollary
`cor:schatten-kernel-fixed-right`. The alternative is necessary,
not a general sufficiency theorem for every `p>1`: for `p>2`, a
right-angle reflection need not be optimal. The normal-form ingredients
are classical projection and matrix geometry and carry no separate
historical novelty claim. Historical priority of the full constrained
transport theory remains provisional.

### Obstruction at that snapshot, now closed

At this snapshot the complete fixed/right kernel family was proved, but
its numerical cost equality was still open. The alternative Frobenius
comparison and positive-compression argument were only conventional.
The newer entry above proves those ingredients and the unrestricted
local-to-global theorem. Earlier chronological records below retain the
scope of their own snapshots.

Validation: `lake exe cache get` preceded every Lean build. The normal-form,
intrinsic-plane, commuting-block and full actual-kernel targets passed.
`lake build DavisKahan.All ForTauCeti` passed (10,387 jobs;
`/tmp/reflecting-kernel-final-build.log`), through the ordinary aggregate
imports. BibTeX and repeated pdfLaTeX passes produced
`/tmp/dk-reflecting-kernel-paper/dk-reflecting-kernel.pdf`, with no unresolved
references or citations, multiply defined labels or overfull boxes.

## Reflecting-block descent after `5c2ca4ad2`

The previously missing **analytic descent** is now compiled, including
the endpoint parameters `d=+1,-1`. Let `d^2+k^2=1`,
`S=[[-d,-k],[-k,d]]`, `P0=diag(1,0)` and
`W(t)=S*diag(exp(i*(d+1)*t/2),exp(i*(d-1)*t/2))`.

- `TauCeti.reflectingPhasePower_second_order`, in
  `SchattenReflectingPhases.lean`, proves the Peano expansion
  `2^p - p*2^p*d^2*t^2/8 + o(t^2)` for `p>1`. The scalar statement even
  allows arbitrary real `d`, because inverse-sine regularity is only local.
  `reflectingPhasePower_strict_descent` gives strict improvement at all
  sufficiently small nonzero steps when `d!=0`.
- `ReflectingVariation.schatten_displacement_variation` identifies the
  scalar formula with the **actual finite Schatten cost** of `W(t)` by
  its trace and determinant. `variation_mem_unitary`, `variation_transports`
  and `continuous_variation` certify a continuous feasible curve for all
  real steps. `not_isLocalMinOn_reflecting_transports` excludes local
  minimality against all planar feasible unitaries. These statements
  require `d^2+k^2=1`; they do not exclude either endpoint or repeated roots.
- `reflecting_block_eq_zero_of_isLocalMinOn_transports_complex` lifts
  that exclusion through any orthogonal complementary unitary block.
  It applies to an unrestricted ambient local minimum and forces `d=0`.
  The exponent can be any finite Schatten exponent greater than one,
  not just the campaign's `1<p<2` regime.
- `ReflectingVariation.not_isLocalMinOn_negative_identity` excludes a
  nonzero negative identity block for every finite `p>=1`, including
  the nuclear endpoint. The ambient version is
  `not_isLocalMinOn_of_negative_identity_block_complex`.
  `not_isLocalMinOn_of_negative_identity_on_invariant_subspace_complex`
  starts with an actual nonzero source-invariant subspace on which the
  transporter acts as `-I`: it constructs its reducing complement and
  coordinates. The source operator need only be self-adjoint.
- `no_neg_one_of_isLocalMinOn_transports_of_source_invariant_complex`
  excludes the entire negative eigenspace if it is source-invariant,
  for any finite `p>=1`. Consequently
  `isMinOn_of_isLocalMinOn_transports_of_negative_eigenspace_invariant_complex`
  proves a constrained local minimum is global for `1<p<2` under this
  invariance hypothesis. This strengthens the earlier no-`-1` endpoint:
  local minimality now derives absence of `-1`. No invariance of the
  other spectral spaces is assumed. The manuscript proposition
  `prop:schatten-local-global-no-minus-one` includes the stronger result.
- The reusable
  `isLocalMinOn_block_transport_of_orthogonal_sum` transfers local
  minimality to any unitary block over either scalar field, with no
  assumptions on the source operators. The trace/determinant cost lemma
  `schatten_displacement_rpow_eq_of_trace_det_fin_two` applies to any
  normal complex planar operator, including coincident eigenvalues.

The vanishing displacement contribution is handled by a second-order
Peano bound on its **phase**, not by twice differentiating the Schatten
cost at a zero singular value. The small-phase cost is `O(abs(t)^(2*p))`,
which is enough for `o(t^2)` when `p>1`. The stronger cubic coefficient
checked in earlier SymPy diagnostics is not a compiled endpoint.
The included manuscript now states Proposition
`prop:schatten-reflecting-descent` with these hypotheses.

### Remaining obligation at that snapshot

The analytic variation was closed at that snapshot. The next task was to derive the normal
coordinates from **every actual small common invariant block** of the
source projection and the negative spectral projection of the gradient
kernel reflection. The existing
`exists_orthogonal_blocks_of_two_projections` supplies a complete orthogonal
family of nonzero blocks of dimension at most two. Negative identity
blocks are now excluded intrinsically. A rank-one source projection on
each remaining traceless reflecting plane still needs the explicit unitary
normal form `P0=diag(1,0)`, `S=[[-d,-k],[-k,d]]` with real `d,k`.
The compiled ambient exclusion then forces `d=0`, leaving only zero and
right angles. Reassembly with the existing gradient-kernel cost-deficit
identity would prove that every constrained local minimum is global.
The newer entry above closes the normal coordinates and actual-plane
classification. At that snapshot the unrestricted conclusion was **not yet Lean-verified**;
the current entry above closes it. Full pure
Schatten optimizer parameter assembly, real matching and operator-ideal
attainment remain separate open formal targets.

No historical-priority claim is made for Taylor expansion, orthogonal
block restriction or this classical descent construction. The closest
local-to-global precedent rechecked here is Massey--Rios--Stojanoff,
*Local Lidskii's theorems for unitarily invariant norms* (2018), Theorems
3.5 and 3.12: their domains are fixed-eigenvalue self-adjoint orbits and
fixed-singular-value matrix orbits, respectively. An implication for the
prescribed-projection transport fiber would need an additional reduction.
See the novelty review for the primary source and the priority boundary.

Validation: `lake exe cache get` preceded every build. The scalar, planar,
block-lifting, intrinsic negative-block and stronger local-to-global
targets passed. The final `lake build DavisKahan.All ForTauCeti` passed
(10,383 jobs; `/tmp/reflecting-final-build.log`), including all additions
through the ordinary aggregate imports. The manuscript was rebuilt with
BibTeX and repeated pdfLaTeX passes, without unresolved references or
citations, multiply defined labels or overfull boxes, at
`/tmp/dk-reflecting-descent-paper/dk-reflecting-descent.pdf`.

## Complete all-angle Charbonnier classification after `f51c60f13`

The full finite complex ambient iff is now compiled, including every
zero, repeated, critical, supercritical and right angle and arbitrary
fixed directions. The pair has equal ranks. Weighted results assume
`0<b<a`; literal Charbonnier results assume `tau>0`. Write `R` for the
completed canonical rotation, `C` for the actual principal cosine,
`Z=T.adjoint R`, and `U=weightedPhaseFactor a b C`. Write
`F_P=U P+U.adjoint (I-P)`.

- `SmoothedNonacuteClassification.minimizing_weighted_transport_positive_phase_projection_mod_kernel_complex`
  constructs `P=1_(0,infinity)(Im(C*Z))` for every ambient optimizer.
  It is an orthogonal projection commuting with `R` and source reflection,
  vanishes on `ker C`, and satisfies `C Z=C F_P`.
- `minimizing_weighted_transport_iff_phase_and_kernel_complex` and
  `smoothed_transport_isMin_iff_phase_and_kernel_complex` prove the full
  iff: a feasible transporter is globally minimizing exactly when it is
  self-adjoint on `ker C` and has that compatible weighted phase formula.
  Cosine commutation is **derived**, not an additional condition on the
  candidate. In particular this is an unrestricted ambient classification.
- `smoothed_transport_isMin_iff_phase_and_defect_equiv_complex` replaces
  kernel self-adjointness by a unique actual unitary identification of
  the crossed defects, paired with its inverse action. The geometric
  reverse implication is compiled in
  `CosineKernel.selfAdjoint_on_cosine_kernel_of_defect_equiv` and the
  corresponding iff; these hold on arbitrary real/complex Hilbert spaces.
- `SmoothedPhaseDefectAttainment.exists_unique_weighted_transport_from_phase_and_defect_complex`
  and `exists_unique_smoothed_transport_from_phase_and_defect_complex`
  take **any** orthogonal `P` commuting with `R,J` and **any** crossed-defect
  unitary `D`. They produce exactly one ambient transporter with the
  prescribed phase formula modulo `ker C` and actions `D,D.symm`.
  Exact value and comparison against all ambient transporters are compiled.
  These construction theorems even allow redundant kernel values of `P`.
  `transport_eq_of_phase_and_defect_actions_complex` proves uniqueness
  on arbitrary complex Hilbert spaces with orthogonally projected subspaces,
  without finite dimension, optimality, or feasibility of the compared
  unitaries. Existence and minimum-cost conclusions remain finite-dimensional.
- `SmoothedCorrectionClassification.smoothed_correction_isMin_iff_phase_and_kernel_complex`
  classifies every closest prescribed-subspace-preserving unitary, with
  no commutator norm restriction. For `T=A V.adjoint`, it uses kernel
  self-adjointness and `C V=C F_P R.adjoint A`.

The complete theorem says
`C T.adjoint R=C F_P`, together with the crossed-defect exchange actions.
The operator identity cancels on `(ker C)^perp`: the adjoint difference
has image in `ker C`. The donor
`LinearIsometryEquiv.eq_on_orthogonal_ker_of_relative_left_mul_eq` proves
this cancellation without positivity, completeness, or finite dimension.
A separate unitary algebra argument shows that equality with a
cosine-commuting reference transporter forces cosine commutation.

The included manuscript now contains
`thm:smoothed-all-projections-defects` and the all-angle commuting-correction
criterion. The **set of all finite complex Charbonnier minimizers and
independent attainment of every phase/defect parameter pair are closed**.
Inactive phase projections remain redundant. No general normalized
parameter bijection, product `Homeomorph`, Grassmannian dimension formula,
or classification of local minima is asserted as a Lean endpoint.
The isoclinic metric theorem retains its established stronger hypothesis.
This advance supplies neither the pure Schatten all-optimizer theorem,
the unrestricted real matching formula, nor operator-ideal attainment.

The formerly open pure Schatten reflecting-descent calculation is now
formalized in the newer entry above. Its geometric extraction from every
actual gradient-kernel block remains the next unrestricted proof step.

Historical novelty remains provisional. A fresh targeted search for block
diagonal unitary trace-norm approximation and Charbonnier transport did not
identify a theorem subsuming this classification. BLR (2001), Lemma 3.3
and Theorem 4.2, remain exact precedents for the right-angle scalar Schatten
mechanism and complete Frobenius optimizer families respectively. Standard
spectral projection, unitary cancellation, and defect geometry receive no
separate priority claim. Earlier sections below record their dated frontiers.

Validation: each Lean build was preceded by `lake exe cache get`. The
focused classification, arbitrary-parameter attainment and correction
targets passed. The manuscript was rebuilt with BibTeX and repeated
pdfLaTeX passes, without unresolved references/citations, multiply defined
labels or overfull boxes, in
`/tmp/dk-nonacute-classification-paper/dk-nonacute-classification.pdf`.
The final `lake build DavisKahan.All ForTauCeti` passed (10,337 jobs;
`/tmp/nonacute-final-build.log`), including the dimension-free uniqueness
generalization and all new modules through the ordinary aggregate imports.

## Mixed right-angle family after `c16d48091`

The arbitrary mixed-defect converse is now compiled. The optimization
statements are finite-dimensional complex, with `0<b<a` for weighted
nuclear cost or `tau>0` for the literal Charbonnier cost. Other principal
angles, multiplicities, critical directions, and fixed space are unrestricted.

- `SmoothedDefectReplacement.minimizing_weighted_transport_unique_defect_equiv_complex`
  and `smoothed_minimizer_unique_defect_equiv_complex` prove that **every**
  ambient global optimizer has exactly one actual unitary identification
  `D : halmosSourceDefect K L ≃ halmosTargetDefect K L`. Its action is `D`
  on the source crossed defect and `D.symm` on the target crossed defect.
- `exists_weighted_minimizer_prescribing_defects_complex` and
  `exists_smoothed_minimizer_prescribing_defects_complex` take **any** such
  `D` and **any given ambient optimizer**. They construct a global optimizer
  with the prescribed actions, agreeing with the given optimizer everywhere
  on `(ker C)^perp`. The comparison quantifier ranges over every ambient
  transporter. No supplied extension, diagonal model, or prescribed pairing
  relative to the canonical completion is assumed.
- `KernelCostSplitting.weighted_transport_split_cosine_kernel` constructs
  actual unitary restrictions and proves
  `nuclear(a*T-b*I) = nuclear(a*T_pos-b*I_pos) + a*dim(ker C)`.
  It is **real/complex**, assumes `0<=b<=a`, feasibility, commutation with
  the actual cosine, and self-adjointness on its kernel; optimality is not
  assumed. `weighted_transport_cost_eq_of_eq_on_cosine_kernel_orthogonal`
  proves equality of costs for any two such transports agreeing off the kernel.
- `SmoothedDefectReplacement.smoothed_transport_split_cosine_kernel_complex`
  gives the literal identity
  `Psi_tau(T) = Psi_tau(T_pos) + (eta-tau)*dim(ker C)`.
  Here `eta-tau=(sqrt(tau^2+4)-tau)/2`; the same feasibility, commutation,
  and kernel hypotheses suffice without optimality.
- `KernelTransportReplacement.exists_transport_replacing_cosine_kernel`
  constructs the ambient extension of any self-adjoint unitary on the actual
  kernel exchanging the source reflection sectors. It derives feasibility
  and global cosine commutation while preserving all complementary action.
  This geometric statement is real/complex and finite-dimensional.
- `SmoothedNonacutePhases.minimizing_weighted_transport_cosine_mul_relative_commutes_rotation_complex`
  proves the all-angle global identity `[C*(T*R),R]=0` for **every** attaining
  weighted transporter. The unweighted relative unitary need not commute
  with the chosen rotation on the right-angle part.

The underlying geometric necessity in
`CosineKernel.exists_unique_defect_equiv_of_selfAdjoint_on_cosine_kernel`
needs **neither finite dimension nor cosine commutation**. Feasibility and
self-adjointness on the cosine kernel alone give a unique crossed-defect
isometry and its inverse action. `CanonicalSymmetry.exists_selfAdjoint_transport_prescribing_defects`
extends any defect isometry to a global self-adjoint transporter preserving
`C` on an arbitrary real/complex Hilbert space. That extension's positive-angle
action is not claimed optimal. These statements do not supply ideal-class
feasibility, convergence, or attainment.

The generic donor `FiniteUnitaryRestriction.lean` derives actual unitary
restrictions and inverse actions from finite invariant subspaces, without
assuming the ambient space finite or complete. Its orthogonal-sum assembly
needs only an orthogonal projection and no finite-dimensional hypothesis.
`BlockSchatten.lean` now splits finite Schatten powers and nuclear costs on
actual reducing restrictions, consuming the accepted `IsReducing` API and
the existing orthogonal-block theorem. These are classical foundations.

The checked manuscript includes Proposition `prop:smoothed-arbitrary-defects`
and the weighted-relative commutation identity in spectral separation.
The **right-angle parameter necessity and arbitrary-parameter attainment**
are closed, also when positive angles are present. A single full ambient
phase-plus-defect iff and a typed product/topological classification still
need the positive-phase assembly described next.

### Exact next global phase lemma

For an attaining `T`, put `Z=T*R` and
`H=Im(C*Z)=C*Im Z`. The compiled cosine commutation and `[C*Z,R]=0`,
together with unitarity of `R`, make `H` commute with `R,J,C`.
The proposed intrinsic projection is `E=1_(0,infinity)(H)`; it vanishes
on `ker C`. In a joint eigenbasis of `C,Im Z`, the corresponding eigenvalues
are `c>=0,g`, so `H` acts by `c*g`. For `c>0`, its sign is the sign of `g`,
and the existing scalar reconstruction gives the optimal phases. At `c=0`,
cosine multiplication kills both sides. The exact next Lean target is
`C*Z = C*(U E+U* (I-E))` with `E` orthogonal, commuting with `R,J`, and
zero on the kernel. Most of the acute positive-imaginary proof can be reused.

The expected full criterion for a feasible `T` is: `T` commutes with `C`,
is self-adjoint on `ker C`, and admits such a compatible phase projection
modulo the kernel. For sufficiency compare with the compiled optimizer
from `E`; cancel `C` on its kernel's orthogonal complement to identify
positive restrictions, then apply the new cost-equality theorem. Combined
with the unique `D` theorem and its arbitrary replacement, this would close
the complete finite Charbonnier family. It is **not yet a compiled iff**.
The pure Schatten zero-gradient local descent, unrestricted real matching,
and ideal extensions retain their earlier exact obstructions.

Independent numerical diagnostics (NumPy, seed 61273, `tau=0.4`) used
angles `0,0.35,c_tau,1.3,1.3,pi/2,pi/2`, two extra fixed directions, and
six arbitrary complex two-dimensional defect unitaries. The maximum cost
error was below `2.7e-15`; a transport residual was below `4.7e-16` and
positive-action change was exactly zero. The relative-rotation commutator
norm was `1.4231456447910595`, while its cosine-weighted version was below
`9.7e-17`. These are diagnostics, not proof evidence. The exact two-dimensional
prototype is `R=[[0,-1],[1,0]]`, `W=[[0,1],[1,0]]`, with `Z=diag(1,-1)`:
the pure complementary criterion proves optimality, but `[Z,R]` is nonzero.

The BLR primary PDF was checked again at Lemma 3.3 (printed p. 36) and
Theorem 4.2 (pp. 39--40). The lemma already gives the right-angle scalar
Schatten minimum and all attaining scalar pairs; Theorem 4.2 classifies
Frobenius minimizers. Do not claim a new rank-one reflection mechanism.
The present advance is the compiled arbitrary-rank mixed Charbonnier
identification and independent extension. Historical priority remains
provisional; the right-angle geometry and orthogonal-cost algebra are
classical. Earlier entries below are dated proof-frontier records.

Validation for the mixed-defect update: `lake exe cache get` preceded
all focused builds. The final `lake build DavisKahan.All ForTauCeti`
passed (10,333 jobs; `/tmp/mixed-defect-full-build.log`), including the
literal splitting identity and every new module through the aggregate.
The manuscript was rebuilt with BibTeX and repeated pdfLaTeX passes,
with no unresolved references/citations, multiply defined labels, or
overfull boxes (`/tmp/dk-mixed-defect-paper/dk-mixed-defect.pdf`). The
source, declarations, and claim mapping are durable; these build logs
are local reproduction evidence.

## Complete acute classification and isoclinic metric after `9693e8946`

All optimization endpoints below concern finite-dimensional complex Hilbert
spaces and equal-rank subspaces. The weighted statements assume `0<b<a`;
literal Charbonnier statements assume `tau>0`. Write `C` for the actual
principal cosine, `R` for canonical rotation, `J` for source reflection,
`Z=T*R`, and `U=weightedPhaseFactor a b C`.

- `SmoothedAcuteClassification.minimizing_weighted_transport_positive_phase_projection_complex`
  proves that **every attaining ambient transporter** with injective `C`
  has `Z=U P+U* (I-P)`. Its explicit witness is the positive real spectral
  projection of `Im Z`. This projection is orthogonal and commutes with
  both `R` and `J`. The proof uses a real joint eigenbasis of `C,Im Z`,
  the established scalar real-part identity, and unitarity; no generic
  eigenvalue or multiplicity assumptions are imposed.
- `minimizing_weighted_transport_iff_projection_of_injective_cosine_complex`
  proves both directions of that criterion. The literal all-ambient
  endpoints are
  `smoothed_transport_isMin_iff_projection_of_injective_cosine_complex`
  and `smoothed_transport_isMin_iff_projection_of_isUniformlyAcute_complex`.
  The latter has the actual hypothesis `IsUniformlyAcute K L`, meaning
  projection gap strictly below one. Zero, critical, subcritical, repeated,
  and supercritical acute angles and arbitrary fixed ambient directions
  are included. Projection parameters on inactive directions are redundant;
  no uniqueness of the unnormalized ambient parameter is asserted.
- `SmoothedIsoclinicFamilies.exists_scaled_isometric_smoothed_isoclinic_family_complex`
  treats the stronger **whole ambient** hypothesis `C=c I`, `0<c<1`,
  `eta*c<eta^(-1)`. With `beta=eta*c/eta^(-1)` and
  `s=sqrt(1-beta^2)>0`, it gives an injective assignment from all compatible
  ambient projections to optimizers, surjectivity onto **every** feasible
  global minimizer, the affine relative formula
  `Z=(beta-i*s)I+2i*s P`, and the exact identity
  `||T(P)-T(Q)||=2*s*||P-Q||`. Thus the correspondence and inverse are
  Lipschitz. The formal deliverable is bijection and norm identity;
  a Lean `Homeomorph`, general mixed-angle parameter topology, and
  Grassmannian manifold dimensions have not been registered.
- `SmoothedCorrectionClassification.smoothed_correction_isMin_iff_projection_of_commutator_lt_one_complex`
  classifies **all** closest subspace-preserving unitary corrections to
  `A`, under `||A P_K-P_K A||<1`. They are exactly
  `(U E+U* (I-E)) R* A` for orthogonal `E` commuting with `R,J` of the
  pair `(K,A K)`. Comparison is against all preserving unitaries,
  equivalently all unitaries commuting with the prescribed projection.
  The hypothesis permits supercritical angles and nonunique minimizers.
  The existing cost-preserving correction/transport lemma in
  `SmoothedCommutatorCutoff.lean` is now public and reused.

These results are included as Theorem `thm:smoothed-acute-projections`,
Corollary `cor:smoothed-isoclinic-metric`, and the all-correction formula
following `cor:smoothed-commuting-correction`. They do not extend the
Schatten all-minimizer theorem or the real matching formula by analogy.

The generic bridge in `Geometry/Angle/AcuteCosine.lean` proves that a
uniformly acute pair has invertible, hence injective, principal cosine
on any real/complex Hilbert space; it makes **no** infinite-dimensional
optimization or ideal claim. The joint real eigenbasis refinement and
`LinearIsometryEquiv.eq_of_relative_eq`, `norm_sub_relative`, and
`norm_sub_eq_of_relative_affine` are classical reusable ingredients.
The last three need neither completeness nor finite dimension.

The next mixed-defect reduction is also compiled in
`Geometry/Angle/CosineKernel.lean`: the actual `ker C` equals the crossed
source/target defect sum, the two reflections are opposite there, and
every cosine-preserving actual transporter anticommutes with source
reflection on that kernel. These statements are valid on arbitrary
real/complex Hilbert spaces, with no selected defect pairing.
`SmoothedRightDefect.smoothed_minimizer_right_defect_reflecting_complex`
combines this with optimizer self-adjointness for every finite complex
Charbonnier global minimizer. This is a necessary mixed right-block
structure; arbitrary-isometry converse assembly and cost additivity
remain to prove.

Independent diagnostics used NumPy, seed 73124, `tau=0.25`. On three
identical angles `1.35`, projection ranks 0 through 3 gave cost error
below `1.8e-15`, transport residual below `2.2e-15`, and norm-identity
error below `1.4e-15`, with scale `2s=1.9193988999508451`. A mixed list
containing zero, a subcritical angle, the critical angle, a repeated
supercritical angle, and another acute angle gave zero rounded cost
error and transport residual below `1.3e-15`. These are diagnostics,
not proof evidence.

### Remaining strongest obligations

The acute Charbonnier ambient iff is closed. For mixed right-angle
pairs, necessity (cosine preservation and self-adjointness on `ker C`)
and the pure complementary iff theorem are proved. The remaining converse
must restrict to the positive-cosine part, extend an arbitrary unitary
identification of the two actual crossed defect spaces paired with its
adjoint, and prove nuclear cost additivity. The acute projection formula
must not be imposed on the defect family: it gives only a subfamily there.
General products of multiplicity Grassmannians and arbitrary defect
unitaries still need typed restriction/assembly and topology statements.

A concrete next mixed-defect lemma is the cost splitting identity
`nuclear(a*T-b*I) = nuclear(a*T_pos-b*I_pos) + a*dim(ker C)`
for a feasible cosine-preserving transporter self-adjoint on `ker C`,
where `T_pos` is its restriction to `(ker C)^perp`. The second term follows
from the compiled anticommutation and self-adjoint weighted trace formula;
the remaining work is the actual reducing restrictions and nuclear
orthogonal-sum additivity. The positive restriction's principal cosine
must then be identified with the restricted ambient cosine before using
the acute classification. This avoids assuming the desired block formula
as a hypothesis.

For pure Schatten `1<p<2`, the missing local-to-global lemma is local
optimality of the zero-gradient reflecting restriction. The draft's
candidate descent uses `W exp(i t H)` on a two-projection block, with
`H=diag(cos(gamma)^2,-sin(gamma)^2)`. Away from `gamma=pi/4`, the
large phase decreases at order `t^2`, while the phase born at zero
has cost `O(|t|^(2p))=o(t^2)`. Its coefficient checks algebraically,
but the needed perturbation/remainder proof is not in Lean. Do not apply
a twice-differentiable objective theorem at a zero displacement singular
value. Unrestricted real four-dimensional determinant classes, the real
matching lower bound, and ideal feasibility/convergence/attainment remain
separate unproved endpoints.

The research novelty review adds the exact comparison with Contino,
Giribet, and Maestripieri, *Weighted Procrustes problems* (2017), Theorems
3.5 and 4.5. Their optimization variable ranges over all bounded operators;
these results do not directly classify our constrained unitary fiber.
No historical-priority clearance follows from this distinction.

Validation for this update: `lake exe cache get` followed by the focused
classification, isoclinic, correction, and right-kernel targets passed.
The final `lake build DavisKahan.All ForTauCeti` passed (10,321 jobs;
`/tmp/smoothed-classification-final-build.log`). The updated manuscript
was typeset with BibTeX and repeated pdfLaTeX passes, with no undefined
references/citations, multiply defined labels, or overfull boxes
(`/tmp/dk-acute-classification-paper/dk-acute-classification.pdf`). These
temporary logs are local build records; a fresh clone contains the Lean
sources and exact declaration mapping needed to reproduce the checks.

## Arbitrary multiplicity projections after `2524482e5`

The acute projection converse now has compiled ambient endpoints. All spaces
in the optimization statements are finite-dimensional complex Hilbert spaces;
weights satisfy `0<b<a`, or `tau>0` for the literal Charbonnier objective.

- `SmoothedProjectionOptimizers.exists_weighted_transport_from_projection_complex`
  takes **any ambient orthogonal projection** `P` commuting with the actual
  completed canonical rotation `R` and source reflection `J`. With
  `U=weightedPhaseFactor a b C`, it constructs a transporter `T` with
  `T*R=U P+U* (I-P)`, exact optimal value, and a lower bound against **every**
  ambient transporter. `exists_smoothed_transport_from_projection_complex`
  states the literal Charbonnier result. No diagonal frame is supplied, and
  repeated, subcritical, critical, fixed, and right angles are allowed.
  The right-angle choices covered by this formula are a subfamily of the
  arbitrary-unitary defect family.
- `SmoothedMultiplicityAttainment.exists_weighted_transport_with_multiplicity_projection_complex`
  takes an **arbitrary orthogonal projection** `Q` on the actual space
  `N=ker(R-mu I)`, with `|mu|=1`, `Re(mu)>0`, and `a*Re(mu)<b`. It constructs
  its reflected ambient extension and an ambient global optimizer whose
  relative phase on `N` is `(beta-i*s)I+2i*s Q`, and whose phase on `J N`
  is the reflected copy. Here `beta=a*Re(mu)/b`, `s=sqrt(1-beta^2)>0`.
  Other principal angles are unrestricted. No projection-extension or
  invariant-block hypothesis is supplied. The literal endpoint is
  `exists_smoothed_transport_with_multiplicity_projection_complex`.
- `exists_injective_smoothed_multiplicity_family_complex` strengthens this
  to an injective assignment from **all** orthogonal projections on `N` to
  global Charbonnier minimizers. It proves the pairwise bound
  `2*s*||Q-Q'||_op <= ||T(Q)-T(Q')||_op`. The generic
  `Submodule.relative_phase_projection_separation` proves the same estimate
  whenever two relative unitaries have common affine phase coefficients,
  even without optimality, finite dimension, or completeness. Thus it also
  compares parameters of arbitrary actual optimizers from the earlier
  necessary classification. No forward continuity, homeomorphism, dimension,
  or sharpness of the separation coefficient has been registered in Lean.

Proposition `prop:smoothed-projection-attainment` includes these consequences.
The parameter-recovery bound has inverse coefficient `1/(2*s)` at a fixed
supercritical angle. A claim about uniform conditioning through the transition
would require more: `s` vanishes at the threshold.

The proof reuses the accepted joint symmetric-eigenspace decomposition:
`PairedSpectralDecomposition.exists_paired_spectral_joint_eigenbasis` and
`PairedRotationEigenbasis.exists_paired_rotation_joint_eigenbasis` diagonalize
an additional symmetric commuting map on the paired nonzero spaces. The old
paired basis APIs now consume these stronger results. The source pair gives
`exists_subspace_paired_rotation_projection_basis_complex`, and the signed
attainment proof now works in any such frame via
`exists_signed_weighted_transport_in_frame_complex`. The new donor
`exists_unique_paired_projection_extension` now extends a
projection by projecting onto its range plus its reflected range, with
uniqueness under support on the paired sum. It only requires this prescribed
subspace to be finite dimensional; the ambient Hilbert space may be infinite.
These are
classical foundations, with no separate historical originality claim.

### Exact remaining classification and next proof

Necessary matching projections and the arbitrary **one-factor** converse are
compiled. The global compatible-projection construction also proves sufficiency
for all acute choices once assembled as one ambient projection. The missing
acute iff theorem is **necessity of that single ambient projection** for every
optimizer. `SmoothedOptimizerNoMixing.minimizing_weighted_transport_relative_commutes_rotation_of_injective_cosine_complex`
now proves global relative commutation with `R` when the actual `C` is injective,
including fixed and repeated-angle directions. A direct next proof is to use
`Im(T*R)` as the extra symmetric map in the new paired joint basis, recover the
two scalar phase signs from its common eigenvectors, and assemble their zero/one
spectral projection. This should also identify the product of independent
acute multiplicity choices. The natural injective-cosine/acute-pair bridge
should be stated with the actual projection-gap hypothesis.

On `ker C`, every optimizer is already a self-adjoint unitary restriction.
The complementary-pair iff criterion is proved, but the **mixed ambient**
arbitrary-defect-isometry family still needs its restriction/extension and
cost-additivity proof. These obligations, followed by topology and dimensions,
remain before asserting the complete product of Grassmannians and unitary
families. The set-theoretic injection above is not a topological embedding
claim. One useful next metric step is to retain the explicit zero extension
outside `N+J N` and prove equality in the norm estimate for that particular
family; an existential choice alone does not establish forward continuity.

Validation: `lake exe cache get` followed by the focused multiplicity target
and `lake build DavisKahan.All ForTauCeti` passed
(`/tmp/smoothed-projection-full-build.log`, 10,309 jobs). The manuscript typesets
with BibTeX and resolved references in `/tmp/dk-multiplicity-attainment-paper/`;
local font expansion is disabled at the command line only. Existing paired-basis
and signed-family theorem types were preserved while their proofs now consume
the stronger APIs. No Challenge endpoint, dependency pin, source denominator,
or unrelated untracked file was changed.

A diagnostic with NumPy seed 1381, `tau=1/4`, multiplicity three, and two
random rank-one projections at 80 degrees gave parameter distance
`0.8835569300247879`. The proved separation lower bound was
`1.7226860721970945` and the explicit pure-block ambient distance was
`1.7226860721970951`. Both costs agreed with `5.193436267739524` within
`1e-15`. Equality for this explicit family is consistent with the candidate
sharpness calculation; this numerical observation is not its Lean proof.

The Schatten all-minimizer/local-to-global, real matching, and infinite-ideal
frontiers are unchanged. In particular the generic Hilbert-space separation
lemma does not establish Schatten-ideal feasibility, convergence, or attainment.
A targeted search for block-diagonal unitary/trace-norm and Charbonnier transport
minimizers supplied no theorem-level precedent that closes the present
classification. This is limited search evidence, not a priority clearance.

## Paired phases and complementary right-angle classification after `51f21951d`

The new finite complex results use the same actual transport constraint and
weighted nuclear cost, with `0<b<a`. They advance the classification of
**every** optimizer, rather than adding a selected block hypothesis.

- `SmoothedOptimizerPairedPhases.minimizing_weighted_transport_paired_phase_projection_complex`
  takes an arbitrary ambient attaining transporter `T`. For a unit-circle
  rotation eigenvalue `mu` with `0<Re(mu)<b/a`, it constructs the actual
  restrictions of `Z=T*R` to `N=ker(R-mu I)` and `M=ker(R-conj(mu) I)`.
  Source reflection restricts to `j:N≃M`. With `beta=a*Re(mu)/b` and
  `s=sqrt(1-beta^2)>0`, there is a **unique** orthogonal projection `E` on
  `N` such that the restrictions are `(beta-i*s)I+2i*s E` and
  `(beta-i*s)I+2i*s j E j*`. Thus the two multiplicity parameters agree.
  `smoothed_minimizer_paired_phase_projection_complex` supplies the literal
  Charbonnier endpoint for `tau>0` and every globally minimizing ambient
  transporter. Proposition `prop:smoothed-matching-phases` states this result.
- `SmoothedSignedOptimizers.exists_independent_signed_weighted_transport_minimizers_complex`
  derives one paired rotation frame from **arbitrary** equal-rank subspaces.
  For **every** independent Boolean choice of optimal phase signs it constructs
  an attaining ambient transporter and proves the lower bound against all
  ambient competitors. Repeated and right angles are allowed, and fixed
  directions are fixed. This proves an attaining signed family; a fixed frame
  does not exhaust the possible mixing within equal-angle multiplicities.
- `SmoothedRightDefect.minimizing_weighted_transport_orthogonalComplement_iff_selfAdjoint_complex`
  proves a complete criterion when the target is the orthogonal complement:
  a feasible ambient transporter attains the weighted minimum **iff** it is
  self-adjoint. `smoothed_transport_orthogonalComplement_isMin_iff_selfAdjoint_complex`
  expresses the literal Charbonnier criterion with a quantifier over all
  competitors. It includes dimension zero and arbitrary multiplicity, with
  equal complementary ranks as the feasibility hypothesis. The weighted value
  is `a*dim(E)`; the smoothed value is
  `dim(E)*(sqrt(tau^2+4)-tau)/2`. This is Corollary
  `cor:smoothed-complementary-right`. It does not yet assemble arbitrary right
  defect choices with other angles in a mixed ambient pair.

The donor lemmas express classical unitary geometry and trace algebra:
`AnticommutingInvolution` now pairs conjugate unitary eigenspaces under an
actual reversing involution, without finite dimension. `Projection/UnitaryTransport`
proves that relative transports commute with source reflection.
`UnitaryScalarRealPart.exists_restriction_unique_phase_projection_complex`
constructs a finite invariant restriction and its unique phase projection;
the earlier full-cosine restriction consumes it. `NuclearTrace` computes
weighted self-adjoint-unitary costs from their traces. No separate priority
claim is made for these ingredients.

### Previous remaining theorem and a direct route

The new projection-attainment update above closes the one-factor converse
and compatible ambient-projection construction described here. At this earlier
frontier, the necessity on each acute supercritical multiplicity space is now compiled.
The next classification theorem is the **arbitrary-projection converse**:
for any orthogonal projection on each positive rotation multiplicity space,
construct its reflected copy and an ambient attaining transporter. The signed
construction proves this in a diagonal frame. Its proof should be made
available for any admissible paired frame and applied to frames adapted to
the chosen projections, or replaced by direct positivity of the dual residual.
On an active angle this residual has diagonal part `a*sin(theta) I` and an
off-diagonal part of norm `b*sqrt(1-(a*cos(theta)/b)^2)`; the squared difference
is `a^2-b^2>0`. Both routes still need the global assembly, including fixed
and right summands. The complementary-right iff theorem handles the full
right-only ambient problem; lifting it to an arbitrary reducing `ker C` and
proving the product assembly remain. No Grassmannian topology or dimension
theorem is registered as Lean-certified.

Numerical diagnostics (NumPy, seed 342, `tau=1/4`, multiplicity three) checked
a random rank-two phase projection at 80 degrees and an arbitrary unitary
right-defect identification. Their Charbonnier costs were respectively
`5.193436267739522` and `5.296693311223912`, agreeing with the exact scalar
formulas within `2e-15`; unitary/transport residuals were below `3e-15`.
These are diagnostics, not proof evidence. The earlier opposite-source-phase
counterexample remains valid and explains the need for matching parameters.

Validation: after `lake exe cache get`, the focused signed-family and right-defect
modules compiled, followed by `lake build DavisKahan.All ForTauCeti`
(`/tmp/smoothed-paired-full-build.log`, 10,303 jobs). The journal typeset with
BibTeX and resolved references in `/tmp/dk-paired-classification-paper/`;
font expansion was disabled only at the command line for the local TeX
installation. No dependency, source-result denominator, Challenge endpoint,
or unrelated untracked file was changed.

The Schatten all-minimizer, reflecting-kernel local-to-global, unrestricted
real matching, and ideal-theoretic frontiers remain as recorded below. Fresh
primary-source search again identified BLR Theorem 4.2 (Frobenius minimizers),
not a theorem establishing this weighted classification. Historical priority
is provisional; verification of these new statements is independent of it.

## Smoothed spectral separation after `15ae65745` (24 October 2026)

New compiled statements concern **every** finite complex global optimizer,
including repeated, zero and right principal angles. For weights `0<b<a`,
let `R` be the completed canonical rotation, `Z=T*R`,
`C=sqrt(I-(P-Q)^2)`, and `B=min(I,(a/b)C)` by spectral calculus.

- `SmoothedCertificateAverage.lean` extracts `Z+S Z* S=2B` from the
  self-adjoint dual displacement and the already fixed subcritical/critical
  directions. `S` is a self-adjoint unitary grading of the canonical rotation.
  Its clipping-recovery lemma accounts for mixed subcritical and supercritical
  lists; the argument does not assume block invariance of the competitor.
- `SmoothedOptimizerNoMixing.minimizing_weighted_transport_twisted_average_complex`
  proves this equation for an actual ambient minimizing transporter, with
  `R=C+i S sqrt(I-C^2)`, and proves `Z` commutes with `C`. On every
  positive-cosine space it also commutes with `S`.
- `minimizing_weighted_transport_commutes_cosine_complex` proves that the
  original transporter `T` commutes with `C` as well. Distinct principal
  angles, the right defect space, and the common fixed space cannot mix.
- `minimizing_weighted_transport_relative_real_part_complex` proves, on
  `Cx=cx` with `c>0`, `(Z+Z*)x=2 min(1,a*c/b)x`.
  `minimizing_weighted_transport_relative_commutes_rotation_on_positive_cosine_complex`
  proves `Z R x=R Z x` there. Thus the two opposite rotation phases are
  preserved separately even within an equal-angle block.
- `minimizing_weighted_transport_selfAdjoint_on_right_defect_complex` proves
  `T x=T* x` for every `x` in `ker C`. Cosine commutation makes this a
  reducing self-adjoint unitary restriction.
- The literal Charbonnier endpoints, for `tau>0` and every ambient global
  minimizer, are `smoothed_minimizer_commutes_cosine_complex`,
  `smoothed_minimizer_relative_real_part_complex` (scalar `min(1,eta^2*c)`),
  and `smoothed_minimizer_selfAdjoint_on_right_defect_complex`.
  Proposition `prop:smoothed-optimizer-separation` states the consequences.
- `SmoothedOptimizerPhases.minimizing_weighted_transport_eigenspace_phase_projection_complex`
  constructs the restriction of the actual relative unitary to
  `N=ker(C-cI)`. If `0<c<b/a`, write `beta=a*c/b` and
  `s=sqrt(1-beta^2)>0`. There is a **unique** orthogonal projection `E` on
  `N` for which `Z|N=(beta-i*s)I+2i*s E`. This is a necessary spectral
  normal form of every optimizer, not a claim that every projection on
  the full cosine space is admissible or attaining.

The reusable `PositiveUnitaryAverage.rigidity_of_unitary_twisted_average_on_eigenvector`
works over either field on arbitrary Hilbert spaces: at every nonzero
average eigenvalue it gives the prescribed unitary real part and commutation
with the grading. It assumes neither finite dimension nor closed range.
`BasisDiagonal.lean` supplies generic positivity and adjoint eigenbasis lemmas;
these classical foundations carry no independent priority claim.

### Previous classification boundary and a failed shortcut

The paired-phase update above closes the matching-halves step below; the
arbitrary-projection and mixed-defect converses remain open. At this earlier
frontier, on an actual positive **rotation** phase space
`N_plus=ker(C-cI) ∩ ker(R-exp(i*acos(c))I)`, the new commutation theorem
makes `Z` invariant. Transfer the unique-projection description to this
multiplicity space. Source reflection identifies it with the opposite
rotation phase space; prove that the two restrictions have the same
projection parameter under that identification. Then construct an attaining
ambient transport for every choice of these multiplicity projections.
This is the remaining converse needed before asserting the product of
Grassmannian families. On `ker C`, identify the now-proved self-adjoint
restriction with `[[0,A],[A*,0]]` on the intrinsic crossed defects and prove
attainment for every unitary `A`. Topology and dimensions remain unregistered.

The real-part equation alone is **insufficient**, even with admissibility
and cosine commutation. On one supercritical acute plane put `c=cos(theta)`,
`beta=a*c/b<1`, `s=sqrt(1-beta^2)`, and
`Z=diag(beta+i*s,beta-i*s)` in the source-projection coordinates.
Then `T=R_theta Z*` is feasible and `Re Z=beta I`. Direct multiplication
gives `T+T*=2*c*beta I`, so its weighted nuclear cost is `2 sqrt(a^2+b^2-2*a^2*c^2)`, strictly exceeding `2*a*sin(theta)`:
the squared radicands differ by `b^2-a^2*c^2>0`. This conventional calculation
explains why an arbitrary projection on the full two-sided cosine space
cannot be used as a sufficient optimizer parametrization. It is not yet
registered as a Lean operator counterexample. A NumPy check at `tau=1/4`,
`theta=80 degrees` gives Charbonnier cost `2.3178813595` versus optimum
`1.7311454226`, with transport/unitarity residuals below `1.2e-16` and the
scalar cost formula agreeing within `4.5e-16`.

Validation: the focused `SmoothedOptimizerPhases` target and the aggregate
`lake build DavisKahan.All ForTauCeti` succeeded after `lake exe cache get`.
The journal manuscript also typesets with BibTeX and resolved references.
The stronger certificate theorem retains the cosine eigenvector equations
in its conclusion; its existing consumer was updated in the same change.
No Challenge or comparator endpoint references that theorem. The pre-existing
Challenge/name-drift failures recorded in the earlier update remain outside
this mathematical build claim.

The unrestricted real matching and infinite-ideal optimization frontiers
have not changed in this proof wave. The full complex Schatten classification
and the reflecting-kernel local-to-global descent also remain open as
specified in the earlier update.

A further primary-source comparison identified Tamara Bottazzi,
*Best approximation by diagonal operators in Schatten ideals*, LAA 620
(2021), 1--26, DOI `10.1016/j.laa.2021.02.025`. Its problem is additive
Hermitian approximation by a fixed diagonal linear subspace, with
Birkhoff--James/duality characterizations. This supports treating the norm
support machinery as classical. It is a different feasible set from the
unitary transport fiber; no theorem implying the present phase classification
has been established. Full formula retrieval was incomplete, so this is
not an exhaustive theorem-level priority clearance. Source:
<https://www.sciencedirect.com/science/article/pii/S0024379521000847>.

## Optimizer classification frontier after `84822b0ba` (24 October 2026)

The unrestricted finite complex value and cutoff remain the foundation. New
compiled results constrain **every** global optimizer, rather than just a
selected direct-sum witness:

- `SchattenGlobalLowerBound.lean: gradient_kernel_cost_defect_of_isLocalMinOn_transports_complex`
  proves that at any local constrained minimum the ambient excess over the
  exact principal-angle value equals the excess on the actual gradient
  kernel. Its nonzero gradient blocks already attain their scalar minima.
  The original global lower bound now consumes this stronger identity.
- `SchattenOptimizerKernel.lean: gradient_kernel_optimal_of_isMinOn_transports_complex`
  proves that any global optimizer restricts to an attaining self-adjoint
  unitary on that kernel, with every restricted principal angle zero or right.
- `apply_eq_self_on_gradient_kernel_of_isMinOn_acute_transports_complex`
  proves that for an acute pair **every** global optimizer fixes the whole
  gradient kernel. This includes all common ambient directions lying there;
  no assertion that the whole common fixed subspace has already been
  identified with that kernel is inferred.
- `isMinOn_of_isLocalMinOn_transports_of_no_neg_one_complex` proves that a
  constrained local minimum with no eigenvalue `-1` is global. Eigenvalue `1`
  and zero displacement singular values are allowed. The more general
  `isMinOn_of_isLocalMinOn_transports_of_gradient_kernel_fixed_complex` gives
  the exact sufficient kernel condition. The full local-to-global statement,
  including nontrivial reflecting kernels, remains unproved in Lean.

These are finite complex `1<p<2` assertions with the original ambient
transport constraint. They are included as Propositions
`prop:schatten-optimal-kernel` and `prop:schatten-local-global-no-minus-one`.
The standalone reflection equality lemma in `SchattenReflectionBound.lean`
only needs a finite exponent greater than one and attainment of the scalar
value. Its sine comparison is strict at every interior angle. It cannot be
applied to an arbitrary **real** global minimizer: a real reflection may
minimize the real problem while costing more than the complex scalar value.

The reusable algebra for the smoothed optimizer families also advances:

- `ForTauCeti/.../PositiveUnitaryAverage.lean` proves that `U+V=2D`, `D>=0`,
  forces both unitaries to commute with `D`, gives `V=U*` on its range and
  `V=-U` on its kernel. If `D` is injective, `V=U*` on the whole space.
  These theorems allow arbitrary real/complex Hilbert spaces, with no
  finite-dimensional or closed-range assumption.
- `UnitaryScalarRealPart.lean` characterizes all finite complex unitaries with
  `X+X*=2cI`, `c^2+s^2=1`, as `X=cI+i s H` with self-adjoint unitary `H`.
  Equivalently `X=(c-i s)I+2i s E` with an orthogonal projection `E`, unique
  when `s!=0`. It also proves the paired equation
  `X+Y*=2cI`, `c>0`, is equivalent to this form with `Y=X`. At `c=0`, the
  exact condition is `Y=-X*`, leaving an arbitrary unitary choice.
  These classify **prescribed unitary-average blocks**. The newer spectral-
  separation update above derives the average equation from every ambient
  optimizer; matching the multiplicity halves and proving the converse remain.

The equality extraction has now advanced beyond the prescribed-block algebra:

- `NuclearTrace.re_trace_eq_nuclear_iff_isPositive` and
  `re_trace_isometry_comp_eq_nuclear_iff_isPositive` prove the exact equality
  case of nuclear support over either field, including singular operators.
- `SmoothedNuclearCertificate.weightedNuclear_support_eq_re_trace_complex` exposes
  the exact trace identity that previously appeared only inside the lower-bound
  proof. The old lower-bound API is preserved and consumes this identity.
- `SmoothedOptimizerCertificate.weightedNuclear_eq_minimum_iff_certificate_complex`
  characterizes all attaining contractions with paired imaginary diagonal
  entries: vanishing diagonal defect and positive dual displacement are
  necessary and sufficient. `weightedDiagonalDefect_eq_zero_iff_fixed_complex`
  characterizes vanishing defect by pointwise fixation of positive-weight
  and fixed basis directions.
- `apply_eq_self_of_critical_certificate_complex` handles zero dual weights
  at the transition. Self-adjointness of the positive dual displacement
  forces real diagonal entry one there, hence pointwise fixation. This
  argument does not impose a uniform subcritical bound on other angles.
- `SmoothedOptimizerRigidity.exists_paired_certificate_for_weighted_transport_complex`
  derives the certificate basis from arbitrary equal-rank complex subspaces
  and gives necessary and sufficient equality conditions for every ambient
  weighted transporter, with weights `0<b<a`.
- `smoothed_minimizer_agrees_with_canonical_on_subcritical_planes_complex`
  applies to the literal Charbonnier cost for `tau>0` and every ambient
  globally minimizing transporter. It agrees with direct rotation on all
  principal planes **at or below** the cutoff, and fixes all canonical
  fixed directions, even if the remaining angles are supercritical.
  Proposition `prop:smoothed-optimizer-certificate` states these consequences.

The equality certificate now yields the positive-average equation and
spectral separation, as recorded in the newer update above. The full
Grassmannian/unitary parametrization still needs the compatibility and
converse statements described there. No ideal-theoretic norm, feasibility,
or attainment theorem follows from the infinite-dimensional algebra alone.

No first-publication claim is made for the classical unitary-average,
projection-parameter, kernel-invariance, or directed-gap lemmas. The
classification consequences are registered against the ongoing complex
optimizer target, not added to the 29 historical source results.

Validation for this extension: `lake exe cache get` followed by
`lake build DavisKahan.All ForTauCeti` succeeded. The journal manuscript
was typeset in a fresh output directory with BibTeX and resolved references;
the local TeX installation required disabling microtype font expansion at
the command line. No production TeX configuration was changed for that
environment workaround.

The final fixed-field API polish adds `_complex` to the three new operator
certificate declarations. The required broader compatibility check exposed
an existing failure in `Challenge/MathlibCandidate/CourantFischerWeyl/Leaderboard.lean:6`:
`TauCeti.abs_eigenvalues_sub_le_opNorm` no longer resolves. The declaration-name
drift utility also reported 25 existing migration/census/leaderboard findings,
none referencing the new transport declarations. These validation surfaces
are unchanged from the starting `84822b0ba` snapshot. They were left untouched;
do not describe the repository-wide compatibility gate as passing. The
mathematical `DavisKahan.All` / `ForTauCeti` build remains the separate evidence
for the new results.

### Independent checks and exact next proof obligations

The conventional all-acute classification is still under review, with its
kernel obstruction now discharged for global minimizers. The next step is to
identify the paired gradient planes with the canonical equal-angle summands,
retain their principal phase bounds, and apply scalar uniqueness to obtain
all signed phase choices. The general right-angle case still needs the
intrinsic statement that its free factor is `[[0,A],[A*,0]]`, with no coupling
to fixed or acute summands. Topology and dimension assertions about the final
minimizer set are not yet registered as Lean theorems.

For the full local-to-global theorem, the exact missing analytic statement
is feasible descent on a non-right reflecting two-dimensional block. An
independent calculation confirms the draft's coefficient and gives an
explicit route: with `kappa=cos(2 gamma)`,
`u(t)=arcsin(kappa*sin(t/2))`, the eigenvalues of the draft's feasible curve
are `exp(i(kappa*t/2-u(t)))` and
`-exp(i(kappa*t/2+u(t)))`. The first phase has derivative zero at the origin
and is in fact cubic to leading order. The large phase contributes
`-(p/2)*2^(p-2)*kappa^2*t^2`. Prove a second-order remainder bound for the
small phase and transfer this actual cost descent through the existing
orthogonal block extension. The case `kappa=0` is exactly the right-angle
block and must remain exceptional.

Real-field diagnostics, using NumPy/SciPy as exploration only:
4,800 random nuclear matching instances (lengths 1 through 8, seed
`20261024`) agreed with the two-sorted-sum evaluation. The largest sampled
gap was `0.2666109925`, below `2-sqrt(3)`. Six real 6D Schatten-`3/2`
instances, including zero, right, repeated critical, and unequal angles,
were optimized in all four stabilizer determinant components with two
starts each (seed `2718`); the best costs agreed with the matching formula
to at worst `4.5e-10`. This does not prove the matching formula, the sorted
reduction, or the field-gap bound. Their full real four-dimensional
all-competitor endpoint remains the first missing optimization theorem.

Primary-source comparison was refreshed against Bolotnikov--Li--Rodman
(2001), Theorem 4.2 (Frobenius minimizers) and Theorem 4.5 (Q-norms under
additional block hypotheses), and Massey--Rios--Stojanoff (2018), Theorems
3.5 and 3.12. The latter treat Hermitian conjugacy orbits and full
fixed-singular-value orbits, respectively; the transporter stabilizer fiber
here is different. No reduction of the new constrained statements to those
results has been established. This is a comparison of hypotheses, not proof
of historical novelty. The original 2001 paper is available at
<https://journals.uwyo.edu/index.php/ela/article/download/117/117/117> and
Local Lidskii at <https://arxiv.org/html/1806.11436>.

## Latest completed complex Schatten theorem (24 October 2026, `521572a2`)

**Completed, not proposed:** The Lean development now proves, for *every*
finite-dimensional complex inner-product space and equal-dimensional pair
`U,V`, and for every exponent `1<p<2`, the attained **global** minimum

```
min_{W unitary, W(U)=V} ||I-W||_p^p
    = sum_{j=1}^k m_p(theta_j),
m_p(theta) = min_{0 <= delta <= theta}
    (2 sin((theta+delta)/2))^p + (2 sin((theta-delta)/2))^p.
```

This includes zero, repeated and right principal angles and competitors
which mix principal planes arbitrarily. It is not merely an upper bound
obtained by a block-diagonal construction. The global lower bound and
attainment are compiled separately. The completed cutoff also states
that the canonical *nonacute* direct rotation minimizes the full
Schatten power **if and only if** every angle is at most
`acos((2-p)/p)`, with equality included. The scope is finite-dimensional
**complex**, not arbitrary real rank nor infinite-dimensional Schatten
ideals. This does not classify every minimizing ambient unitary.

**Primary Lean evidence (target `521572a2`):**

- `DavisKahan/FiniteDimensional/DirectRotation/SchattenGlobalLowerBound.lean`:
  `sum_phaseMinimum_le_schatten_transport_complex`, for every admissible
  unitary (the no-cross-plane-improvement direction).
- `DavisKahan/FiniteDimensional/DirectRotation/SchattenGlobalAttainment.lean`:
  `exists_unitary_attaining_schatten_principalAngles_complex` and
  `exists_unitary_minimizing_schatten_transport_principalAngles_complex`,
  constructing and certifying the unrestricted minimizer.
- `DavisKahan/FiniteDimensional/DirectRotation/SchattenCanonicalOptimality.lean`:
  `nonacuteDirectRotation_schatten_minimal_iff_complex`, equivalence of
  canonical optimality and the angle cutoff for every admissible transporter.

**Checked manuscript:** `paper.tex` now includes
`schatten_transport_verified.tex` between sharp displacement and smoothed
transport. That source includes the scalar classification, complete
unrestricted lower-bound argument, actual Lean signature, cutoff and a
rank-two numerical example. The Manim `novelty-tour` teaches the difference
between scalar phase minimization and full ambient no-mixing optimality.

**Novelty boundary:** The problem of constrained ambient unitary transport
and failure of Schatten minimality for `1<=p<2` are established prior art
(Bolotnikov--Li--Rodman 2001; Davis--Kahan 1970 Example 4.2). The global
principal-angle formula and exact all-rank cutoff are now complete, credible
candidates for original mathematical results. First-publication priority
is **not established** merely by completion of a Lean proof or an unsuccessful
literature search. Compare possible matrix-nearness, unitary completion,
Procrustes and quotient-distance theorems at equivalent hypotheses.

**Not yet completed at full generality:** classification of *all* optimal
Schatten transports; infinite-dimensional Schatten ideals; general real
arbitrary-rank matching; sorted-pair reduction; sharp real/complex field
gaps. Retain them in unverified research notes rather than the checked paper.
The YWS paper stub and the original 29-source-result inventory are unchanged.

### Research/applications boundary

The exact finite-dimensional formula is directly useful as a global lower
certificate for any numerically produced feasible complex unitary, and the
principal-plane construction attains that bound. The cutoff identifies when
canonical rotation itself is optimal. This does not yet provide a complexity
bound for computing the angles, a noisy-data estimation theorem, a physical
quantum-gate synthesis procedure, or a higher-rank real algorithm.

## Current article and visualization update (24 October 2026, `642de34d`)

The mathematical claims already included in `smoothed_transport_verified.tex`
were **not awaiting Lean proof** in this snapshot: the exact complex minimum,
explicit optimizer, necessity-and-sufficiency of the canonical/global
uniqueness cutoff, strict quadratic growth, mixed-angle quartic growth,
critical planar flatness, sharp angle-value sensitivity, and nearest commuting
unitary with the exact operator-norm commutator criterion all have corresponding
formalized endpoints. The 29 reviewed Davis--Kahan source targets are unchanged.

The manuscript now gives the commuting application a self-contained numerical
illustration, anchored in the verified formulas: `tau=1`, source projection
`diag(1,0)`, and unitary planar rotations at `45` and `80` degrees. It explicitly
distinguishes the mathematically certified unitary correction from speculative
physical constraints. The new title reflects both the source formalization and
mathematical transport extension; it does not claim proof of mathematical
first-publication priority.

The original novelty review is retained with a new **afternoon reassessment**
at its top (`MATHEMATICAL_NOVELTY_REVIEW_2026-10-24.md`) rather than deleting
older research history. The `novelty-tour` Manim deck adds focused teaching
scenes on critical quartic growth, the exact commutator test, and the same
2x2 numerical example. Reusable palette and color definitions are unchanged.

Remaining priority questions at the earlier `642de34d` snapshot: Do general weighted unitary Procrustes/nuclear
matrix-nearness theorems imply this combined exact minimum and cutoff? Are the
critical order-four growth and full uniqueness boundary already expressed
for this precise transporter feasible set? No negative web search constitutes
proof of novelty. At that earlier snapshot, real arbitrary-rank matching and global higher-rank
complex Schatten optimization were both open. The latter was completed at
`521572a2` and is now in the checked manuscript; all supercritical minimizer
classification and real field-gap conjectures remain outside it.

## Publication scope: mathematical extension ships with the DK paper

The author explicitly directed on 24 October 2026 that the new mathematical
insight must ship with this journal article. This overrides the separate-paper
recommendation in `MATHEMATICAL_NOVELTY_REVIEW_2026-10-24.md` while retaining
that review's proof-status and priority distinctions. `paper.tex` now includes
`smoothed_transport_verified.tex`: the fully Lean-certified unrestricted
complex smoothed minimum, explicit optimizers, exact canonical and global
uniqueness cutoffs, exact commuting correction, strict-subcritical quadratic
growth, and quartic growth through the cutoff. The critical quartic
coefficient, failure of quadratic growth, sharp angle sensitivity, and exact
commutator test for a unique closest correction are also compiled and included.
These results are motivated by the formal refutation of Proposition 4.4 and
form the article's mathematical extension.
This `642de34d` record preceded the all-rank complex Schatten theorem.
The broader all-minimizers, real matching/gap, and infinite-dimensional
Schatten drafts remain excluded. Mathematical priority for the exact smoothed theorem and
its stability estimate is plausible but provisional; negative searches are
not proof of first publication. The original 29-result denominator is unchanged.

## What the article can claim now

| Claim for the journal article | Evidence in this repository | Boundary / wording |
| --- | --- | --- |
| The 1970 Davis--Kahan paper has **29 reviewed result-level targets**; 28 are proved and Proposition 4.4 is refuted as printed. | `dev/davis-kahan-1970-formalization-result-inventory.json`; `dev/davis-kahan-1970-full-source-census.json`; `appendix_process.tex` | This is a result-level *source accounting*, not a count of Lean declarations, nor 29 theorems proved. Review of semantic correspondence is distinct from Lean compilation. |
| The sine-theta formalization retains the **real and complex, infinite-dimensional, unbounded self-adjoint**, finite-interval/exterior and ordered half-infinite gap alternatives, with the source's ideal-norm hypotheses. | `DavisKahan/Sources/DavisKahan1970/SineTheta/Presentation.lean`: `sinTheta_unbounded_formGap_whereDefinedUIN_rclike`; `paper.tex` § `sec:sine-theta`; `claims_to_evidence.md` | State norm membership and operator-domain hypotheses; do not claim every possible norm/operator configuration is covered. |
| The positive trial-coordinate sine operator equals the modulus of the rectangular Sylvester block. | `Presentation.lean`: `sourceDirectedSinThetaOperator_eq_modulus`, and its derivation in `paper.tex`. | Equality of the *positive modulus* and the sine operator; the rectangular block itself has a different source/target. |
| Printed Proposition 4.4 is false under its **real** hypothesis `alpha <= pi/3`. No smaller positive maximum-angle cutoff repairs it. | `DavisKahan/FiniteDimensional/DirectRotation/SmallAngleCounterexample.lean`; `DavisKahan/Sources/DavisKahan1970/Section4SmallAngle.lean`; `counterexample.tex`. | The phase trick occurs in the original Davis--Kahan Example 4.2 over the complex field; claim the verified identification of the real counterexample and its source-level failure, not first discovery of the phase mechanism. |
| For every finite-dimensional real or complex pair and unitary/orthogonal transporter `W`, `N(P_U-P_V) <= N(I-W)` for **any unitarily invariant seminorm**, without acuteness. | `ProjectionDisplacement.lean`: `projectionDifference_uiNorm_le_displacement`. | Known mathematical neighborhoods include projection pinching, principal-angle theory, Kato/Sz.-Nagy; do not claim priority from an unsuccessful exact-formula search. |
| For acute pairs, `N(I-R) <= sec(alpha/2) N(I-W)` for all such seminorms and transporters. At fixed `0 < alpha < pi/2` the factor is attained in the **real trace norm**, and the common `alpha <= pi/3` factor `2/sqrt(3)` is optimal across the class of norms. | `SharpDisplacement.lean`: `cos_half_maxPrincipalAngle_mul_uiNorm_directRotation_le_displacement`, `factor_necessary_at_fixedAngle`, `pi_div_three_common_factor_necessary`; `sharp_displacement_verified.tex`. | Uniform sharpness **across the class** does not imply that the factor is best for each individual norm. Frobenius/Q-norm minimality can be exact. The inequality is a short consequence of classical geometry; no first-publication claim. |
| The real 4D witness has global minimum `min_W ||I-W||_1 = 4 sin(theta)` and direct rotation cost `8 sin(theta/2)`. | `TraceOptimality.lean`: `SmallAngleCounterexample.exists_traceMinimizer`; `TraceRatio.lean`; `SmallAngleCounterexample.lean`. | Distinguish an attained **global minimum** from the earlier nonminimality witness. |
| Any two projections in a finite-dimensional real or complex Hilbert space have a trace norm equal to the sum of their two directed sine-map trace norms; the positive modulus splits even when the ranks differ. | `ForTauCeti/Analysis/InnerProductSpace/Projection/TraceSine.lean`: `operatorAbs_projectionDifference_eq_directed_sine_sum`, `kyFanSum_projectionDifference_eq_directed_sines`. | No equal-rank, acuteness, or complex-only assumption. This is a finite-dimensional trace statement; its full infinite-dimensional trace-class analogue is not claimed. |
| Every equal-rank pair of finite-dimensional **complex** subspaces admits a unitary transporter minimizing the full trace displacement globally: `min_W ‖I-W‖₁ = ‖P_U-P_V‖₁ = 2∑ sin θ_j`. | `DavisKahan/FiniteDimensional/DirectRotation/ComplexCrossedDefects.lean`, `ComplexPhaseTrace.lean`: `exists_global_complex_trace_minimizer`; `ComplexTracePrincipalAngles.lean`: `exists_global_complex_trace_minimizer_with_principalAngles`. | No acute-angle or supplied-coordinate assumption, including zero and right angles. Applies to the full trace norm (Ky Fan sum at ambient dimension), not a claim of optimality for every unitarily invariant norm. Earlier finite-model theorems remain valid special cases. |

**Verification basis.** The user reported successful Lean builds for the source-level results, the small-angle family, the projection-distance bound, fixed-angle sharpness, real global optimality, and complex finite-model theorems on 23 October 2026. The subsequently updated source revision `b00c5c8` adds the unconditional complex and directed-sine trace theorems, imported by `DirectRotation/All.lean`; see `submission/VALIDATION.md` and `claims_to_evidence.md`. The added Schatten research modules and direct-rotation aggregate were built on 24 October as recorded below. Manuscript PDF builds verify typesetting only.

## Mathematical claims still outside this formalization

- **Real line/hyperplane minimum for arbitrary UI norms:** conventional proof in
  `REAL_TRANSPORT_MINIMIZATION_NOTES.md` and the red-framed working draft; no
  general compiled Lean counterpart is claimed. This includes the consequent
  minimal real ambient dimension of four for the short-angle failure.
- **General real trace equality cases:** the even-multiplicity sufficient
  condition for real angle patterns remains a conventional deduction, not a
  formalized characterization; necessity fails at right angles.
- **Complex equality-case classification:** an attaining transporter and the
  exact minimum are fully formalized. **All** minimizing unitary transporters
  have not been classified. No general Schatten-`p` optimality statement is
  inferred from *trace optimality alone*; the separate all-rank complex
  `1<p<2` optimum is now proved at `521572a2` (see the latest section).
- **Infinite-dimensional trace-ideal extension:** the new projector trace
  identity and complex minimum are finite-dimensional; ideal-membership and
  trace-class hypotheses need a separate analysis in infinite dimensions.
- **Optimal universal acute-pair `sqrt(2)` constant:** the upper bound and
  fixed-angle necessity were compiled earlier; `SharpDisplacementLimit.lean`
  is a separate focused endpoint. Check its specific source/verification record
  before promoting its declaration to a new central result.

## Prior art and originality boundaries

- A **mathematical formula's verification in Lean** is a formalization contribution even if its conventional proof is a short consequence of standard matrix geometry.
- The `sec(alpha/2)` bound is strongest as a **quantitative replacement with a formalized fixed-angle equality case**. Avoid first-discovery and new-optimization-mechanism language pending further historical comparison.
- The real 4D counterexample isolates a **contradiction of a specifically printed real short-angle theorem**. It is a realification of an old complex phase mechanism; these statements must appear together.
- The exact complex all-pairs trace minimum is a **new completed formalization claim** in this snapshot. Davis--Kahan's complex phase mechanism and the corresponding unitary-completion optimization problem are prior art; the absence of an exact published formula in the inspected sources does not establish mathematical first-publication priority. The source-level 29-result denominator remains unchanged.
- `28 + 1` concerns original 1970 source targets. Sharpness, real global optimum, and complex finite-model assembly are **additional** mathematics, not extra source rows.

## Manuscript structure and constraints

### Schatten optimization research extension, 24 October 2026

The current research objective is mathematical novelty beyond formalization,
with an exact angle-dependent Schatten optimization theorem as the primary
candidate. This does not change the 29-result source denominator.

The strongest current conventional candidates are the exact real
Schatten/Charbonnier minimum as two sorted sums, its more general spectral
penalty reduction to weighted matching, and the sharp dimension-independent
additive gaps between real and complex nuclear/smoothed transport.
These full real optimization statements are not yet Lean-certified.
The unrestricted complex Charbonnier minimum, its explicit spectral optimizer,
and its strict-subcritical stability estimate are fully compiled; real
stationarity and positive submaximal spectral blocks are compiled separately.
Priority of the optimization contributions remains provisional.

`SchattenPhaseTransition.lean`, committed at `4173073c9`, now proves global
scalar-phase optimization on `[0, theta]` for `1 < p < 2`: the canonical phase
is uniquely minimizing exactly when `p cos(theta) >= 2-p`, including equality;
above that threshold there is a unique interior minimizer, characterized by the
stationary-amplitude equation. The entire direct-rotation aggregate compiled
after the module was added to its imports. The new public declarations depend
only on `propext`, `Classical.choice`, and `Quot.sound`.

`SchattenPhaseMinimum.lean` defines the attained scalar value and proves its
nonnegativity, right-angle value, and sharp comparison with the canonical
power sum. `SchattenPhaseTransport.lean` realizes it by an admissible bundled
complex unitary and identifies its actual Schatten norm using the accepted
Tau Ceti API. The attaining-family theorem covers every finite exponent at
least one and every angle in `[0, pi/2]`. Both modules and their aggregate
compiled on 24 October. Their minimum statements still concern the scalar
family; no unrestricted lower bound is inferred from attainment alone.

`SchattenPhaseCriticalAngle.lean` now proves the explicit inverse-cosine
cutoff, strict increase and decrease of the amplitude on its two branches,
and existence and uniqueness of both roots below its maximum.
`SchattenThreeHalves.lean` proves the explicit supercritical optimizer
`arccos(cos(theta)/(1-2 cos(theta)))` and the closed value identity
`m_(3/2)(theta)^2 = 8 (1+cos(theta)) sqrt(1-2 cos(theta))`.
The right-angle minimizing phase is also proved unique for `1 <= p < 2`.
The expanded direct-rotation aggregate compiled, and the new public endpoint,
critical-angle, two-root, and three-halves declarations have only the three
standard axioms listed above.

`SchattenPlanarOptimization.lean` proves that the attained scalar cost is the
unrestricted minimum over all complex planar unitaries transporting the model
source line to its target, for every finite exponent at least one. Its generic
lower bound applies on any two-dimensional complex inner-product space with
a unit-vector angle witness. The proof consumes Tau Ceti's accepted normal
spectral theorem and planar singular-value API: the absolute eigenphases have
total budget at least `2 theta`, and scaling them down reduces to the scalar
minimum. The canonical model transport is globally optimal exactly below the
explicit critical angle, including equality. This closes the unrestricted
two-dimensional reduction; independence across several principal planes is
still the separate, unformalized higher-rank step.

The balanced-root geometry is now proved in `SchattenPhaseCriticalAngle.lean`:
the roots have sum below `pi`, their mean is an acute supercritical angle,
and their chord powers give its exact minimum. Conversely every acute
supercritical angle arises this way. `SchattenPhaseSupportingLine.lean`
proves the strict affine upper support for the angle minimum and the strict
cost decrease when a balanced block is split into distinct physical angles
of no greater total angle. It also proves that `m_p` is strictly convex below
the transition and strictly concave from the transition to the right angle.
These are scalar value-function theorems, not a certificate that an arbitrary
matrix competitor has already been reduced to such blocks.

`schatten_optimization.tex` is a mathematical extension draft that is **not
included by `paper.tex`**. It gives a conventional proof candidate for the
unrestricted finite-dimensional complex formula
`min_W ||I-W||_p^p = sum_j m_p(theta_j)`, where `m_p` is the scalar minimum.
The proposed reduction uses first variation, a decomposition by the squared
spectral gradient, and an explicit negative second variation that excludes
overlapping large-phase spaces. A zero-gradient block is treated by a rank
bound. Its consequences include the sharp exponent-dependent canonical-angle
cutoff, the uniform comparison constant `2^(1/p-1/2)`, and a square-root onset
of the minimizing phase. **These unrestricted, second-variation, and asymptotic
claims are undergoing proof review and have not been certified in Lean.**

The draft also gives conventional proofs that every local minimum of the
finite complex transport problem is global, and that the same exact value
formula holds for `P-Q` in the Schatten ideal on a separable complex Hilbert
space with balanced finite defect spaces. The proposed infinite-dimensional
optimizer differs by finite rank from a principal-plane direct rotation:
only angles above the positive critical angle need phase correction. These
two extensions are also **under review and not Lean-certified**. The local
minimum argument uses a separate reflection-block descent and controls the
vanishing displacement cost by `O(|t|^(2p))`; it does not assume the full
objective is twice differentiable at zero singular values.

`figures/schatten_phase_diagram.py` generates a vector PDF and SVG illustrating
the proved scalar cutoff and optimizer. The plot uses the increasing branch
of the logarithmic ratio for numerical roots and the explicit formula at
`p=3/2`; it is exposition, not proof evidence. The standalone proof-review
PDF is generated under `build/schatten-research/`, outside the main manuscript.

Primary-source comparisons verified in this research pass include
Bolotnikov--Li--Rodman (2001), Lemmas 3.2--3.3 and Theorems 3.1/4.2; these
cover the planar `p >= 2` case, the right-angle `p < 2` case, and related Q-norm
and Frobenius problems. The indexed searches have not located the complete
angle-dependent `1 < p < 2` classification or the proposed reduction for
arbitrary complex rank. That is a provisional novelty assessment, not a
first-publication proof. The underlying phase mechanism and trace
nonminimality are established prior art. Lewis (1996), Theorem 1.1, was checked
against the author's scanned paper, printed p.577, for the spectral
differentiability step; the projection decomposition is classical Halmos
theory. Do not attribute these standard ingredients to the present research.

Numerical checks of arbitrary two- and three-plane complex transports did not
improve on the independent scalar minima. Direct finite-difference checks of
the proposed mixed-block descent curve agree with its second derivative
`8 cos(gamma)^2 f_p''(b) < 0`. These are exploratory consistency checks; they
do not establish either the unrestricted theorem or historical priority.

A concrete application is exact unitary rounding into the commutant of an
orthogonal projection. For a unitary `U`, set `Q=UPU*`. The correspondence
`V=W*U` identifies unitaries `V` commuting with `P` with transporters `W` from
`P` to `Q`, preserving the displacement norm. Thus the proposed full angle
formula also solves the nearest block-diagonal unitary problem. Its endpoint
bound would give the sharp uniform estimate
`dist_p(U, {V unitary : VP=PV}) <= 2^(1-1/p) ||[P,U]||_p` for `1<p<2`.
This deduction is conventional and not yet Lean-certified.

The application is related to Chubb--Flammia, *Approximate symmetries of
Hamiltonians*, J. Math. Phys. 58, 082202 (2017), DOI 10.1063/1.4998921.
The final arXiv v3 was checked at
<https://arxiv.org/html/1608.02600>, Definition 2 and Lemma 2.3. Their ground
symmetry is required to be unitary on the ground space, while our rounding
problem requires a globally unitary operator. The older 2016 author PDF
<https://christopherchubb.com/Approximate_Symmetries/Paper.pdf>,
Definition 2 and Lemma 2.2 (printed pp. 2, 4--5), already constructs a
full ambient unitary commuting with the ground-space projector. Thus
neither global unitarity alone nor existence of a nearby commuting unitary
is novel. Its `6 epsilon/Delta` bound was replaced in v3; do not compare
our formula with that obsolete constant to claim an improvement of the
final theorem. The present candidate contribution is exact angle-dependent
Schatten optimization and sharp constants for the two-level problem,
not a claimed replacement of their ground-space result. The research
fragment now avoids an ambiguous contrast between the two versions.

A further local-minimum comparison was checked against the primary preprint
of Massey--Rios--Stojanoff, *Local Lidskii's theorems for unitarily invariant
norms*, Linear Algebra Appl. 557 (2018), 34--61,
DOI 10.1016/j.laa.2018.07.022, <https://arxiv.org/html/1806.11436>.
Their Theorems 3.5 and 3.12 prove that local minima are global for distance
to a full fixed-eigenvalue Hermitian orbit or a full fixed-singular-value
matrix orbit. Our domain is the coset of the stabilizer of a specified
projection. It is a restricted part of the unitary group, and the local
minimality hypothesis on that coset does not imply local minimality on the
larger orbit. These results are relevant antecedents for the landscape
claim, but the inspected statements do not supply our angle formula or
the local-to-global conclusion on the transporter coset. No priority claim
for the general principle that local minima can be global is warranted.

The donor cluster `SpectralTrace.lean`, `SchattenSpectralCalculus.lean`, and
`SchattenUnitaryVariation.lean` supplies a compiled first variation for the
actual accepted Schatten norm power along normal curves with spectra in a
common compact set. It uses scalar supports, the accepted Schur weights,
continuity of the continuous functional calculus, and the accepted normal
spectral theorem. Eigenvalue collisions and zero displacement are allowed
for every finite exponent greater than one. The planar consumer now uses
its general eigenbasis norm formula instead of a separate two-entry sorting
proof. These are classical foundations for the matrix reduction, not new
research claims. They have no newly accepted Tau Ceti roadmap target in this
campaign; no upstream submission scope or acceptance is inferred.
`SchattenStationarity.lean` now proves the constrained trace annihilation and
reflection-anticommutation identity at a local minimum, using feasible
exponential variations and trace-square faithfulness. The direct-rotation
aggregate builds these results. The spectral block classification, exclusion
of mixed large-phase spaces, and higher-rank minimum remain separate formal
obligations.

`SchattenGradientSpectrum.lean` connects the operator gradient symbol on
`exp(i t)` to `p * phaseAmplitude p t` for positive principal phases. It
proves that each positive submaximal gradient level has exactly two roots
in the full principal-phase range, and that unitary eigenvectors at that
gradient level have one of these two phases. The donor variation module also
proves that the zero symbol on the unit circle occurs precisely at `1,-1`,
and a unitary with identically zero phase gradient is self-adjoint. These
compiled results supply the scalar spectral ingredients. Their operator
restrictions and the current overlap-exclusion boundary are registered below.

`SchattenGradientPairing.lean` now constructs the isometric equivalence
between opposite gradient eigenspaces by restricting the source reflection.
The generic construction in `AnticommutingInvolution.lean` also proves
equality of their finite multiplicities. These classical symmetry facts
require no diagonalization of the original transport constraint. The
direct-rotation aggregate builds the new modules, and their axiom audit
uses only the standard `propext`, `Classical.choice`, and `Quot.sound`.
The exclusion of mixed large-phase spaces is not yet formalized.

The restrictions are now constructed in `SchattenGradientBlocks.lean`:
on opposite positive submaximal levels they have a common pair of opposite
phase roots and are affine in star projections. `TwoPointSpectrum.lean`
supplies the classical C-star-algebra projection representation without a
finite-dimensional hypothesis. The gradient square is also proved to
commute with both source and target projections. The maximal signed gradient levels have scalar critical-phase unitary
restrictions, now packaged as
`signed_critical_gradient_eigenspace_representation` in
`SchattenGradientBlocks.lean`.

The no-mixing argument has been simplified to the basis-independent
direction `X=AB+BA`. The projection-compression identities and the strict
sign of the trace coefficient compile in `ProjectionOverlap.lean` and
`SchattenOverlapDirection.lean`. The conventional draft now states the
two-phase second-variation lemma explicitly and derives it from the
classical spectral Hessian of Lewis--Sendov (2001, Theorem 3.3). Their
printed theorem is for real symmetric matrices; the draft explains the
Hermitian extension by realification. Formal identification with the
actual second derivative is now registered below for two-phase blocks.
Its ambient paired-block assembly and the resulting spectral-block overlap
exclusion are now compiled below. The full angle-sum minimum remains unfinished. No novelty is claimed for the spectral Hessian theorem.

`TwoPointDerivative.lean` supplies a more focused compiled route to the
needed Hessian. If a symbol takes the same value at two distinct spectral
points, two applications of the accepted `dslope` factor its difference
from that value into a quadratic polynomial and a continuous remainder.
The polynomial vanishes at the base operator, so only its derivative and
continuity of the remaining functional calculus are needed. The resulting
derivative is the sum of the two diagonal compressions, weighted by the
scalar complex derivatives. This is classical mathematics with no
finite-dimensional hypothesis. Its application to the actual phase symbol
is registered next; no ambient overlap-exclusion claim follows from this
generic API alone.

`SchattenPhaseSymbol.lean` now supplies the required complex extension,
its agreement with the actual phase gradient on the entire unit circle,
its continuity there for exponents greater than one, and its complex
differentiability away from the identity. The derivative bridge matches
its complex tangential derivative to the real phase curvature.
`SchattenTwoPhaseVariation.lean` then proves the gradient derivative and
the second variation of the actual accepted Schatten displacement power.
The latter is stated with explicit scalar derivative data and Frobenius
squares represented by their finite traces. Its proof uses the first
variation at every real time, so it differentiates the actual cost's
derivative. The axiom audit uses only the standard three logical axioms.
This supplies the analytic two-phase input for the ambient spectral-block
overlap exclusion registered below.
The downstream `balanced_phase_second_variation` in
`SchattenSecondVariation.lean` supplies the scalar derivative data from
the amplitude calculus for distinct positive balanced roots, giving the
explicit coefficients `p * amplitudeDerivative p a` and
`p * amplitudeDerivative p b` in the actual-norm second variation.
The corresponding negative-root formula is also compiled. The donor
symbol calculus proves the evenness of the phase-gradient derivative.

`SchattenNoMixing.lean` now proves the core overlap exclusion on the
paired block model. For the sum of the two actual Schatten displacement
powers under their common variation, `AB != 0` gives a strictly negative
second derivative, and every local minimum therefore has `AB = 0`.
The necessary second-derivative test is consumed from the accepted Tau
Ceti calculus API. This theorem concerns the explicit paired objective;
its ambient transfer and the coordinate construction are proved in the next
two modules. The new donor `BlockSchatten.lean` proves additivity of the actual
finite Schatten power for arbitrary real or complex orthogonal square blocks,
using the accepted polar decomposition. The paired objective is now identified
with the actual displacement power on the orthogonal product. The spectral
calculus also proves norm invariance under isometric changes of carrier types;
these are classical assembly ingredients, not separate novelty claims.

`SchattenFeasibleBlocks.lean` now proves the ambient extension step when
paired reflection coordinates are supplied. A common right exponential on
the paired blocks commutes with their swapping reflection. Extending it by
the identity on an arbitrary complementary block gives a continuous feasible
ambient curve. The actual ambient cost equals the paired cost plus the fixed
complementary cost, so local minimality transfers and forces `AB = 0`.
This theorem permits an isometric change of the ambient carrier. The next
module constructs the required coordinates from stationarity.

`SchattenGradientNoMixing.lean` closes the supplied-coordinate hypothesis.
At an arbitrary finite complex constrained local minimum, it identifies the
opposite submaximal nonzero gradient eigenspaces using the actual source
reflection, constructs their common orthogonal coordinates and fixed
complement, and proves that the two large-phase projections satisfy `AB = 0`.
The restrictions retain their actual action on ambient vectors and their
balanced phase representations. `PairedInvolutionDecomposition.lean` supplies
the reusable orthogonal coordinate construction, including both the swapping
reflection and the restricted complementary unitary. The strengthened gradient
block theorem also retains the scalar balance equation in its conclusion.
The axiom audit lists only the three standard logical axioms. The full
principal-angle cost sum and zero-gradient contribution remain to be assembled;
the unrestricted higher-rank minimum is not yet Lean-certified.

The zero-gradient restriction is now represented as an actual reflection in
`SchattenGradientBlocks.lean`: `gradient_kernel_reflection_representation`
constructs its unitary restriction and a star projection `S` with `V = I-2S`.
The generic two-point restriction proof works with allowed eigenvalues, so it
handles both endpoint phases without an artificial choice between `pi` and
`-pi`. The reusable `SchattenInvolution.lean` proves that a self-adjoint
unitary's finite Schatten displacement power is `2^(p-1)` times its nuclear
displacement, over either scalar field. `SchattenReflectionBound.lean` combines
this with the existing projection-distance inequality to bound the sum of
scalar minima over the accepted principal angles for every reflecting
transporter. The conventional proof now uses this trace argument. Applying
the bound to the restricted source and target, then assembling the complete
spectral cost sum, remains part of the unfinished global theorem.

`SchattenTransportExistence.lean` proves attainment on every nonempty finite
unitary transport fiber over real or complex scalars for finite Schatten
exponents at least one. It takes one feasible unitary as its nonemptiness
witness and returns an actual global minimizer. The proof uses operator-norm
compactness and `SchattenContinuity.lean`, which identifies the finite power
with the sum of the accepted approximation-number powers and proves its
continuity through rank changes. This is classical existence, not the exact
angle-dependent minimum. The signed maximal-gradient restriction is also
compiled, completing the zero, submaximal, and maximal restriction cases used
by the conventional proof.

The broader companion `smoothed_transport.tex` records the derivation of
exact complex transport for the Charbonnier spectral penalty
`rho_tau(s) = sqrt(tau^2+s^2)-tau`. With
`eta = (tau+sqrt(tau^2+4))/2`, its cutoff is `cos(theta)=eta^(-2)`;
above it the optimal phase is explicitly `arccos(eta^2 cos(theta))` and
the angle cost is `2 eta sin(theta)-2 tau`. Below it the canonical phase
is optimal. The scalar proof is a two-focus distance problem on a circle.
The unrestricted finite-dimensional proof uses an explicit unitary nuclear
norm support functional in cosine--sine coordinates and does not depend on
the Schatten higher-rank theorem, which was unformalized at this earlier
research stage but is now verified at `521572a2`. The same certificate proves
that relaxation of the commuting unitary factor to a commuting contraction
has exactly the same minimum, with an explicit diagonal optimal contraction
and phase recovery. This also solves nearest commuting-unitary correction
under the same smooth spectral penalty. Its all-minimizers and rounding extensions remain conventional proofs under
review. The proved minimum, explicit spectral optimizer, and stability result
are included through the focused `smoothed_transport_verified.tex`; the
broader companion is excluded from `paper.tex`.

The new `SmoothedPhaseMinimum.lean` now certifies the two-focus circle
inequalities, the explicit weighted scalar-phase minimum, its attaining phase
and uniqueness on the physical interval, and the algebraic specialization
`a=eta`, `b=eta^(-1)` to the displayed smoothing parameter. Its current
`smoothedPhaseCost` is defined through the weighted two-focus expression.
`SmoothedSpectralCost.lean` now proves the literal full displacement
singular-value Charbonnier sum equals the weighted nuclear norm, for every
finite complex unitary, including zero displacement. This uses the generalized
normal spectral-sum identity in `SchattenSpectralCalculus.lean`, which computes
arbitrary functions of all ambient-dimension singular values from the absolute
eigenvalues. The existing Schatten norm proof consumes that identity.
`SmoothedNuclearCertificate.lean` certifies a global lower bound
for the actual accepted nuclear norm of `A-b Z`, in an arbitrary supplied
orthonormal rotation eigenbasis with fixed directions. The competitor may
mix all planes; it suffices that it contracts every basis vector and that
paired diagonal entries have equal imaginary parts.
`SmoothedNuclearAttainment.lean` constructs an actual attaining diagonal
unitary and proves its exact accepted nuclear cost.
`SmoothedCommutantOptimization.lean` proves commutation with the actual
swapping source reflection implies the paired-diagonal condition, and returns
an actual unitary minimizing over all commuting contractions. These results
include arbitrary fixed directions and all mixing competitors.
`SmoothedSubspaceOptimization.lean` now instantiates the structural data for
the canonical nonacute rotation of every equal-rank complex subspace pair,
including right angles, and proves an attaining global minimum of the literal
Charbonnier singular-value cost against every unitary subspace transport.
Its exact value is `smoothedTransportMinimum`, the explicit spectral trace of
the canonical cosine operator. `SmoothedPrincipalAngles.lean` now identifies
that trace with the displayed sum over the accepted principal angles, and
`exists_unitary_minimizing_smoothed_transport_principalAngles` proves the exact
global formula with attainment and a lower bound for every admissible unitary.
The bridge uses a generic directed spectral-trace identity for the accepted
principal sines and a joint eigenbasis of commuting symmetric operators.
Zero angles, right angles, and zero-dimensional spaces are included.
`NonacuteCompression.lean` proves the diagonal cosine
compressions and the source-reflection reversal needed for this instantiation.
`NuclearTrace.lean` adds
the classical trace support inequalities consumed from the accepted Ky Fan
maximum principle and the normal-basis nuclear sum.

`PairedSpectralDecomposition.lean` now derives an actual paired orthonormal
eigenbasis for a symmetric operator reversed by an isometric involution,
over real or complex scalars. It consumes accepted real point-spectral spaces,
proves the involution exchanges their positive and negative parts, and identifies
the remaining space with the kernel. `PairedRotationEigenbasis.lean` applies
this to `R = C+iB`, with `C` positive, `B` symmetric, and `C^2+B^2=I`.
It derives paired rotation eigenphases in `(0, pi/2]`, the corresponding
cosine eigenvalues, and the fixed directions, with no supplied coordinate
chart. `SmoothedRotationOptimization.lean` consumes this construction and
proves the exact weighted nuclear minimum over commuting contractions is
`weightedRotationMinimum`, an explicit spectral trace of the positive cosine
operator, attained by an actual commuting unitary. Its hypotheses are the
structural operator identities and involution anticommutation; it no longer
assumes an orthonormal principal-plane chart. These basis constructions are
classical assembly mathematics, not independent novelty claims.

The fragment now also contains conventional proofs of all smoothed minimizers
and a quantitative stability bound below the transition. Distinct acute angle
summands cannot mix in an optimizer; on a supercritical angle of multiplicity
`m`, a self-adjoint unitary chooses the signs of the optimal phase. On the
right-angle summand the minimizers are all reflecting transports with an
arbitrary unitary matching of the two defect spaces. The canonical rotation is
therefore the unique minimizer exactly when every angle is at most the cutoff.
Below a strict maximum-angle cutoff, an explicit positive multiple of the
squared Frobenius distance to the canonical rotation is bounded by the
objective gap. The stability inequality is now Lean-certified as
`smoothed_transport_growth_of_principalAngles_le` in
`SmoothedSubspaceStability.lean`, with the explicit coefficient and its
positivity proved separately. It consumes accepted principal angles and the
literal singular-value cost and covers all admissible complex unitaries.
The classification assertion remains a conventional proof under review.
These results do not imply a
no-spurious-local-minimum theorem for the whole smoothed problem.

`SmoothedFunctionalPhase.lean` and `SmoothedExplicitOptimizer.lean` now
provide a named optimizer rather than only an existence theorem. The formula
uses functional calculus of the positive cosine operator: amplify each
principal cosine by `eta^2`, clip at one, and complete it on the positive
unit circle. Compose the canonical rotation with the adjoint of that phase
factor. Admissibility, the exact accepted-principal-angle sum, and global
optimality against every admissible complex unitary are compiled. The scalar
clipping identity is compiled; the separately displayed clipped nonunitary
contraction remains a conventional construction. The paper includes the
exact contraction relaxation as a conventional corollary of the same
certificate, and attributes formal verification to the global minimum,
unitary optimizer, and stability endpoints.

`SmoothedCommutingCorrection.lean` now formally transfers the exact
minimum to nearest commuting-unitary correction. Its cost is the literal
Charbonnier sum of singular values of `A-C`. The named
`optimalSmoothedCorrection` preserves the prescribed subspace, commutes
with its orthogonal projection, attains the principal-angle sum for the
subspace and its actual image, and is globally closest among all
commuting unitaries. No commutator surrogate is substituted for the actual
operator difference. `smoothed_transport_verified.tex` includes this
corollary as the concrete use of the transport formula; it claims exact
correction, without empirical application or algorithm-performance claims.

`SmoothedCriticalStability.lean` now certifies a critical-family growth
estimate beyond the earlier strict-subcritical theorem. Given any actual
skew-adjoint unitary `J` reversed by the source reflection, it constructs
`R=eta^(-2) I + sqrt(eta^2-eta^(-2))/eta * J` and proves the root bound
`Psi(W)-Psi(R) >= sqrt((n*d)^2 + ||W-R||_F^4/(4*eta^2)) - n*d`
against every admissible ambient transporter. The resulting fourth-power
error certificate is `||W-R||_F^4 <= 4*eta^2*epsilon*(2*n*d+epsilon)`.
This is an actual operator theorem, without a supplied principal-plane
chart or no-mixing assumption. Its geometric scope is the isoclinic family
with every angle critical and no fixed ambient directions. The sharper
root certificate and explicit constructed critical rotation are compiled;
the characterization of that normal form in terms of accepted principal
angles is conventional geometry. It is included as
`prop:smoothed-critical-stability`. That root certificate has the stated isoclinic scope; the separate
parameter-shift theorem below now covers arbitrary mixed angle lists with
a different quartic coefficient. Priority for the exact critical estimate remains
provisional; support-function rotation and finite trace identities are classical.

`SmoothedQuarticStability.lean` now extends stability to every equal-rank
complex subspace pair with all accepted principal angles at most the exact
cutoff, including arbitrary mixed critical/subcritical angles and fixed
summands. Its fully compiled inequality is
`3*tau*||T-R||_F^4 <= 32*eta^4*n*(Psi(T)-Psi(R))`.
The explicit objective-error bound and feasibility, global minimality, and
uniqueness of the canonical rotation are separate compiled endpoints:
`smoothed_transport_quartic_error_bound` and
`smoothed_canonical_unique_minimizer`. Zero-dimensional spaces are included
by the scaled statement; the paper divides by `n` only when `n>=1`.
The proof selects the nuclear support at `beta=b-delta`, separately from
the objective parameter `b`. Dual weights are at least `delta/a`; the support
loss is at most `n*delta^2/(2*(a-b))`. Optimizing the admissible shift with
the unitary diameter bound gives the explicit coefficient. The old exact
certificate API is retained as the self-parameter specialization of the new
`weightedNuclear_support_with_diagonal_defect` in
`SmoothedNuclearCertificate.lean`; its proof was generalized rather than
copied. This is included as `thm:smoothed-quartic-stability`, with the
sharper critical isoclinic root bound retained separately. The broader
mixed-angle investigation noted above is therefore resolved for this
quartic bound and canonical uniqueness. No classification of supercritical
minimizers is inferred. The coefficient is not claimed optimal, and priority
for these exact growth estimates remains provisional.

`SmoothedCanonicalOptimality.lean` now closes the necessary half of the
canonical cutoff at unrestricted finite complex rank. Its main endpoint
`smoothed_canonical_isMin_iff` states that the actual completed canonical
rotation is globally optimal exactly when every accepted principal angle
is at most `smoothedCriticalAngle tau`. The endpoint
`optimalSmoothedTransport_lt_canonical_of_supercritical` proves that the
named spectral-phase optimizer strictly improves the canonical cost whenever
one accepted angle exceeds the cutoff, including right angles. Together
with quartic uniqueness, this gives the full canonical-optimality decision,
not a classification of every supercritical minimizer. Included as
`cor:smoothed-canonical-cutoff`. The proof generalizes the existing diagonal
nuclear-cost computation in `SmoothedNuclearAttainment.lean` to all supplied
phases, rather than copying it, and adds the reverse paired-to-accepted
angle bound in `SmoothedPrincipalAngles.lean`. All former endpoints remain
consumers. Original Schatten-p arbitrary-rank and real matching minimum
claims remain outside this formalization.

The 2026-10-24 primary-source search for this extension checked the statements
of Bolotnikov--Li--Rodman (2001), especially Theorem 3.1 and Lemmas 3.2--3.3.
Their block-unitary distance problem is unweighted and Theorem 3.1 assumes
a Q-norm. The present smooth objective becomes
`nuclear(eta R - eta^(-1) V)`, with unequal scalar coefficients. Queries for
unitary Charbonnier/pseudo-Huber optimization, smoothed nuclear distance,
and weighted nuclear block-unitary approximation found no matching exact
formula. This is provisional negative evidence, not a priority certificate.
The statements reviewed in Bottazzi (2021), *Best approximation by diagonal
operators in Schatten ideals*, DOI `10.1016/j.laa.2021.02.025`, concern
Hermitian approximation by a linear space of diagonal operators. They provide
related classical duality criteria, rather than the present constrained
unitary problem or its explicit smoothed angle formula. Searches for scaled
unitary, weighted nuclear, and block diagonal unitary approximation likewise
found no matching formula; the absence of an indexed match is not proof of
priority.
The penalty, nuclear support inequality, cosine--sine decomposition, and
convex-relaxation method are classical. Any novelty claim must concern the
exact constrained minimum and its attaining phases, together with the exact
relaxation. Further citation-chain review remains necessary.

The primary paper Lobos--Salazar Cavazos--Nadakuditi--Fessler (2026),
*SIAM Journal on Imaging Sciences* 19(2), 839--878,
DOI [10.1137/25M175891X](https://doi.org/10.1137/25M175891X), explicitly studies
smooth singular-value regularizers, including the hyperbola penalty. Its
indexed primary text and metadata were checked through
[PMC](https://pmc.ncbi.nlm.nih.gov/articles/PMC13138729/) and
[PubMed](https://pubmed.ncbi.nlm.nih.gov/42089089/).
This supports the penalty's established optimization relevance; their inverse
problem constraint differs from the unitary transport constraint. No empirical
improvement in their applications is claimed.

The additional excluded fragment `spectral_penalty_transport.tex` gives a
conventional general decoupling criterion. A convex, increasing, radial penalty
with zero derivative at zero has independent principal-plane minimization if
its circular phase derivative has exactly one increasing and one decreasing
branch, with strictly negative curvature on the latter. The Schatten proof's
large-phase overlap variation then works verbatim; zero-gradient reflections
are bounded using convexity and the nuclear projection-distance inequality.
Nonincreasing positive logarithmic elasticity `s rho''(s)/rho'(s)` suffices.
The family `(tau^2+s^2)^(p/2)-tau^p`, `1 <= p <= 2`, `tau > 0`, satisfies
this criterion and has the explicit local curvature cutoff stated there.
This general theorem is a conventional proof draft, not Lean-certified;
its novelty is provisional. It asserts global value decoupling, without
claiming a unique scalar optimizer or absence of nonglobal local minima for
the entire penalty class. The real-line smoothed cutoff in the separate
fragment follows from the existing real rank-one spectral pairing argument;
it is not registered as an independent novelty claim.

The conventional draft also describes all acute minimizing transporters:
on the multiplicity space of each supercritical angle they are the canonical
rotation times `exp(i delta(theta) S)`, with `S` any self-adjoint unitary.
The resulting families are disjoint unions of complex Grassmannians; for
distinct positive angles there are exactly `2^k` minimizers when exactly
`k` angles are supercritical. Uniqueness is equivalent to every angle being
at most the cutoff. This characterization uses the unformalized higher-rank
block argument and is not a new compiled result.

The same conventional classification yields an acute real-versus-complex
criterion: the real minimum equals the complex minimum exactly when every
supercritical angle has even multiplicity. In a real cosine--sine chart,
`exp(i delta S)` is real exactly when `S = iJ`, where `J` is a real
orthogonal complex structure. Such a structure exists exactly in even
dimension. An odd supercritical multiplicity gives a strict gap by compactness.
This is a corollary of the unformalized optimizer classification, not a
compiled real optimization theorem or an exact formula for the larger real
minimum.

A further primary-source check on 2026-10-24 visually verified Table 5.1
on printed page 116 of Aubrun--Szarek's author-provided
[Chapter 5 PDF](https://case.edu/artsci/math/szarek/ABMB/ABMBchapter5.pdf).
Its caption specifies quotient metrics from extrinsic Schatten norms, while
its Grassmann diameter entries use `sqrt(2) * (2k)^(1/p)` for the displayed
full exponent range. This appears incompatible with the elementary real
rank-one quotient calculation when `p < 2`: the cost is at most two for
every pair, by a reflecting transporter. The raw Appendix B normalization
and full exercise statements remain to be checked from a primary copy;
the author's full PDF has been unavailable. Do not yet claim a book erratum
or infer research priority from this discrepancy.

A subsequent indexed-primary-PDF search recovered Appendix B's equation
(B.13), which defines precisely the unrestricted orthogonal/unitary
transport quotient used here, and Exercise B.12, which gives the canonical
principal-angle expression across the displayed Schatten range. Thus the
metric normalization can now be compared at the formula level. The actual
Appendix PDF remains unavailable for visual verification. The authors'
[posted errata](https://case.edu/artsci/math/szarek/ABMB/errata.pdf), last
updated 7 September 2023, contain no entry for these pages. This does not
establish an unreported error or priority; retain the visual-verification
and independent-review requirement before making a source-correction claim.

The independent fragment `real_four_dimensional_transport.tex` now supplies
an exact conventional solution for real rank-two transport in `R^4`.
For any continuous nondecreasing spectral penalty, the minimum is the smaller
of a restricted scalar-phase cost and a reflection on the larger-angle plane.
Its proof treats all four components of the real stabilizer by the actual
four-dimensional characteristic polynomial. The Schatten corollary clips the
scalar optimum to `[d,h]`, where `h` and `d` are half the angle sum and
difference. The nuclear cost has the closed formula
`min(4 sin(h), 2+4 sin(theta2/2))`, with `theta1 >= theta2`. The Charbonnier
cost has explicit coupled-rotation and reflection branches and an exact
two-inequality canonical region. These real optimization results are
conventional proofs under review, not Lean-certified. They are excluded from
`paper.tex`. Numerical unrestricted searches in all four stabilizer components
agreed with the four-dimensional formula; these checks are not proof evidence.
No matching formula was found in the inspected primary literature, including
Bolotnikov--Li--Rodman (2001). That is provisional negative evidence.

`real_matching_transport.tex` develops the higher-rank real problem as a
finite maximum-weight matching problem. At a real stationary transport, the
skew spectral gradient has zero source-diagonal compressions. On a positive
gradient-square level it defines a complex structure, while source reflection
acts as conjugation. The unitary has at most two complex phase roots, and its
Hermitian spectral projection has a real orthogonal normal form with blocks
of size at most two. Thus the original real space splits into blocks of size
at most four, each carrying at most two principal angles. The exact
four-dimensional formula then gives the matching lower bound; independent
one-plane and paired-plane constructions attain it. Convexity of the penalty
and negative second variation are not required for this real reduction.

The fragment also proves the real nuclear matching formula by a uniform
Charbonnier limit, the even-multiplicity equality criterion including right
angles, and the exact real smoothed canonical region determined by the two
largest angles. It explains the equivalent nearest commuting-orthogonal
correction problem. These are conventional proofs under review, not
Lean-certified, and remain excluded from `paper.tex`. Unrestricted numerical
multistart searches in real dimensions six and eight agreed with the matching
value for Schatten `3/2` and Charbonnier costs; they do not establish the
theorem. The stationary-block proof and literature priority need independent
review before submission. The classical real orthogonal normal form for a
Hermitian projection is an ingredient, not an independent novelty claim.

The first formal foundations for this real reduction now compile.
`OrthogonalComplexStructure.lean` consumes accepted almost-complex modules
and compatible Hermitian cores, proves compatibility with the original real
Hilbert norm, and constructs a real orthonormal basis in quarter-turn pairs.
`Projection/RealBlocks.lean` proves the explicit invariant line/plane step
and the complete orthogonal decomposition for real symmetric/skew components
satisfying the projection identities. These are classical foundations for
the matching proof; the actual real transport optimization endpoints are
still conventional assertions awaiting formal assembly.

`Complexification/Parts.lean` now proves the general operator decomposition
into real and imaginary components, including noncommuting product formulas,
using the established concrete complexification and real-part operator.
`Projection/ComplexRealBlocks.lean` derives the component symmetries and
projection identities from an actual Hermitian projection and instantiates
the complete orthogonal line/plane decomposition. Thus this algebraic step
of the real matching proof is certified without supplied component data or
a principal basis. The complete stationary-block assembly and final matching
optimization are still partly conventional; the compiled real stationarity
and positive-level results are registered below.

The real matching fragment now gives a canonical-optimality criterion for
every Schatten exponent `1 < p < 2` using only the two largest principal
angles and the small root of the scalar amplitude equation. At `p = 3/2`
this becomes the elementary pair of inequalities
`x1 <= 2^(-2/3)` and `x1^2 + x1*x2 + x2^2 <= 1`, where
`xi = sin(theta_(i)/2)`. All three-halves edge weights and their attaining
common rotations are explicit. The same fragment derives the sharp real
rounding constant `(1 - 2^(-2/p))^(-1/2)` for `1 <= p <= 2`.
These are conventional consequences under review, not Lean-certified.
`figures/real_transport_matching.pdf` illustrates the two-angle phase
diagram and a six-angle matching selecting a largest-angle reflection
before pairing $80$ with $75$ degrees. This is the shifted adjacent-pairing
choice in the stronger sorted-sum result below. The figure evaluates the
derived formulas, not an independent proof.

The two-phase algebraic reduction is now compiled beyond the projection
components. `Complexification/RealPoints.lean` consumes the accepted
`TauCeti.realPoints` and its real/imaginary decomposition, supplying the
isometric comparison to the established concrete Hilbert complexification.
`Complexification/FiniteDimensional.lean` supplies its finite-dimensional
instances and exact dimensions. `RealTwoPhaseBlocks.lean` proves that an
actual operator affine in a Hermitian projection has a complete orthogonal
invariant decomposition into complex blocks of dimension at most two,
simultaneously invariant under a specified isometric conjugation. Their
real dimensions are at most four. No supplied real basis is required.
`SchattenRealStationarity.lean` now proves the source-reflection stationarity
identity under only real feasible unitary variations. Real operators are
represented as fixed points of canonical operator conjugation on the
established complexification. `SchattenConjugation.lean` proves that a
conjugate-linear symmetry of a normal operator reverses its Schatten phase
gradient. The complexification specialization also certifies that the
Hermitian directions reversed by conjugation generate real unitary curves.

`SchattenRealGradientBlocks.lean` derives phase data on every positive
gradient level through the maximum of an actual real local minimum and constructs
the source-induced isometric conjugation there. It applies the compiled
projection decomposition to obtain a complete common orthogonal invariant
family with complex dimensions at most two. This uses the accepted
submodule-map isometry through `AnticommutingConjugation.lean`, rather than
assuming a real basis or phase projection. `RealBlockDescent.lean` now
certifies the lift to the original real ambient space: doubling each
positive-level block by source reflection gives a conjugation-stable block,
whose real preimage has dimension at most four. The actual real transporter
and source reflection preserve these blocks. The lifted family is pairwise
orthogonal and its complexification covers the entire positive level and
its reflected negative level. Nontriviality, dimensions, orthogonality,
invariance, and coverage are compiled. At the maximum the two branches
coalesce, and the compiled scalar critical-phase representation supplies the
same real-block construction. The zero-gradient real assembly is now compiled
as described below; the exact matching minimum remains unformalized. The conventional general-penalty
matching and nuclear consequences are not promoted to compiled results by
this partial assembly. The focused modules, `DavisKahan.All`, and `ForTauCeti`
build; the new endpoint axiom checks use only the three standard axioms.

`Projection/TwoBlocks.lean` now proves the classical finite two-projection
lemma over either real or complex scalars. Every nonzero common invariant
space contains a common invariant line or plane; orthogonal-complement
induction gives a complete orthogonal family of blocks with dimension at
most two. The small block is generated by a joint eigenvector of one
projection and the diagonal compression of the other. The proof consumes
the existing joint eigenbasis API. This is the foundation needed for the
real zero-gradient reflection block, not an independently novel theorem.
Both the donor and the critical-level extension pass the full mathematical
build and standard-axiom audit; their final use in the real optimizer
endpoint is supplied by the zero-level construction below.

`SchattenRealKernelBlocks.lean` now completes the actual zero-gradient
real decomposition. The restricted transporter is a reflection, and both
its negative-phase projection and the source projection commute with the
restricted ambient conjugation. `Projection/ConjugationBlocks.lean`
restricts the two projections to the accepted fixed real subspace and
consumes the classical two-projection block theorem. The fixed real space
is carried isometrically to the original real preimage through
`RealBlockDescent.realPointsDescentEquiv`. The resulting nonzero real
lines and planes are pairwise orthogonal, invariant under the actual
source projection and transporter, and their complexification covers the
entire gradient kernel. This closes the exceptional zero-level block
construction; the global assembly over all levels, identification with
principal-angle blocks, and matching lower bound remain separate obligations.
No unrestricted real matching minimum is thereby claimed.

The matching reduction has been strengthened for all Schatten powers
`1 < p < 2` and for Charbonnier penalties. Their two-angle cost is symmetric,
nondecreasing, and submodular. On the active region it depends on the mean
angle through a concave scalar minimum; on the inactive region it is
additive, and the first derivatives agree at the junction. Submodularity
puts a canonical singleton at the smallest angle and proves adjacent
pairing, while monotonicity puts a reflection at the largest angle.
Thus the exact real minimum is the smaller of two sorted sums, with or
without the largest-angle reflection. Only linearly many scalar pair costs
are evaluated after sorting. For Schatten `3/2` and Charbonnier all these
costs are explicit. The broader single-peak-penalty theorem remains a
matching result; submodularity has not been claimed for that entire class.
These ordering and exact-minimum statements are conventional proofs under
review, not Lean-certified.

The nuclear sorted-sum formula now follows by a uniform Charbonnier limit.
Its paired cost is `4 sin((theta+psi)/2)` and reflection cost is two.

Second, the real nuclear minimum exceeds the complex one by at most
`2 - sqrt(3)`, independently of dimension and rank; one angle `pi/3`
attains the constant. The proof maximizes the gap on the compact ordered
angle simplex. Boundary lists reduce to fewer angles. At an interior
maximum the two sorted costs must tie; their stationary convex combination
has positive definite Hessian by strict concavity of `sqrt(1-q^2)` applied
to the cosine balance equations. A nonzero tangent direction on the tie
hypersurface rules out such a maximum when there are at least two angles.
These theorems are conventional proofs under review, not Lean-certified,
and their mathematical priority remains provisional. Differential-evolution
experiments up to eight angles agreed with the gap bound, and random
matching comparisons up to nine angles agreed with the sorted-sum formula;
neither experiment is part of the proof.

The smoothed analogue has the sharp additive field gap
`Delta_tau = 2 eta (1 - sqrt(1 - 1/(4 eta^4)))`, attained by one
angle with `cos(theta) = eta^(-2)/2` and complex scalar phase `pi/3`.
Its proof fixes subcritical planes canonically, applies the sorted matching
construction to supercritical angles, and extends the same tie-Hessian
maximum argument. The canonical singleton derivative
`q = sin(theta)/(eta sqrt(tau^2+2-2cos(theta)))` satisfies
`q >= cos(theta)` and `q' >= -sqrt(1-q^2)`, supplying the endpoint
Hessian bound. The gap approaches `2 - sqrt(3)` as smoothing vanishes and
is asymptotic to `1/(4 tau^3)` for large smoothing. This is a conventional
proof under review, not a compiled real rounding theorem. It supplies a
dimension-independent error bound for enforcing real transports after
the exact complex relaxation; no empirical application benefit is claimed.

The sharp field-gap drafts now also classify all equality cases. For the
nuclear cost, the maximum gap `2 - sqrt(3)` occurs exactly when every
positive principal angle is `pi/3` and the number of such angles is odd.
For Charbonnier, put `r_tau = acos(eta^(-2)/2)` and
`a_tau = 2 atan(tau/(sqrt(tau^2+4) tan(r_tau/2)))`.
The maximum gap occurs exactly for an odd number of angles `r_tau`, with
all remaining angles at most `a_tau`. These follow by equality in the
compact induction: deleting a right angle or an unequal repeated pair
permits a strict improvement by coupling with the remaining exceptional
angle. Subcritical smoothed angles are harmless precisely when their pair
cost with `r_tau` is inactive. Both equality classifications are conventional
proofs under review, not Lean-certified, and priority remains provisional.

The scalar Schatten draft now gives a hyperbolic parametrization. With
`beta=(2-p)/p`, the supercritical acute optimum is determined by the unique
`u>0` satisfying `cos(theta)=sinh(beta*u)/sinh(u)`, and its phase obeys
`cos(delta)=cosh(beta*u)/cosh(u)`. The ratio is strictly decreasing from
`beta` to zero. For `p=2n/(n+1)`, this becomes the single Chebyshev polynomial
equation `U_(n-1)(z)=sec(theta)` with unique root `z>1`.
At `p=4/3`, this yields the explicit phase
`cos(delta)=cos(theta)/(1-2cos(theta)^2)` and scalar minimum power sum
`2^(4/3)*(1-2cos(theta)^2)^(1/3)` above the cutoff `pi/3`.
The real matching costs and their attaining rotations are consequently
explicit at this additional exponent. For all `p=1+1/m`, `m>=2`, the real
canonical pair test is the polynomial inequality
`sum_(j=0)^m u1^(m-j)*u2^j <= 1`, where
`ui=sin(theta_(i)/2)^(2/m)`, together with
`u1 <= 2^(-2/(m+1))`. These derivations are conventional proofs under
review, not Lean-certified; no separate historical priority is claimed for
the hyperbolic or Chebyshev identities. Numerical checks against scalar
minimization agreed at several exponents and angles; they are not proof.

A proposed extension of the sharp field-gap bound to arbitrary Schatten
powers is not established. Numerical maximizations at `p=3/2` through
twelve angles agree with the rank-one candidate, but the strict
curvature-concavity certificate used for nuclear and Charbonnier costs
does not carry over directly. No general-power sharp additive gap theorem
is claimed in the drafts.

A further primary-source comparison on 2026-10-24 checked Antonini--Cavalletti,
*Geometry of Grassmannians and optimal transport of quantum states*,
Annali SNS Pisa 27 (2026), 201--254,
<https://journals.sns.it/index.php/annaliscienze/article/download/6312/2877/5943>.
Printed pp. 204, 210 and Definition 4.2 on p. 228 use the intrinsic
Hilbert--Schmidt geodesic distance on the Grassmannian as the base cost
for Wasserstein transport of spectral measures. This is a different
optimization domain and objective from minimizing a chordal spectral
penalty of an ambient transporter. No extrinsic real two-sum formula or
sharp real-versus-complex field-gap result was found there. This comparison
is source-level negative evidence, not a priority certificate.

The additional weighted-Procrustes comparison checked three primary sources
on 24 October. Contino--Giribet--Maestripieri (2017),
<https://arxiv.org/pdf/1610.00558>, equation (1.4) and Theorem 4.5,
minimize `||W^(1/2)(AX-B)||_p` over every bounded `X`, without a
unitary or commutation constraint. Taking `A=bI`, `B=aR` gives zero
at `X=(a/b)R`, which violates our contraction condition when `a>b`.
Their result therefore does not determine our constrained optimum.
Corach--Massey--Ruiz (2014),
<https://arxiv.org/pdf/1309.7914>, equation (4) and Theorem 7,
optimize `||FX*-I||` over Parseval coisometries. At square size, with
`F=(a/b)R`, the free unitary factor removes `R`; after rescaling the
minimum is `n(a-b)`. Our commuting restriction prevents that removal:
at a single right angle in dimension two its minimum is `2a`.
Thus the Parseval theorem does not directly imply our value either.
Fulova--Trnovska (2023), <https://arxiv.org/pdf/2304.14961>, Table 1
and Section 1, give conic formulations and numerical methods for constrained
real Procrustes problems, with Frobenius, spectral, and induced row/column
norms. These statements do not give a closed smoothed/nuclear angle formula.
Watson (1994)'s publisher abstract remains accessible, but the full theorem
text was not obtained; its exact implication is still unresolved. These
comparisons exclude direct applications of the inspected statements, not
all equivalent prior results or broader reductions.

A further primary comparison checked Bottazzi, *Best approximation by
diagonal operators in Schatten ideals*, Linear Algebra and its Applications
620 (2021), 1--26, DOI <https://doi.org/10.1016/j.laa.2021.02.025>.
The publisher's text formulates additive best approximation of Hermitian
operators by the full linear space of diagonal operators and develops
support-functional and Birkhoff--James characterizations. Those are
classical antecedents for a support-certificate method. The stated domain
has neither the commuting-unitary restriction nor the bounded commuting
contraction constraint used in our weighted problem. This rules out a
verbatim identification of the problems, not a possible reduction through
a stronger general approximation result. The author-repository PDF was
located but returned HTTP 403; exact theorem-level comparison beyond the
publisher's exposed text remains incomplete. No priority claim is inferred
from this access limitation.

The older primary source Bouldin, *Best approximation of a normal operator
in the trace norm*, Acta Sci. Math. (Szeged) 51 (1987), 467--474,
<https://acta.bibl.u-szeged.hu/15159/1/math_051_fasc_003_004_467-474.pdf>,
was checked at Theorems 3 and 11. It minimizes over the full cone of positive
operators and classifies uniqueness in that cone. On one strict-subcritical
rotation plane, Theorem 3's positive approximant is `a cos(theta) I`.
Its norm exceeds `b`, so it is outside our bounded contraction set, and its
nuclear error `2a sin(theta)` is strictly smaller than our
`2 sqrt((a cos(theta)-b)^2+a^2 sin(theta)^2)`. Thus the stated positive-cone
minimum is not our constrained value. This comparison also reinforces that
spectral clipping and nuclear approximation have classical antecedents;
possible reductions through bounded-spectrum refinements remain a priority
question, not excluded by the difference of feasible sets alone.

The 2026 follow-up by Bottazzi--Varela,
<https://arxiv.org/pdf/2604.16041>, was checked at Section 1 and Theorem 1.
It treats Hermitian additive approximation by a full C*-subalgebra in the
spectral norm, with trace-annihilator support witnesses. That theorem
supports the classical ancestry of the certificate method and has a
different objective and feasible set from our commuting-unitary weighted
nuclear minimum. This is a comparison of the inspected statement, not an
exhaustive exclusion of all consequences of that paper.

`SmoothedCriticalFlatness.lean` adds a compiled scalar sharpness certificate
for the cutoff. For `b,d>0` and a unit phase `z` with
`|b Im(z)| <= d/2`, the tangent two-focus excess is between zero and
`b^2 |z-1|^4/(2d)`. The endpoint
`critical_phase_no_quadratic_modulus` constructs arbitrarily close nonzero
unit phases violating every positive quadratic modulus. This is included as
`prop:smoothed-critical-flatness`. `SmoothedCriticalTransportFlatness.lean` now closes the operator interpretation:
`smoothed_critical_planar_no_quadratic_growth` uses actual unitary
transporters between the established model lines at the exact cutoff,
the literal singular-value cost, and Frobenius distance. Its final signature
requires no supplied eigenbasis or normal-form hypothesis. The internal
spectral calculation and its general two-dimensional endpoint are separate
from this concrete model instantiation. Together with the unrestricted quartic lower bound, it
explains why the quadratic certificate cannot persist at the cutoff.
The exact factorization `critical_phase_quartic_factorization` and limit
`tendsto_critical_phase_quartic_ratio` now certify the leading scalar
coefficient `b^2/(4d)`. On the actual critical plane the corresponding
Frobenius fourth-power coefficient is `b^2/(16d)`, matching the leading
term of the root lower bound at dimension two. This last comparison is
algebra in the manuscript; the general quartic bound's global coefficient
is not claimed optimal. No new general error-bound principle is claimed.

`SmoothedCalibration.lean` inverts the canonical cutoff as an explicit
smoothing-scale test. For every accepted acute angle, canonical global
optimality is equivalent to `tau >= (1-cos(theta))/sqrt(cos(theta))`.
The scalar threshold and preservation under increasing smoothing are compiled,
as is the unrestricted all-pairs complex equivalence. The manuscript gives
the short algebra after `cor:smoothed-canonical-cutoff`. This is a useful
parameter-selection consequence, not a separate novelty claim.

`SmoothedCorrectionStability.lean` transfers both growth certificates to
the literal operator-difference correction objective. The Frobenius distance
between a feasible correction and `R* A` equals the distance between its
associated transporter and `R`. The compiled endpoints are
`smoothed_correction_quadratic_growth`, `smoothed_correction_quartic_growth`,
and `optimalSmoothedCorrection_eq_canonical_of_angles_le`. The final endpoint
identifies the previously named spectral correction with the canonical
correction in the closed regime. The manuscript gives its fourth-root
objective-error bound and cites the transferred strict quadratic estimate.
These are utility consequences of the transport theorem, with no empirical
performance or separate priority claim.

`SmoothedValueSensitivity.lean` proves a sharp value-sensitivity certificate.
The least Lipschitz constant of the exact scalar minimum on `[0,pi/2]` is
`2/eta`. Both branches join differentiably at the cutoff, and the derivative
there is `2/eta`, proving necessity. The finite-sum endpoint bounds the
error in the exact global value by `2/eta` times the sum of the angle errors.
The main endpoints are `smoothedPhaseMinimum_lipschitz`,
`sum_smoothedPhaseMinimum_lipschitz`,
`smoothedPhaseMinimum_hasDerivAt_critical`, and
`lipschitzOnWith_smoothedPhaseMinimum_iff`. Included as
`cor:smoothed-value-sensitivity`; this is a quantitative consequence of the
minimum formula, with no separate first-publication claim.

`SmoothedCommutatorCutoff.lean` gives the directly computable operator-norm
criterion for the canonical correction: `||AP-PA|| <= sqrt(1-eta^(-4))`
is necessary and sufficient for its global minimality. The actual unitary
input and source subspace are used, with no supplied principal coordinates
or maximum-angle witness. It covers the boundary and dimension zero.
The main endpoint is `canonical_correction_isMin_iff_commutator`, with
`projectionGap_unitary_image_eq_commutator` and
`smoothed_canonical_isMin_iff_projectionGap` as bridges. The manuscript
states the criterion in the correction application. The projection norm
identity is classical; no separate priority claim is made for it.

`SmoothedOptimizerUniqueness.lean` now classifies uniqueness of the actual
global minimum at every finite complex rank. The endpoint
`smoothed_transport_unique_minimizer_iff` states that a unique feasible
global minimizer exists exactly when all accepted principal angles are at
or below the cutoff. Above it, the named
`oppositeOptimalSmoothedTransport` is feasible, attains the same exact angle
sum, is globally minimizing, and is distinct from the earlier optimizer.
The proof uses the opposite signs of the spectral phases and the accepted
paired-angle bridge; no chart or no-mixing condition is supplied to the
final theorem. The shared literal nuclear computation is now
`nuclear_phaseTransport_eq_sum_weightedPhaseCost` in
`SmoothedNuclearAttainment.lean`, consumed by both phase signs rather than
duplicating the positive optimizer's proof. Included in
`cor:smoothed-canonical-cutoff`. The classification of every supercritical
minimizer remains conventional and excluded from the article.

The correction endpoint
`smoothed_correction_unique_minimizer_iff_commutator` now proves that the
same commutator inequality is also necessary and sufficient for uniqueness
of the closest feasible correction. The proof uses an explicit equivalence
of ambient unitary groups, transfers both feasibility and global minimizing
properties, and consumes `smoothed_transport_unique_minimizer_iff`.
This is stated in the included application, with equality included.

The direct primary check of Lobos et al. (2026), Section 2.1, equation (2.2),
<https://pmc.ncbi.nlm.nih.gov/articles/PMC13138729/>, confirms the normalization:
its hyperbola is `psi_delta(s)=delta^2 sqrt(1+(s/delta)^2)`, equal to
`delta*rho_delta(s)+delta^2` for positive `delta`. The fixed-dimension
singular-value sum therefore differs by a positive scale and an additive
constant. Their low-rank inverse-problem optimization supplies precedent
for the penalty, not for this unitary transport constraint or its exact
minimum. The manuscript now states the normalization qualification.
The Chubb--Flammia sentence refers to nearby commuting operators, preserving
the distinction between the published ground-space-unitarity condition
and the older author version's ambient unitary construction recorded above.

The integrated journal text typesets successfully with `pdflatex`, `bibtex`,
and two further LaTeX passes. This VM lacks `latexmk`; its default T1 Computer
Modern fonts also need microtype expansion disabled for the local build.
The source was compiled with the command-line option
`\PassOptionsToPackage{expansion=false}{microtype}` and output under
`build/journal-smoothed/`, without changing mathematical statements or
committed font settings. The displayed smoothed Lean signature also
elaborates independently against the production theorem.

- Main file: `paper.tex`; optional red-framed working variant: `paper_working.tex` (sets `DKWorkingDraft`).
- Mathematical text built by the manuscript: `counterexample.tex`, `sharp_displacement.tex`, `smoothed_transport_verified.tex`. The all-pairs complex theorem is now in the checked manuscript. The only red-framed provisional theorem is the **real** line/hyperplane result, gated by `includeUnformalizedRealTransport` in `paper_working.tex`. The old `sharp_displacement_unformalized.tex` is a retired conventional proof note, not included in either manuscript. `sharp_displacement_verified.tex` is also an older detailed record.
- Symbol colors: `math_symbol_colors.tex`; `\DKMathColorsfalse` after its input turns symbol colors off. Keep the readable Manim-derived shade map and `appendix_notation.tex` aligned.
- Primary manuscript reference metadata: `references.bib`; historical detail: `PROPOSITION_4_4_LITERATURE_MAP.md` and `submission/LITERATURE_AUDIT.md`.
- Source and statement evidence: `claims_to_evidence.md`, `submission/VALIDATION.md`, source inventories under `dev/`.
- Other non-paper research: `MATHEMATICAL_COMPANION.md`, `REAL_TRANSPORT_MINIMIZATION_NOTES.md`, `papers/what_it_takes_to_prove_davis_kahan/`.
- Writing rules: `AGENTS.md`, `STYLE_GUIDE.md`, `../BANNED_WORDS_AND_PHRASES.md`, `../SPECIFIC_NEGATIVE_PROMPTS.md`. Avoid putting revision history, proof-status disputes, literature negative-evidence logs, and agent instructions into the rendered article. Maintain them here.

## Questions that would alter publication claims

1. Is the **all-norm sharp direct-rotation factor** stated, or an exactly equivalent optimization stated, in older constrained unitary/Grassmann literature? Read theorem statements, not abstracts; use the `LIT` entries in `PROPOSITION_4_4_LITERATURE_MAP.md` to continue the citation graph.
2. Has a paper **explicitly identified failure of the real, short-angle Proposition 4.4** before this project? An earlier general trace-norm nonminimality claim is not equivalent evidence of that recognition.
3. Has the general complex minimum, now formalized through paired nonacute phase corrections rather than a supplied principal-plane chart, appeared verbatim in prior mathematics? Distinguish the classical ingredients from the newly verified Lean assembly and the exact principal-angle formula.
4. Have the optional **real rank-one minimization and least uniform sqrt(2) constant** formalizations been user-confirmed built? Do not infer this from their existence as files.

Update this document with dated, source-linked findings when one of these boundaries changes. Manuscript prose should contain the mathematical result after an issue is resolved, not an account of this decision log.

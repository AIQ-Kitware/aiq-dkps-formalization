# Mathematical novelty review: Davis--Kahan and spectral-penalty transport

**Research record, not manuscript prose.** 24 October 2026. Original review snapshot:
`b251994524e7f4a5145f3a045b757cad30c6dbf9` (source archive dated
2026-10-24 08:51). Scope: the Davis--Kahan formalization and subsequent
finite-dimensional subspace-transport optimization program. **YWS is excluded**;
its source investigation and conference stub live in
`../yws_formalization_conference/`.

**Question:** What has the project established that could be an original
mathematical result, as opposed to a formalization achievement, an explicit
correction of a printed statement, or a consequence of standard projection
and matrix geometry?

**Current verification frontier:** the 25 October entry supersedes earlier
pending phase-parameter assessments. The original source snapshots and
literature comparisons below remain historical research records.

## Ambient Charbonnier no-overlap and balanced kernel restrictions (25 October)

The ambient block-construction step is now compiled.
`gradient_block_no_overlap_of_isLocalMinOn_transports_complex` constructs
the actual opposite eigenspace restrictions at every positive submaximal
gradient level of **any** finite complex local transport minimum, uses the
actual source reflection, extends its feasible variation, and proves
disjointness of the two negative-curvature projections. No prescribed frame
or exception excluding identity/right-angle directions is supplied.
`signed_critical_gradient_eigenspace_representation_complex` separately
identifies every actual signed maximal restriction with its scalar critical
phase, without a minimizing hypothesis.

`gradient_kernel_local_reflection_restriction_complex` transfers actual
local minimality to the actual zero-gradient kernel, retains its unitary
and source actions, and gives a reflection `I-2*S` with `2*S*P0*S=S`.
The formal Hessian exposed a shorter exceptional-block argument: the
source-preserving Hermitian direction `H=P*A+A*P-A` has zero positive-space
compression and negative-space compression `D=2*A*P*A-A`. The actual
curvature is exactly `-||D||_HS^2/sqrt(tau^2+4)`. Every unbalanced reflection
therefore has a certified negative-curvature direction. This proves the
balance identity in all ranks, replacing the planned separate two-plane
descent for this step.

This is a proof insight produced while consuming the formal Hessian, and a
concrete correction certificate. Historical priority is not asserted for
this elementary balance argument. The classical projection geometry,
Lewis--Sendov Hessian precedent and local-Lidskii scope comparisons below
remain applicable. The **full Charbonnier local-to-global theorem is still
open**: disjoint paired scalar costs, balanced kernel geometry/cost and
assembly into the global principal-angle value remain to be formalized.
The scalar Vieta route for the next cost identity is recorded explicitly in
`PAPER_CONTEXT.md`; it is a conventional derivation pending Lean.

## Charbonnier two-phase Hessian and ambient reflection restrictions (25 October)

The actual Charbonnier two-phase Hessian is now compiled for `tau>0`,
distinct balanced phases and arbitrary multiplicities, **including identity
and reflection eigenvalues**. The operator gradient derivative also permits
infinite-dimensional complete complex Hilbert spaces; the literal trace
objective remains finite-dimensional. Its exact two curvature coefficients
change sign at `cos(t)=eta^-2` and equal `1/tau` and
`-1/sqrt(tau^2+4)` at the two zero-gradient endpoints.
`SmoothedScalarVariation` separately proves the one-point formula, including
zero Hessian in every Hermitian direction at a critical/coalesced scalar
phase of arbitrary multiplicity. This does not imply local minimality or
higher-order growth for an unpaired scalar block.

`SmoothedNoMixing` proves strict negative second variation for overlapping
negative-curvature projections and disjointness at a local minimum of the
**prescribed paired curve**. `SmoothedReflectionSecondVariation` proves an
**ambient** Hessian necessity for actual two-phase local transport minima,
the explicit reflection compression inequality, and exclusion of negative
spectral subprojections commuting with the source. The latter conclusion
requires the actual transporter itself to be a reflection. The preceding entry closes actual ambient no-overlap, maximal scalar
restrictions, transfer to the actual kernel and reflection balance. Scalar
block costs and global value assembly remain open.
There is still no compiled Charbonnier local-to-global theorem.

The primary author-hosted [Lewis--Sendov paper (2001), Theorem 3.3](https://people.orie.cornell.edu/aslewis/publications/01-twice.pdf)
was read directly. It gives the Hessian of a twice differentiable real
symmetric spectral function, with the repeated-eigenvalue and divided-
difference terms. This is classical precedent for the calculus mechanism;
it does not identify the optimizer set of the prescribed-projection fiber.
No independent historical novelty is claimed for these Hessian identities
or necessary tests. The stronger classification/landscape results retain
their previously recorded novelty boundary.

## Charbonnier local stationarity and actual gradient spectra (25 October)

The local-to-global campaign now has its actual analytic first layer:
`SmoothedUnitaryVariation` differentiates the **literal** singular-value
Charbonnier objective along Hermitian unitary curves at every time, and
`SmoothedStationarity` derives trace annihilation and source-reflection
anticommutation from actual constrained local minimality. Every finite
complex transporter and `tau>0` is allowed; repeated eigenvalues, identity
eigenvalues and right angles require no exclusions.

`SmoothedGradientSpectrum` proves an exact nonnegative-square gradient
deficit, the sharp `eta^-1` scalar and operator bounds, equality at an actual
critical-phase eigenvector, an algebraic two-candidate description of every
gradient level, and the **actual** affine projection representation of the
unitary on each gradient eigenspace. Its actual zero-gradient restriction
is `I-2*S`, with no minimizing assumption. `SmoothedGradientPairing` proves
actual reflection pairing of opposite levels and reduction of both source
and target by the squared gradient. The included manuscript endpoint is
`prop:smoothed-local-spectral-structure`.

These are proved necessary local structure, **not** the Charbonnier
local-to-global theorem. The distinct-phase second variation and paired overlap exclusion are now
closed in the preceding entry. The remaining proof must extract their actual
ambient blocks, handle coalesced and nonoptimal reflection blocks, and
assemble the value.
The general first-variation theorem in `UnitarySpectralVariation` is consumed
by both penalties. Its continuous supporting-field hypothesis does not cover
the nuclear singularity at identity. No independent priority claim is made
for scalar calculus, spectral-trace differentiation or anticommuting eigenspaces.

The primary [Massey--Rios--Stojanoff paper](https://arxiv.org/html/1806.11436)
was rechecked at Theorems 3.5 and 3.12. They prove local-to-global results
for strictly convex unitarily invariant norm distances on Hermitian
conjugacy or fixed-singular-value orbits, respectively. The prescribed-
projection transport fiber is a different domain; no reduction identifying
those feasible sets has been justified. Charbonnier itself is a nonhomogeneous
spectral penalty. This is a domain/hypothesis comparison, not proof of novelty
and not a shortcut to the missing local-to-global argument. The existing BLR
comparisons remain relevant, and historical originality remains provisional.

## Complete effective Charbonnier multiplicity families (25 October)

For `tau>0`, every finite complex equal-rank pair now has a complete
nonredundant multiplicity-product classification of **all ambient** global
Charbonnier optimizers. The new endpoints are
`smoothed_transport_isMin_iff_unique_normalized_phase_and_defect_complex`,
`exists_smoothed_multiplicity_parameter_equiv` and
`exists_smoothed_multiplicity_parameter_homeomorph`. They retain the actual
phase restrictions, both independent defect actions and the weighted
left-relative equation `C*T.adjoint*R`. The product consists of arbitrary
independent orthogonal projections on actual active canonical eigenspaces
and an independent arbitrary crossed-defect unitary. Zero, exactly critical,
repeated, fixed and right angles are included.

The optimizer set is compact. Each inverse rank coordinate is locally
constant; different rank sectors have fixed-pair positive operator-norm
separation, with no sharp or transition-uniform constant claimed. Simple
active multiplicities with zero right defect give exactly `2^s` isolated
optimizers, irrespective of inactive multiplicities. The manuscript states
`thm:smoothed-effective-coordinates`. Normalization and the inverse phase
Lipschitz estimate are in `SmoothedParameterNormalization`; the full product
and algebraic rank-stratification are in `SmoothedMultiplicityParameters`;
topology and rank separation are in `SmoothedParameterTopology`.

The effective support is proved for general `0<b<a`, from the exact phase
coefficient `2*i*c*sqrt(1-min(1,a*c/b)^2)`: only positive cosines below `b/a`
contribute. Charbonnier specializes to `a=eta`, `b=eta^-1`. The shared
normalization and recovery ingredients are classical. Their finite-effective-
space Hilbert generality is not an infinite-dimensional optimum theorem.
Projection carriers carry the topology; the subspace rank-stratification
is algebraic. Component counts, manifold dimensions, smoothed local-to-global,
real matching, ideal optimization and the nuclear limit `tau=0` remain outside
this compiled endpoint.

The [BLR primary paper](https://journals.uwyo.edu/index.php/ela/article/download/117/117/117)
was rechecked at Problem 1.1, Theorem 3.1 and Theorems 4.2/4.5. Problem 1.1
asks for all minimizers. Theorem 3.1 gives Q-norm optimality and an equality
criterion under its associate-norm hypothesis. Theorem 4.2 classifies
Frobenius minimizers; Theorem 4.5 adds a compatibility condition for a Q-norm
value theorem. These are exact precedents. Charbonnier's nonhomogeneous
objective is not a direct instance of those theorem statements. This
comparison does not establish first-publication priority. Historical novelty
of the complete nonlinear classification remains **provisional**, with no
independent novelty claim for projection products, rank stability or compactness.

## Operator norm homeomorphism and separated rank sectors (25 October)

The finite complex `1<p<2` classification now includes its actual
**operator norm topology**. In `SchattenParameterTopology.lean`,
`exists_schatten_normalized_parameter_homeomorph` upgrades the normalized
phase/defect equivalence, and
`exists_schatten_multiplicity_parameter_homeomorph` gives a homeomorphism
from independent projections on the actual active multiplicity spaces,
times arbitrary independent crossed-defect unitaries, onto **all** ambient
global optimizers. Equal subspace ranks and finite `1<p<2` are the
optimization hypotheses; there is no angle simplicity, acuteness or
preselected competitor frame. Actual phase restrictions and both defect
actions are retained. Zero, critical, repeated and right angles are included.

The latter theorem proves local constancy of every multiplicity-projection
rank and a fixed-pair `k>0` such that a different rank on any one factor
implies `1 <= k*||T-S||`. Hence the rank sectors are clopen and uniformly
separated for the fixed pair and exponent, and ranks are constant along
continuous connected families. The constant is not claimed sharp or
uniform near phase transitions. `isCompact_schattenTransportMinimizers`
proves compactness; the discrete-topology endpoint proves isolation in
the simple-active/no-right-defect case, where the exact count is `2^s`.
The manuscript includes `thm:schatten-optimizer-topology`.

The proof consumes the accepted Tau Ceti operator-norm topology on linear
isometry equivalences. New donor lemmas prove compactness of projection
and finite-dimensional isometric-identification spaces (including empty
and trivial cases), rectangular inversion continuity, the paired
restriction/extension homeomorphism, rank stability of idempotents at
norm distance less than one, and contraction under invariant restriction.
These are classical facts. The closed graph proof also uses the previously
compiled geometric uniqueness theorem without a feasibility hypothesis.
No additional historical-priority claim is made for these topological
consequences. The historical novelty of the nonlinear full optimizer
classification remains provisional under the theorem-level comparisons below.

**Remaining boundary:** the old rank-stratified subspace equivalence is
algebraic. The current homeomorphism uses orthogonal-projection carriers,
without defining a new topology on Mathlib's `Module.Grassmannian`.
Path connectedness of each rank sector, exact component counts and
manifold dimensions remain unproved in Lean. The anticipated components
and dimensions in the conventional draft are not promoted by this result.
Charbonnier's full multiplicity product, real matching and ideal
optimization retain their earlier proof obligations.

## Manuscript integration assessment: source `427169ce` (25 October)

The global finite complex Schatten `1<p<2` research story now comprises four
separate verified mathematical conclusions: (i) the exact all-ambient optimum
and sharp canonical cutoff, (ii) **all** optimizer classification including
nonacute defects, (iii) an algebraic multiplicity-space parametrization and
exact `2^s` counts for simple active angles with zero defect, and (iv) the
absence of nonglobal constrained local minima, also for nearest
subspace-preserving unitary corrections. These are compatible theorems with
different logical content; the paper should lead with the complete theory,
then prove the individual steps. A set-level factorization by complex
Grassmannians does not establish a homeomorphism, connected components or
smooth dimensions. A local-to-global theorem does not prove convergence of
any numerical algorithm. All real matching, field-gap and infinite-dimensional
ideal results remain outside the verified claim boundary.

The Charbonnier all-global-minimizer classification is also checked and can
be stated alongside the exact value, uniqueness and stability results. A
smoothed local-to-global result is not checked. Neither classification
should be labeled a first-discovery theorem on the basis of a negative
literature search; finite-dimensional matrix-nearness and constrained
unitary transport remain important precedents. The main paper now calls
out the complete new theory while preserving the 28-proved/1-refuted source
inventory and keeping the YWS material separate.

## Complete finite multiplicity coordinates and exact counts (25 October)

The finite complex `1<p<2` optimizer classification now has its full
algebraic multiplicity-space factorization. The compiled theorem
`exists_schatten_multiplicity_parameter_equiv` gives independent arbitrary
orthogonal projections on the **actual** positive canonical eigenspace at
each distinct supercritical interior angle, together with an independent
arbitrary unitary between right defects. The actual active angle set is
proved finite. Its paired eigenspace sum is proved equal to the phase-weight
kernel complement, so no prescribed-frame or simple-spectrum restriction
is imposed on ambient competitors.

`nonempty_schatten_rank_stratified_parameter_equiv` replaces every projection
factor by all subspaces stratified by their exact dimension. This is the
finite product of disjoint unions of complex Grassmannian **sets** predicted
by the draft. The new statement does not assert a homeomorphism, connected
components or smooth/manifold dimensions. The checked manuscript includes
`thm:schatten-multiplicity-parameters`.

The exact count
`natCard_schattenTransportMinimizers_of_simple_active_angles` is also compiled:
if there is no right defect and every active multiplicity is one, there
are exactly `2^s` global optimizers, where `s` counts distinct active angles.
Inactive multiplicities are unrestricted. Included as
`cor:schatten-simple-active-count`. This is completeness of the sign choices,
not merely an exhibited family. Projection/range correspondence, rank
stratification and the paired commutant construction are classical ingredients
with no independent novelty claim.

The focused search of Schatten/Grassmannian minimizers, ambient unitary
transport, nearest block-diagonal unitaries and the critical cosine formula
returned neighboring operator-geometry work. Primary statements checked:

- Andruchow (2015), [*Parametrizing projections with selfadjoint operators*](https://www.sciencedirect.com/science/article/pii/S0024379514006983), Proposition 2.1 and Proposition 3.1: existence/uniqueness for a Grassmannian exponential and injectivity of Davis' projection map with a left inverse; the paper also minimizes projection distance in an off-diagonal completion problem. These are explicit precedents for projection geometry and completion, with different variables and objective from full Schatten displacement minimization over transporters.
- Andruchow--Chiumiento--Di Iorio y Lucero (2012 preprint), [*The compatible Grassmannian*](https://arxiv.org/html/1208.6571v1), Theorem 6.3 and Corollary 7.3: Fredholm-index connected components and minimal-length local geodesics for restricted compatible Grassmannians. The curve-length functional differs from the ambient chordal objective `||I-W||_p`.
- Tahiri--Tumpach (2026 preprint), [*The Restricted Schatten-class Grassmannian as affine coadjoint orbit*](https://arxiv.org/html/2605.22512v1), Theorems 18--20: coadjoint-orbit and symplectic structures at `1<=p<=2`. These provide operator-ideal geometric precedents; those theorem statements do not state the angle-dependent ambient minimizer classification.

These comparisons do not establish first-publication priority. BLR's
theorems and the broader matrix-nearness comparison below remain relevant.
Historical priority of the complete nonlinear transport classification
stays **provisional**. Generic Grassmannian geometry and projection
parametrizations cannot themselves support a novelty claim.

## Nonredundant optimizer parameters and stability (25 October)

`SchattenParameterNormalization.lean` now proves the unique normalized
phase/defect classification and an algebraic parameter bijection for every
finite complex pair at `1<p<2`. The phase projection is supported on the
orthogonal complement of `ker(C*(F-F.adjoint))`; its actual angle coefficient
is `2*i*cos(theta)*sin(optimalPhase(p,theta))`. The coefficient vanishes
precisely on inactive interior, fixed and right-angle directions. Right
defects are still parametrized independently by an arbitrary unitary.

The endpoints are
`schatten_transport_isMin_iff_unique_normalized_phase_and_defect_complex`
and `exists_schatten_normalized_parameter_equiv`. The latter includes a
uniform operator-norm Lipschitz estimate recovering the phase projection
from the optimizer for a fixed pair and exponent. No sharp recovery
constant or uniformity through a phase transition is claimed. The
manuscript includes `thm:schatten-normalized-parameters`.

This closes redundancy and injectivity in the operator parameters. The
multiplicity-space and rank-stratum factorization is now compiled above;
Grassmannian homeomorphism, connected components and dimensions remain
unverified. The normalization and norm
recovery are classical consequences of the new complete classification;
they carry no separate historical-priority claim. The historical priority
of the full nonlinear Schatten classification remains provisional under
the theorem-level comparisons below.

The local extension ingredient has also been strengthened to
`exists_unique_paired_projection_extension`: arbitrary projection data on a
finite-dimensional subspace orthogonal to its reflection determine a unique
compatible projection supported on the paired sum, even in an infinite
ambient Hilbert space. This replaces the weaker existence-only declaration.
It advances multiplicity-space coordinate assembly and carries no separate
historical novelty or ideal-optimization claim.

## Complete all-angle complex Schatten optimizer classification (25 October)

The full unrestricted finite complex `1<p<2` optimizer **iff** is now
compiled as
`SchattenNonacuteClassification.schatten_transport_isMin_iff_phase_and_defect_complex`.
Every global optimizer has compatible phase-projection and arbitrary
reflecting crossed-defect data, and every compatible projection/defect pair
occurs jointly in a unique global optimizer with those prescribed actions.
Zero, repeated, critical and right angles and fixed ambient directions are
included. No prescribed-block or cosine-preserving competitor hypothesis
is imposed. The named canonical completion is fixed; the optimizing defect
unitary is independent and arbitrary.

The necessary intrinsic witness is the positive spectral projection of
`Im(C*R.adjoint*T)`. `SchattenPhaseDefectAttainment.lean` supplies joint
attainment and uniqueness; `SchattenProjectionAttainment.lean` first realizes
any compatible projection in its own derived paired frame. The spectral
phase factor has the actual optimal scalar phases and actions `F(1)=1`,
`F(0)=i`. The manuscript includes
`thm:schatten-all-phase-defect-minimizers`. The earlier necessary-only and
arbitrary-projection-attainment boundaries are now closed.

The algebraic Grassmannian-set product/bijection is now compiled above;
component dimensions and topological assertions are **not** separate Lean endpoints. Inactive and
right-angle projection parameters may be redundant. The exact generic
operator-distance identity is compiled for full relative-phase
representations and included as `cor:schatten-phase-parameter-distance`;
it is classical norm invariance plus affine algebra, with no separate
historical novelty claim. Real matching and ideal-theoretic optimality
remain open.

The complete classification also transfers to **every** Schatten-nearest
unitary preserving a prescribed subspace, via the compiled
`schatten_correction_isMin_iff_phase_and_defect_complex`. For prescribed
unitary `A`, the bijection `V -> V*A.adjoint` identifies corrections
preserving `K` with transport from `A(K)` to `K`, preserving literal
Schatten distance. The manuscript includes
`cor:schatten-all-nearest-commuting`. This supplies a concrete matrix
nearness consequence of the new classification. The reduction itself is
classical; its utility does not establish historical priority for the
underlying classification or any experimental performance claim.

The new priority-search pass queried the critical cosine formula,
Schatten principal-angle minimizer classification, Grassmannian phase
parameters, minimal-distortion citation terms, nearest block-diagonal
unitaries and Schatten Procrustes. It returned the BLR
paper and unrelated Schatten problems, with no theorem-level matching full
`1<p<2` classification. This is limited negative-search evidence. BLR's
[official journal paper](https://journals.uwyo.edu/index.php/ela/article/download/117/117/117)
already poses the exact general transport problem; its planar right-angle
`p<2` result (Lemma 3.3), Frobenius minimizer classifications
(Theorems 3.4 and 4.2) and Q-norm theorem (Theorem 3.1) remain explicit
precedents, rechecked in the journal PDF. The all-angle nonlinear phase classification is the
current candidate contribution, but first-publication priority remains
**provisional** pending the wider matrix-nearness/quotient-metric comparison.

## Intrinsic angle-space parameters, including nonacute ambient pairs

The necessary phase parameter is now compiled in intrinsic coordinates:
for every finite complex `1<p<2` ambient local/global optimizer, every
`0<theta<pi/2` and every canonical defect completion, its actual relative
unitary on `ker(|P-Q|-sin(theta)*I)` has scalar real part
`cos(optimalPhase(p,theta))*I`. Above the cutoff it determines a **unique
orthogonal projection commuting with the actual restricted canonical
rotation and source reflection**. No acuteness hypothesis is imposed on
other angles; zero, repeated, critical and right angles elsewhere are
included. At and below the cutoff every optimizer agrees with canonical
rotation on that individual angle space, even if other angles exceed it.

Evidence: `SchattenEqualAnglePhases.lean` and
`SchattenEqualAngleCompatibility.lean`, in particular
`relative_phase_unique_compatible_projection_on_angle_of_isLocalMinOn_complex`
and `apply_eq_canonical_on_angle_le_critical_of_isLocalMinOn_complex`.
Included as Proposition `prop:schatten-intrinsic-angle-parameter`.

The proof isolates the actual gradient-kernel obstruction:
`gradient_kernel_sinAngleOperator_isStarProjection_of_isLocalMinOn_complex`
holds for every finite complex `p>1`. Its restricted sine eigenvalues are
zero or one, excluding that kernel from every interior angle space. This
uses the already verified fixed/right kernel blocks rather than a Hessian
at vanishing displacement. The generic supporting projection and symmetric-
orthogonality facts are classical; the scalar-real-part two-phase spectral
projection itself is classical as well. No separate novelty claim is made
for these algebraic ingredients.

The next unresolved claim is **attainment of every compatible phase
projection**, then the full nonacute ambient phase/defect iff and its
Grassmannian parameter bijection/topology. Independent signed scalar
attainment does not yet prove that every prescribed multiplicity projection
occurs. These boundaries remain explicit in `PAPER_CONTEXT.md`.

Primary sources rechecked: [BLR (2001), Problem 1.1 and its matrix formulation](https://journals.uwyo.edu/index.php/ela/article/download/117/117/117)
already asks for the entire minimizer set; and
[local Lidskii (2018), Section 1 and Theorems 3.5/3.12](https://arxiv.org/html/1806.11436)
classifies minimizers for fixed spectral or singular-value matrix orbits.
Those orbit constraints differ from prescribed subspace transport. The
current angle-dependent necessary parameter theorem is not licensed as
historically new by that domain distinction alone. Priority of the full
transport classification remains **provisional** pending theorem-level
comparison across the broader nearness literature.

## Exact pure Schatten uniqueness and its commutator consequence

The unrestricted finite complex `1<p<2` theory now includes the **exact
uniqueness criterion**: a unique global transporter exists iff every
principal angle is at most `arccos((2-p)/p)`. Every local minimum then
equals canonical rotation, including at critical equality, with repeated
and zero angles and in dimension zero. Above the bound, two independently
constructed opposite-phase ambient optimizers are distinct. Right angles
are included in this nonuniqueness conclusion. Evidence:
`SchattenCanonicalUniqueness.lean` and
`SchattenSignedOptimizers.lean`, especially
`schatten_transport_unique_minimizer_iff_complex`.
The included manuscript states `cor:schatten-unique-minimum`.

A common frame derived from the actual subspace pair now realizes **every
independent attaining signed phase choice**, with exact global cost and
comparison against all ambient unitaries. This is a converse construction
for scalar signs; it does not yet establish the intrinsic full
Grassmannian parameter iff or classify every optimizer in one fixed frame.

The useful application is also compiled: the nearest subspace-preserving
unitary to any prescribed unitary `A` is unique iff
`||AP-PA|| <= 2*sqrt(p-1)/p`, with equality. The proof transfers all
competitors by `C -> C*A.adjoint`; it does not impose a common principal
plane decomposition on competitors. Evidence:
`SchattenCommutatorCutoff.schatten_correction_unique_minimizer_iff_commutator_complex`;
included `cor:schatten-commutator-uniqueness`. This is a sharp mathematical
certificate, with no numerical-performance or implementability claim.

Primary comparison rechecked: BLR (2001),
[official journal PDF](https://journals.uwyo.edu/index.php/ela/article/download/117/117/117),
Lemma 3.3 (printed p. 36), already gives the planar right-angle
`1<=p<2` optimizing relation. Theorem 3.4 gives all Frobenius minimizers
for its block-diagonal nearness problem. Those statements are not an
angle-dependent all-rank `1<p<2` uniqueness criterion. This comparison
identifies a theorem-level scope difference; it is not a proof of
historical priority. The complete transport result's novelty remains
**provisional**, pending the broader matrix-nearness and quotient-metric
citation investigation recorded below. The gap and commutator identities
are classical and have no independent novelty claim.

## Named canonical relative phases and acute commutation

The signed phases are now identified relative to the **actual named canonical
rotation**. `positive_gradient_canonical_relative_phase_basis_of_isLocalMinOn_complex`
retains its geometric phases `+/-theta_i` and the actual relative phase
`R^*U`, with the same scalar `exp(i*eps_i*optimalPhase(p,theta_i))` on
both reflection-paired vectors. This is compiled for every finite complex
ambient local minimum at `1<p<2`, every completion on the right defect,
all multiplicities and critical angles. The checked signed-phase
proposition includes these canonical and relative actions.

`commute_canonicalRotation_of_isLocalMinOn_acute_transports_complex`
also proves whole-space commutation for **every acute optimizer**, including
zero/critical/repeated angles and an empty ambient space. It uses the
actual paired basis and proves identity for both operators on the actual
gradient kernel. The checked manuscript includes Corollary
`cor:schatten-acute-canonical-commutation`.

The geometric bridge is dimension-free: for any feasible paired phase
eigenvector of nonnegative acute mean, the canonical intertwiner has
coefficient `cos(theta)*exp(i*theta)`, its positive modulus has coefficient
`cos(theta)`, and `R*C=intertwiner` gives the canonical eigenvalue. A supplied
defect isometry remains an explicit hypothesis; no infinite ideal or
index-balance claim follows. These are classical polar/projection identities
with no independent novelty claim.

The intrinsic scalar-real-part/projection parameter theorem and converse
attainment are still pending. The now-proved canonical relative basis
removes the prior canonical-action obstruction. Historical priority of the
complete angle-dependent optimizer classification remains **provisional**.

## Signed optimal phases on every actual positive-gradient space

The positive acute phase structure is now a compiled **every-optimizer**
statement. `positive_gradient_optimal_phase_basis_of_isLocalMinOn_complex`,
in `SchattenOptimizerPhases.lean`, constructs a complete basis of the actual
positive-gradient space, physical angles `theta_i` and signs `eps_i=+/-1`
with transporter eigenphases
`theta_i+eps_i*optimalPhase(p,theta_i)` and
`-theta_i+eps_i*optimalPhase(p,theta_i)` on the source-reflection-paired
vectors. The actual sine eigenvalue of both vectors is `sin(theta_i)`.
This holds for every finite complex ambient local minimum at `1<p<2`,
including critical and repeated angles, empty positive spaces and arbitrary
zero/right-angle sectors elsewhere. Proposition
`prop:schatten-all-signed-phases` is included in the checked manuscript.

The phase decomposition now retains `alpha_i,beta_i in (0,pi)`, needed
before applying the scalar uniqueness theorem to half the absolute phase
difference. `SchattenOptimalPhase.lean` supplies the named optimal phase,
its exact cutoff and the two-way scalar phase-pair classification. These
are packaging and consequences of the already proved scalar diagram;
no separate historical novelty is claimed for naming the phase or
retaining the branch bounds.

The newer entry above identifies canonical rotation on these same paired
eigenvectors. The intrinsic operator parameter theorem still must assemble the
relative phase on each geometric equal-angle multiplicity space, and prove
attainment of every compatible projection parameter. The right-defect
parameter and arbitrary attaining replacements are already compiled.
Historical priority of the complete angle-dependent optimizer
classification remains **provisional**.

## Complete pure Schatten right-defect parameter and independence

The right-angle part of the **every-optimizer** theorem is now compiled
for finite complex `1<p<2`, including arbitrary positive/zero angles and
multiplicities elsewhere. `SchattenRightDefect.lean` proves that the whole
sine-one space lies in the actual gradient kernel, hence is a reflecting
restriction. Each ambient local minimum therefore determines exactly one
unitary identification `D` between the actual crossed defects and acts by
`D.symm` on the other defect.

`SchattenDefectReplacement.lean` proves the converse independently of
all complementary optimizer choices: every prescribed `D` gives exactly
one globally optimal ambient transporter with any given local optimizer's
whole complementary action. Its exact principal-angle value and comparison
with all ambient competitors are conclusions. This proves necessity,
attainment and independence of the right-defect parameter. The positive
acute equal-angle phase parameter and its converse assembly remain open.
Proposition `prop:schatten-all-right-defects` is in the checked manuscript.

The supporting cost split is real/complex and holds for every finite
`p>=1` under explicit feasibility, cosine commutation and reflecting-kernel
hypotheses. The right-angle power is `2^(p-1)*dim(N)`; it does not depend
on `D`. A shared geometric extension now supplies both the pure Schatten
and the existing Charbonnier attainment theorem.

The primary comparison rechecked for this step is BLR (2001),
[official journal PDF, Lemma 3.3, printed p. 36](https://journals.uwyo.edu/index.php/ela/article/download/117/117/117).
It already identifies the planar right-angle Schatten optimizer relation
for `1<=p<2`. Their Theorem 4.2 classifies all Frobenius optimizers.
No separate historical novelty is claimed for the right-angle mechanism,
block reflection geometry, orthogonality argument or cost additivity.
The present compiled statement applies the exact defect parameter inside
every ambient constrained optimizer and constructs arbitrary replacements.
Historical priority of the full angle-dependent transport theory remains
**provisional**; this comparison provides no general historical clearance.

## Pure Schatten unequal-angle separation and fixed directions

Two further every-optimizer conclusions are now Lean-verified, including
all degenerate angles and multiplicities at arbitrary finite complex rank
for `1<p<2`:

1. Every constrained local minimum commutes with `|P-Q|` and maps every
   eigenspace of that operator onto itself. Since sine is injective on
   `[0,pi/2]`, this excludes mixing between unequal principal angles,
   including the zero- and right-angle sectors.
2. Every such local minimum fixes every vector `x` for which `P*x=Q*x`.
   This fixes the entire common source and common orthogonal ambient
   space, without assuming the remaining pair is acute.

The endpoints are in `SchattenOptimizerAngles.lean` and
`SchattenFixedDirections.lean`, registered with exact names in
`claims_to_evidence.md`. They apply to every global optimizer because a
global minimum is local. Proposition `prop:schatten-angle-preservation`
is included in the checked manuscript.

The nonzero-gradient basis already consists of paired common eigenvectors
of the unitary and intrinsic sine operator. The missing kernel argument
is now a reusable classical theorem: any reflecting transporter commutes
with the modulus of its projection difference, because conjugation
negates that difference. This reflection lemma even holds on arbitrary
real/complex complete Hilbert spaces. A finite-dimensional restriction
identity then assembles the actual ambient commutation. Angle preservation
makes the zero-angle space reducing; its inherited local minimum has
coincident source/target and exact cost zero, forcing identity there.

These are compiled components of a complete pure Schatten optimizer
classification. The newer entry above closes the right-defect intertwiner
and its arbitrary attaining replacement. The acute equal-angle phase
equation, its converse attainment and parameter topology remain open. The classical algebra
and restriction lemmas carry no originality claim. The closest identified
BLR and Local Lidskii comparisons below still leave historical priority
of the constrained Schatten classification **provisional**.

## Full finite complex Schatten local-to-global theorem

The unrestricted finite complex landscape theorem is now **Lean-verified**
for `1<p<2`: every local minimum over all unitaries transporting `K` to
`L` attains the exact scalar principal-angle sum and is globally optimal.
The norm and its `p`th power both have this property. This includes zero,
right, critical and repeated principal angles, eigenvalues `1,-1`, fixed
ambient directions and empty gradient kernels, at arbitrary finite rank.
The exact endpoints are
`schatten_transport_cost_eq_sum_of_isLocalMinOn_complex`,
`isMinOn_of_isLocalMinOn_transports_complex` and
`isMinOn_schatten_of_isLocalMinOn_transports_complex`, in
`SchattenLocalGlobal.lean`. The checked manuscript includes Theorem
`prop:schatten-local-is-global`.

The final obstruction was numerical kernel optimality. The complete
fixed/right family makes the kernel reflection's source-diagonal
compression an orthogonal projection. A classical positive-compression
trace certificate proves Frobenius optimality over the full transport
fiber. The bounded-singular-value inequality
`2^(p-2)*||I-W||_F^2 <= ||I-W||_p^p`, with equality for reflections,
then proves kernel Schatten optimality. The existing attained global
value and cost-deficit identity yield the ambient theorem. These
ingredients now compile in `SchattenFrobenius.lean`,
`Projection/FixedRightCompression.lean` and
`UnitaryTransportFrobenius.lean`. No independent originality is claimed
for the pointwise power inequality, projection algebra or Procrustes
trace certificate.

The continuous cost-preserving bijection `V -> V*A^*` also gives a
compiled consequence: **every local Schatten-nearest unitary preserving
a specified subspace is globally nearest**, with arbitrary input unitary
`A`, in finite complex dimension and `1<p<2`.
`SchattenCorrectionLocalGlobal.lean` proves the norm and power versions;
Corollary `cor:schatten-correction-local-global` is included. This
mathematical landscape result supplies no algorithmic convergence or
experimental-performance guarantee.

### Theorem-level historical comparison

Primary sources rechecked for this step:

- Bolotnikov--Li--Rodman (2001),
  [official journal PDF](https://journals.uwyo.edu/index.php/ela/article/download/117/117/117):
  Problem 1.1 includes this transport feasible set; Lemma 3.3 treats the
  right-angle Schatten case `1<=p<2`, including its attaining phases;
  Theorems 3.4 and 4.2 treat Frobenius optimization and its full optimizer
  family; Theorem 4.5 treats a Q-norm under additional block structure.
  The statements inspected do not assert the present `1<p<2` constrained
  local-to-global theorem.
- Massey--Rios--Stojanoff (2018),
  [Local Lidskii, Theorems 3.5 and 3.12](https://arxiv.org/html/1806.11436):
  local minima are global for strictly convex unitary-invariant norm
  distances on a fixed-eigenvalue Hermitian orbit or fixed-singular-value
  matrix orbit, with joint spectral or singular-value structure. Those
  orbits differ from the prescribed-projection transport fiber. An
  implication for our result requires a further reduction; none is
  justified by the theorem statements alone.

Targeted searches combining Schatten, subspace transport, local minima,
minimal distortion and block-diagonal unitary approximation found no
additional theorem-level precedent that settles this priority question.
This is limited negative search evidence. **Historical originality remains
provisional.** The mathematically stronger result and its formal proof
can be stated without a priority claim.

### Scope retained for the next theorem

The full pure Schatten operator parameterization is still conventional:
assemble the actual paired-gradient basis into geometric equal-angle
spaces (unequal-angle reduction and zero-angle rigidity now compile), identify the two supercritical
phases with an orthogonal-projection parameter, and classify the full
right-defect intertwiner. The current theorem also supplies no real
matching formula, smoothed local-to-global result, or operator-ideal
feasibility/convergence/attainment theorem. Earlier dated snapshots below
retain their original frontiers; the current result supersedes their
local-to-global obstruction.

## Complete reflecting-kernel geometry after `276828432`

The normal-form obstruction recorded in the preceding iteration is now
closed. `PlanarReflection.exists_source_reflection_coordinates` constructs
unitary coordinates from the actual nonconstant source projection and
nonscalar self-adjoint planar unitary. The diagonal gauge fixes the
source, allows a zero off-diagonal coefficient, and produces real `d,k`
with `d^2+k^2=1`, `k>=0`. Mathlib supplies the ordered symmetric eigenbasis;
the matrix proof identifies the two scalar involutions separately.

`SchattenReflectingPlanes.lean` now proves the intrinsic alternative:
for every finite complex ambient local Schatten minimum with `p>1`,
every common invariant complex plane on which the transporter is an
involution is fixed pointwise or exchanges the source and complementary
sectors. The ambient endpoint
`fixes_or_exchanges_source_complement_on_invariant_plane_of_isLocalMinOn_complex`
assumes no prescribed coordinates, restricted operators or orthogonal
extension. Other ambient eigenvalues are unrestricted. Zero/full source
restrictions and the scalar involutions are included. The commuting-block
fixed-space theorem holds in every finite dimension for `p>=1`, with
only self-adjointness required of the source operator. Proposition
`prop:schatten-intrinsic-reflecting-plane` is in the checked manuscript.

The extension through **every small block** and the complete actual
gradient kernel also compiles. The dimension-one step uses the cyclic
generator theorem to prove `ContinuousLinearMap.commute_of_finrank_le_one`
over arbitrary real/complex normed spaces. The small-block alternative
forces every nonfixed block to have dimension two. The full theorem
`gradient_kernel_fixed_or_right_blocks_of_isLocalMinOn_transports_complex`
then constructs a complete orthogonal family on the actual zero-gradient
kernel of every ambient local minimum, for arbitrary rank and finite
complex `p>1`. It derives the restricted unitary, actual source projection
and negative-phase projection; no supplied block model or spectral gap
is assumed. Corollary `cor:schatten-kernel-fixed-right` is included.

This is a necessary local-minimum classification for reflecting planes.
It is not a sufficiency assertion for all `p>1`; for `p>2` the right-angle
reflection can have larger cost than canonical rotation. At that snapshot the unrestricted
`1<p<2` no-spurious-local-minima theorem still needed the numerical
angle/cost assembly. The current entry above closes that obstruction
through the Frobenius certificate. `PAPER_CONTEXT.md`
records the precise remaining declarations. No pure Schatten all-optimizer,
real matching or operator-ideal claim has been promoted by this step.

The two-projection normal form, source basis, diagonal phase gauge and
restriction of unitary operators are classical ingredients with no
independent priority claim. A targeted search again returned Halmos,
*Two subspaces* (1969),
[publisher DOI](https://doi.org/10.1090/S0002-9947-1969-0251519-5), and the
existing BLR (2001) unitary-nearness work. The publisher's Halmos PDF was
inaccessible on this pass (HTTP 403), so this pass supplies no new
theorem-level historical clearance. The previously checked BLR and Local
Lidskii comparisons below remain applicable. Historical originality of
the broader constrained transport results remains **provisional**.

## Reflecting-block descent after `5c2ca4ad2`

The singular-gradient descent calculation now has a Lean proof. For
`S=[[-d,-k],[-k,d]]`, `d^2+k^2=1`, right multiplication by
`diag(exp(i*(d+1)*t/2),exp(i*(d-1)*t/2))` preserves transport of
`diag(1,0)`. For every finite Schatten exponent `p>1`, its actual
displacement power is
`2^p - p*2^p*d^2*t^2/8 + o(t^2)`.
`reflectingPhasePower_second_order`,
`ReflectingVariation.schatten_displacement_variation`, and
`reflecting_block_eq_zero_of_isLocalMinOn_transports_complex`
formalize the expansion, its spectral identification, and its exclusion
inside an unrestricted ambient local minimum whenever `d!=0`.
The endpoint parameters `d=+1,-1` are included. A nonzero negative
identity block is also excluded for all finite `p>=1`, including the
nuclear endpoint; the actual-subspace version constructs the orthogonal
block representation rather than assuming it. This also proves a stronger
local-to-global endpoint for `1<p<2`: a local minimum is global if its
actual negative eigenspace is source-invariant, since local minimality
then excludes that eigenspace. The theorem is
`isMinOn_of_isLocalMinOn_transports_of_negative_eigenspace_invariant_complex`.
Proposition `prop:schatten-reflecting-descent` and the strengthened
`prop:schatten-local-global-no-minus-one` are included in the checked
manuscript.

The phase has a second-order Peano bound with zero constant and linear
terms, which makes its small-displacement cost `o(t^2)` for `p>1`.
The proof consequently avoids an unjustified second derivative at a
vanishing displacement singular value. The previously diagnosed cubic
coefficient remains conventional, since the weaker compiled estimate is
sufficient. No independent originality is claimed for Taylor expansion,
trace/determinant reconstruction, or orthogonal block restriction.

This closed an analytic step toward the pure Schatten no-spurious-minima
theorem. The newer entry above also closes the actual planar normal form.
A common two-projection decomposition exists in Lean; assembling its
fixed/right blocks and the kernel cost-deficit identity remains necessary.
`PAPER_CONTEXT.md` gives the
precise resumption point. The real matching and infinite ideal claims
have not been promoted.

A primary local-to-global precedent was rechecked:
Massey, Rios and Stojanoff, *Local Lidskii's theorems for unitarily
invariant norms* (2018),
[Theorems 3.5 and 3.12](https://arxiv.org/html/1806.11436).
Theorem 3.5 treats distance from a fixed self-adjoint matrix on a fixed
eigenvalue unitary orbit. Theorem 3.12 treats distance from a fixed matrix
on a fixed singular-value orbit; both assume a strictly convex unitarily
invariant norm and prove local minima global, with joint spectral data.
Our assessment is that applying them to the prescribed-projection
transport fiber would require a further reduction not supplied by their
statements. This comparison does not establish historical novelty.
BLR's right-angle and Frobenius precedents below remain applicable.
The overall transport classification's historical priority remains
**provisional**.

## Complete finite Charbonnier optimizer set after `f51c60f13`

The full all-angle ambient classification now compiles in
`SmoothedNonacuteClassification.lean`. For every finite complex equal-rank
pair and `tau>0`, a feasible `T` is globally minimizing iff it has a
compatible orthogonal phase projection modulo the cosine kernel and is
self-adjoint on that kernel. The intrinsic projection is
`1_(0,infinity)(Im(C T.adjoint R))`; it commutes with actual `R,J` and
vanishes on `ker C`. Cosine commutation is a consequence, with no extra
assumption on the candidate. The typed version replaces kernel
self-adjointness by a unique crossed-defect unitary paired with its inverse.

`SmoothedPhaseDefectAttainment.lean` also proves that **every** compatible
phase projection and **every** crossed-defect unitary jointly determine
exactly one attaining ambient transporter, with the exact global value and
comparison against every feasible unitary. The weighted statements assume
`0<b<a`. The literal statements assume `tau>0`. This closes the single
nonacute iff and independent mixed parameter assembly that the preceding
entries left open. `SmoothedCorrectionClassification.lean` transfers the
criterion to all nearest subspace-preserving unitaries without a commutator
norm restriction. The included manuscript now states
`thm:smoothed-all-projections-defects` and this correction consequence.

This is a full **optimizer-set** result; phase parameters can remain
redundant on inactive directions. General product topology, normalized
parameter homeomorphisms, and manifold dimensions are not formal endpoints.
Neither all-local-minima-global nor the pure Schatten, real matching or
operator-ideal classifications follows from these declarations.
The uniqueness of a transporter with prescribed phase/defect data itself
holds on arbitrary complex Hilbert spaces with orthogonally projected
subspaces; its existence and cost-optimality conclusions remain finite.

BLR (2001), [Lemma 3.3 and Theorem 4.2](https://journals.uwyo.edu/index.php/ela/article/download/117/117/117),
remain direct precedents for the right-angle scalar Schatten mechanism and
complete Frobenius optimizer classification. The new statement concerns
the complete arbitrary-angle weighted/Charbonnier family. The classical
spectral-selection, defect geometry, cancellation and orthogonal extension
ingredients carry no independent novelty claim. A further targeted search
for block diagonal unitary trace-norm approximation and Charbonnier
transport produced no additional theorem-level implication; that negative
search evidence is limited. Historical originality is **provisional**,
including for the all-nearest commuting-unitary application.

The next pure Schatten obstruction recorded at that snapshot was the
reflecting two-plane descent calculation. Its sufficient second-order
estimate is now formalized in the newer entry above. Its stronger cubic
phase coefficient remains a symbolic diagnostic. The unrestricted
local-to-global theorem still needs the geometric block extraction.

## Arbitrary mixed right-angle families after `c16d48091`

The previously missing mixed right-angle converse now compiles in
`SmoothedDefectReplacement.lean`. Every finite complex weighted/Charbonnier
optimizer determines one unique unitary identification of the actual
crossed defects, acting by its inverse on the other defect. Every such
identification can replace that of any given global optimizer while
preserving all its positive-cosine action. The resulting ambient transporter
is constructed and compared with every admissible unitary. Thus no positive
angle, multiplicity, or preselected defect-pairing restriction is introduced.

`KernelCostSplitting.lean` proves the actual weighted cost split for real
or complex cosine-preserving feasible transporters self-adjoint on the
cosine kernel, without assuming optimality. The literal Charbonnier split
and the independent replacement are included as Proposition
`prop:smoothed-arbitrary-defects`. `SmoothedNonacutePhases.lean` proves
`[C*(T*R),R]=0` globally for every optimizer. Replacing this by unweighted
relative commutation would exclude actual right-angle minimizers.

The full ambient phase-plus-defect iff still needs the intrinsic
positive-phase projection modulo the kernel. The precise candidate and
remaining sufficiency argument are in `PAPER_CONTEXT.md`. General product
topology, pure Schatten all-minimizer classification, real matching, and
operator-ideal optimization remain outside the new compiled scope.

The primary [BLR paper](https://journals.uwyo.edu/index.php/ela/article/download/117/117/117)
was rechecked at Lemma 3.3, printed p. 36: it gives the exact right-angle
scalar Schatten minimum `2^p` and all attaining scalar pairs for
`1<=p<2`. Theorem 4.2, pp. 39--40, gives the complete Frobenius optimizer
family. These are direct precedents for the scalar mechanism and
optimizer-family question. The new finite Charbonnier theorem concerns
arbitrary multiplicity mixed with other angles and independent replacement
under its own objective. Classical defect geometry, self-adjoint extension,
and orthogonal-block cost additivity receive no separate originality claim.
No exhaustive historical-priority clearance is asserted.

## Complete acute Charbonnier classification after `9693e8946`

The acute all-optimizer theorem is now compiled, including arbitrary
multiplicities, subcritical and critical angles, zero angles, and fixed
ambient directions. Every global minimizer has
`T*R=U E+U* (I-E)` for an orthogonal projection commuting with the actual
canonical rotation and source reflection, and every such projection is
attaining. An intrinsic witness is `1_(0,infinity)(Im(T*R))`.
`SmoothedAcuteClassification.lean` proves the weighted `0<b<a` criterion
and literal `tau>0` endpoints, both for injective actual cosine and for
the concrete projection-gap hypothesis below one.

For the **whole ambient isoclinic** case `C=c I`, `0<c<eta^(-2)`,
`SmoothedIsoclinicFamilies.lean` gives all minimizers bijectively and
proves `||T(E)-T(F)||=2*sqrt(1-eta^4*c^2)*||E-F||`. This improves the
previous one-factor lower distance bound to an exact metric statement
under its stronger hypothesis. The bijection and norm identity imply
continuity in both directions; no Grassmannian manifold formalization
or general mixed-angle topological classification is claimed.
`SmoothedCorrectionClassification.lean` transfers the full acute family
to all closest prescribed-subspace-preserving unitaries when the input
commutator defect is below one. These compiled results are included in
the checked manuscript. The actual right-angle kernel is now identified with the crossed-defect
sum, and every Charbonnier optimizer is self-adjoint and anticommutes
with source reflection there (`CosineKernel.lean`, `SmoothedRightDefect.lean`).
These classical geometric reductions do not prove the arbitrary mixed
defect converse. Mixed right-angle assembly, the pure Schatten full
classification, unrestricted real matching, and ideal extensions remain
unproved at their proposed scope.

The classical joint eigenbasis, spectral projection, and relative-unitary
norm algebra are not separate originality claims. A further exact
precedent is Contino, Giribet, Maestripieri, *Weighted Procrustes problems*,
JMAA 445(1), 443--458 (2017),
[DOI](https://doi.org/10.1016/j.jmaa.2016.07.050),
[primary preprint](https://arxiv.org/pdf/1610.00558).
Theorems 3.5 (`B=I`) and 4.5 (general `B`) characterize minimizers of
`||W^(1/2)(AX-B)||_p` over **all bounded operators X**, under closed-range,
ideal, and weighted range-compatibility hypotheses. They give weighted
inverses and a shorted-operator value. Their feasible set and operator
weight differ from the unitary transport fiber and scalar weighted nuclear
problem here. This comparison rules out a direct identification of those
statements with our classification; it does not establish that no other
precedent subsumes it. The earlier BLR Frobenius and Q-norm comparisons
remain applicable. Historical novelty remains provisional.

Earlier entries below record their dated proof frontiers; the current
acute classification supersedes their unresolved acute assembly statements.

## Arbitrary projection attainment after `2524482e5`

The new compiled converse permits an arbitrary orthogonal projection on one
actual acute supercritical rotation multiplicity space. Its reflected ambient
extension yields a global optimizer over all ambient complex transporters,
with other angles unrestricted. `SmoothedMultiplicityAttainment.lean` supplies
weighted nuclear and literal Charbonnier endpoints. The set of all these
projections injects into the ambient Charbonnier minimizers, with quantitative
separation `2*sin(delta)*||Q-Q'||_op <= ||T(Q)-T(Q')||_op`.

`SmoothedProjectionOptimizers.lean` also proves the global formula
`T*R=U P+U* (I-P)` is attaining for **any** ambient orthogonal `P` commuting
with the canonical rotation and source reflection. This is sufficient
without a supplied diagonal frame. The earlier necessary matching phase
projections and this converse establish exactly which projections can occur
on any one acute multiplicity space.

The full acute iff theorem still needs to assemble the necessary projections
of every optimizer into one compatible ambient projection. Global commutation
with `R` is now compiled under injectivity of the actual cosine, providing
the next reduction. Mixed right-defect assembly, topology, and dimensions
remain incomplete. No continuity of the chosen projection-to-minimizer
assignment is claimed from a set-theoretic injection or a lower norm bound.
Proposition `prop:smoothed-projection-attainment` includes the proved results.

Joint eigenbases, reflected projection extension, and the affine separation
lemma are classical ingredients. The possible originality remains attached
to the constrained transport classification and its penalty-dependent
consequences. Targeted searches for the block-diagonal-unitary trace-norm
problem and Charbonnier transport returned no implication proving this
classification; negative search evidence does not certify priority.

## Paired-phase and complementary-right update after `51f21951d`

Every finite complex weighted optimizer now has a unique projection parameter
on each **one-sided rotation multiplicity space**, and source reflection forces
the reflected parameter on the opposite rotation space. This is compiled in
`SmoothedOptimizerPairedPhases.lean` for `0<b<a`; the literal Charbonnier
endpoint assumes `tau>0` and global optimality over all ambient transports.
There is no distinct-angle mixing or free second multiplicity parameter.

`SmoothedSignedOptimizers.lean` constructs attaining ambient transports for
all independent phase-sign choices in a frame derived from the pair. In the
complementary right-angle problem, `SmoothedRightDefect.lean` proves the full
ambient iff criterion: a feasible transporter is minimizing exactly when
self-adjoint. The weighted value is `a*dim(E)` and the Charbonnier value is
`dim(E)*(sqrt(tau^2+4)-tau)/2`. These results are included in
`prop:smoothed-matching-phases` and `cor:smoothed-complementary-right`.

The mixed-angle arbitrary-projection converse, arbitrary right-defect product
assembly, and the topology/dimension assertions still need Lean proofs.
The complete optimizer family is therefore not yet claimed formally.
The classical eigenvector pairing and affine trace computation receive no
separate originality claim. A fresh search again located BLR Theorem 4.2
(all Frobenius minimizers), with its different objective; it did not supply a
weighted or Charbonnier classification. This is no exhaustive priority claim.
The [author's BLR PDF](https://cklixx.people.wm.edu/vlad.pdf) supports this
objective-level comparison; see the exact precedents below.

The numerical repeated-angle and arbitrary-right-isometry checks recorded in
`PAPER_CONTEXT.md` agree with the candidate converse families. They supply
no independent proof of sufficiency or topology.

## Spectral-separation update after `15ae65745` (24 October 2026)

The ambient equality certificate now proves that **every** finite complex
Charbonnier global minimizer preserves the principal-cosine eigenspaces.
Its relative unitary has scalar real part `min(1,eta^2*c)` on each positive
cosine eigenspace, preserves the two opposite canonical rotation phases
there, and the original transporter is self-adjoint on the right-angle
defect space. These are compiled in `SmoothedOptimizerNoMixing.lean` and
included as Proposition `prop:smoothed-optimizer-separation`.

`SmoothedOptimizerPhases.lean` also constructs the actual restriction and
its unique two-phase orthogonal projection on every positive supercritical
cosine block. This is a necessary normal form. The full optimizer-family
theorem still needs the source-reflection identification of the two rotation
halves, the arbitrary-projection attaining converse on one half, and the
arbitrary defect-isometry converse. The full cosine block is too large for
an unrestricted projection parameter: the explicit feasible opposite-source-
phase construction in `PAPER_CONTEXT.md` has the correct real part but
strictly exceeds the minimum. No maintained theorem is being refuted here;
this rules out an insufficient shortcut to the proposed classification.

No separate novelty claim is made for positive unitary averages or the
classical spectral-projection algebra. Bottazzi (2021), *Best approximation
by diagonal operators in Schatten ideals*, LAA 620, 1--26,
[DOI](https://doi.org/10.1016/j.laa.2021.02.025), supplies a further comparison
for additive Hermitian approximation by diagonal linear subspaces. Its
feasible set differs from the unitary transport fiber. Full theorem-formula
retrieval remains incomplete; this comparison does not certify priority.

## Optimizer-rigidity update after `84822b0ba` (24 October 2026)

The value theorem is now used to prove constraints on **every** finite
complex Schatten optimizer. `SchattenOptimizerKernel.lean` proves its actual
gradient kernel is an attaining reflection with only zero and right angles,
and is fixed pointwise for acute pairs. It also proves local-to-global
optimality when eigenvalue `-1` is absent; eigenvalue `1` is allowed. The
full all-minimizer and no-nonglobal-local-minima claims remain incomplete.

The classical algebra behind the smoothed multiplicity families is now
compiled: `PositiveUnitaryAverage.lean` handles positive averages in arbitrary
Hilbert dimension, including nonclosed range; `UnitaryScalarRealPart.lean`
classifies the finite scalar phase fibers by orthogonal projections or
self-adjoint unitaries. This is a prescribed-block result. In addition,
`SmoothedOptimizerCertificate` and `SmoothedOptimizerRigidity` now extract the
exact ambient equality criterion: vanishing diagonal defect and positive dual
displacement. Every global Charbonnier minimizer agrees with direct rotation
on all planes at or below the cutoff and fixes the canonical fixed directions,
even with supercritical angles elsewhere. The spectral-separation update
above now derives the positive-average equation and identifies the allowed
phases on positive-cosine blocks. Matching the two multiplicity halves and
proving the attaining converse remain. These results are compiled partial
classification; the full Grassmannian/unitary family theorem is incomplete. No independent mathematical novelty is claimed for the classical
trace-support equality or the unitary-average algebra.

Fresh primary-source comparison checked BLR (2001), Theorems 4.2 and 4.5,
and Massey--Rios--Stojanoff (2018), Theorems 3.5 and 3.12. BLR's 4.2 concerns
Frobenius minimizers; 4.5 requires a Q-norm and additional block structure.
Local Lidskii's two theorems concern conjugacy and fixed-singular-value
orbits. Those domains differ from the constrained stabilizer fiber here;
no implication giving our exact optimizer classification has been established.
Sources: [BLR journal PDF](https://journals.uwyo.edu/index.php/ela/article/download/117/117/117),
[Local Lidskii](https://arxiv.org/html/1806.11436). Priority remains provisional.

The real matching and field-gap assertions remain conventional. Independent
numerical diagnostics found no discrepancy for 4,800 nuclear matching lists
or six full real 6D Schatten-`3/2` multistart optimizations covering all
stabilizer determinant components. Their scopes, seeds and tolerances are
recorded in `PAPER_CONTEXT.md`; these checks do not certify a global theorem.
The infinite-dimensional positive-average result supplies algebra only, not
Schatten ideal convergence, index balance, or infinite-dimensional attainment.

## Late-afternoon reassessment: source `521572a2500c` (15:48, 24 October 2026)

The **unrestricted higher-rank complex Schatten theorem has been completed
in Lean** since the 08:51 and 14:23 audits below. All older passages
stating that `SP-3` is only drafted should be read as **historical
snapshot descriptions**, not current claims about proof status. The
publication decision remains to include these verified results in the
Davis--Kahan journal paper, with YWS separate.

| Current theorem/claim | Lean evidence in `521572a2` | Scope and priority boundary |
| --- | --- | --- |
| Exact all-rank complex Schatten `1<p<2` minimum `sum_j m_p(theta_j)` | `SchattenGlobalLowerBound.sum_phaseMinimum_le_schatten_transport_complex`; `SchattenGlobalAttainment.exists_unitary_minimizing_schatten_transport_principalAngles_complex` | **Compiled global theorem** over every complex unitary transporter, including mixing, repeated, zero and right angles; not a real-field or infinite-dimensional theorem |
| Existence of an attaining all-rank unitary | `SchattenGlobalAttainment.exists_unitary_attaining_schatten_principalAngles_complex` | Independent minimizing phase on principal planes produces a feasible witness; no-mixing lower bound supplies the nontrivial global certification |
| Canonical optimality `iff` every angle `<= acos((2-p)/p)` | `SchattenCanonicalOptimality.nonacuteDirectRotation_schatten_minimal_iff_complex` | **Compiled all-rank cutoff**, equality included; not a complete classification of every minimizing transporter |
| Smoothed minimum, uniqueness, quartic transition, commuting correction | `SmoothedPrincipalAngles`, `SmoothedExplicitOptimizer`, `SmoothedOptimizerUniqueness`, `SmoothedQuarticStability`, `SmoothedCommutatorCutoff` | Previously completed; still the strongest application-oriented family |
| Real matching, sorted-pair formula and sharp field gaps | `real_matching_transport.tex`, formalized building blocks | **Not yet completed** as unrestricted global theorems in this snapshot |

**Novelty assessment.** The global Schatten principal-angle formula and
sharp all-rank cutoff now join the exact smoothed-penalty theory as the
leading *completed* candidates for original mathematical theorems.
Davis--Kahan (1970) and Bolotnikov--Li--Rodman (2001) already established
the phase/transport setting, partial norm optimality, and failures for
`p<2`. We may state exactly what we have formalized and prove, but
should not claim historical priority for the all-rank formula until an
independent search for equivalent quotient-metric and matrix-completion
statements has been resolved. A modern use case is an **exact optimum
certificate** for arbitrary complex unitary subspace alignment; efficiency,
noise robustness, and quantum implementation require further work.

The included paper section is `schatten_transport_verified.tex`, with
numerical two-angle example at `p=3/2`, and Manim's `novelty-tour` adds
an all-rank theorem slide and a no-mixing proof-intuition slide. The
only main-text unformalized transport formula remains the optional
real line/hyperplane working-draft box. **The historical source inventory
stays 28 proved plus one refuted, not 30 or 31 source results.**

---

## Afternoon reassessment: source `642de34df29a` (14:23, 24 October 2026)

This section is the **current assessment** for the journal article. The
claim-by-claim table below records the original 08:51 snapshot and remains a
useful prior-art baseline; its descriptions of the smoothed theorem as only
having a strict-subcritical stability bound are superseded here.
The earlier suggestion to create a separate optimization paper is also
superseded by the authors' publication decision recorded in `PAPER_CONTEXT.md`:
**the verified smoothed-transport mathematics belongs in the Davis--Kahan
journal article**. We retain the separate YWS stub.

### Established scope newly important for the contribution statement

| Candidate contribution | Verified endpoint(s) in the 14:23 snapshot | Exact limit |
| --- | --- | --- |
| Globally exact complex smoothed minimum, with a computed optimizer | `SmoothedPrincipalAngles`, `SmoothedSubspaceOptimization`, `SmoothedExplicitOptimizer` | Finite-dimensional complex Hilbert spaces, equal-rank subspace pairs, `tau>0`, literal Charbonnier singular-value cost; no all-penalty optimality assertion |
| Canonical optimality and uniqueness **through** the cutoff | `SmoothedCanonicalOptimality.smoothed_canonical_isMin_iff`; `SmoothedOptimizerUniqueness.smoothed_transport_unique_minimizer_iff`; `SmoothedQuarticStability.smoothed_canonical_unique_minimizer` | Uniqueness of the **global minimizer** iff every principal angle is at most `acos(eta^-2)`; above it distinct opposite-phase minimizers exist. This does not classify **all** supercritical minimizers |
| Global quartic stability through critical angles and strict quadratic growth | `SmoothedQuarticStability.smoothed_transport_quartic_growth`; `SmoothedSubspaceStability.smoothed_transport_growth_of_principalAngles_le` | Quartic coefficient `3 tau/(32 eta^4 n)` for `n>=1` in the closed cutoff regime; quadratic coefficient strictly positive below; no claim that global quartic coefficient is sharp |
| Sharp *order* of critical flatness | `SmoothedCriticalFlatness.critical_phase_quartic_factorization`, `tendsto_critical_phase_quartic_ratio`; `SmoothedCriticalTransportFlatness.smoothed_critical_planar_no_quadratic_growth` | Actual feasible planar scalar-phase path; its fourth-order leading chord coefficient is `eta^-2/(4d)` with `d=sqrt(eta^2-eta^-2)`. The planar result excludes any positive local quadratic-growth constant |
| Exact closest unitary preserving a given projection | `SmoothedCommutingCorrection.optimalSmoothedCorrection_isMin_of_commute`; `SmoothedCommutatorCutoff.canonical_correction_isMin_iff_commutator`, `smoothed_correction_unique_minimizer_iff_commutator`; `SmoothedCorrectionStability` | Unitary ambient `A`, orthogonal projection `P`, finite complex dimension; the canonical correction is optimal **and the closest correction unique** iff `||AP-PA||_op <= sqrt(1-eta^-4)`. No gate-locality, physical-noise, or algorithmic-complexity constraint |
| Sharp scalar value sensitivity and parameter selection | `SmoothedValueSensitivity`; `SmoothedPhaseMinimum`; smoothing cutoff in `smoothed_transport_verified.tex` | `2/eta` is the least uniform Lipschitz coefficient in principal angle; the minimal `tau` for a single angle with positive cosine is `(1-cos theta)/sqrt(cos theta)` |

**Novelty judgment.** The full constrained minimum and explicit spectral
optimizer remain credible candidates for a mathematically new theorem. The
exact boundary uniqueness classification, critical quartic order, and the
commutator-based symmetry correction make a stronger, more specific
contribution claim than the optimum alone. We have **not** established
first-publication priority for this collection. The phase mechanism,
unitary-subspace completion constraint, weighted matrix nearness, nuclear
norm certificates, and smooth singular-value penalties all have prior art.
The most important remaining novelty check is whether a general constrained
weighted nuclear/Procrustes theorem simultaneously yields the optimum,
cutoff, uniqueness and critical error bounds. Check the exact hypotheses,
not only abstracts.

### Applications by evidentiary strength

1. **Immediate theorem-level:** exact nearest complex unitary preserving a
   projection (including selected spectral subspaces) and an operator-norm
   commutator test for canonical optimality/uniqueness. The correction preserves
   the subspace and its complement. Nearby approximate-symmetry constructions
   (e.g. Chubb--Flammia) already exist, so existence alone is not new.
2. **Immediate theorem-level:** cost-optimality certificates for feasible
   numerical candidates, with quadratic or quartic Frobenius-distance error
   bounds in the correct angle regimes. This is a mathematical guarantee,
   not an experimentally measured solver speedup.
3. **Immediate numerical consequence:** if principal angles are estimated,
   the exact optimum changes by at most `(2/eta) sum |theta_i-phi_i|` for
   matched angle lists. A complete statistical guarantee also needs a
   theorem controlling the principal-angle estimation errors.
4. **Prospective only:** quantum gate synthesis under locality/depth limits,
   error correction under noise channels, MRI/PCA improvements, and constrained
   hardware implementation. The current unitary-transport feasible set does
   not include those extra assumptions, and no experiments are reported.

The journal manuscript now includes a self-contained `2x2` example at
`tau=1`, with `theta_c = 67.5444848 degrees` and commutator cutoff
`0.92417637`. At `45 degrees`, the unique correction is `I` at exact cost
`0.51856025`. At `80 degrees`, scalar phase corrections `exp(±i 62.9597168
 degrees) I` attain `1.18690483`, while the canonical correction has cost
`1.25742453`. These values come from exact algebraic formulas, not numerical
optimization, and are independently checked by
`visualizations/tests/test_novelty_latex.py`. The parallel presentation
`visualizations/dkvis/decks/novelty.py` teaches the cutoff and quartic
transition using the repository's semantic Manim colors.


## 1. Executive assessment

There are **three distinct publishable stories** and they should not be
confused.

1. **Formalized Davis--Kahan theory.** The reviewed source inventory has 29
   result-level targets: 28 are formalized at the reviewed scope and the
   printed Proposition 4.4 is refuted. The extension includes a verified
   counterexample at arbitrarily small positive angles, a universal
   projection-displacement lower bound, a sharp *class-uniform* secant
   approximation factor, an exact real four-dimensional trace optimum,
   a finite-dimensional all-pairs complex trace optimum, and a directed-sine
   projector trace decomposition. This is already a coherent **formalized
   mathematics** paper. It does not require priority for the classical phase
   construction or the elementary norm comparisons.
2. **An exact, globally optimized *smoothed* spectral-transport problem.**
   The snapshot formalizes the unrestricted finite-dimensional complex
   Charbonnier minimum for equal-dimensional subspaces, an **explicit
   optimizer**, and a **quantitative stability inequality** below the
   phase-transition angle. The constraint is the old one, but the
   nonhomogeneous penalty, exact angle formula, and global optimizer make
   this the strongest currently **Lean-completed candidate for a new
   mathematical theorem**. Its originality is *plausible, not certified by
   negative search results*. The weighted nuclear-norm reformulation and
   classical matrix-approximation literature demand further review.
3. **Schatten and real-field optimization.** The planar complex
   `1 < p < 2` transition, including the necessary-and-sufficient critical
   angle for all admissible planar unitary competitors, **is formalized**.
   The general complex higher-rank angle-sum formula, classification of all
   minimizers, exact real arbitrary-rank matching formula, sorted two-sum
   reduction, and sharp dimension-free real-minus-complex field gaps have
   substantive **conventional proof drafts and many verified ingredients**.
   Their final global statements are **not yet Lean-certified** in this
   snapshot and require independent mathematical review before prominence
   or publication.

**Historical recommendation (08:51; superseded for publication scope):**
The earlier review favored a separate optimization article. The authors
subsequently decided to include the verified smoothed mathematical extension
in this journal paper. The real-matching conclusion remains outside the checked main text;
the higher-rank complex Schatten result was subsequently completed in `521572a2`;
the textbook-metric discrepancy remains a separate edition-verification issue.

The word **novel** here means a defensible mathematical first-publication
claim; it does *not* mean the statement was recently formalized, that a proof
is difficult, or that an exact matching phrase was absent from web searches.

## 2. Notation and optimization domains

Let `U,V` be equal-dimensional subspaces of a finite-dimensional real or
complex inner-product space, with orthogonal projections `P,Q` and principal
angles `theta_1,...,theta_k` in `[0,pi/2]`. A **transporter** is an orthogonal
(real) or unitary (complex) `W` with `W(U)=V`, or equivalently `WPW*=Q`.
The *extrinsic* ambient displacement is `I-W`, not the shortest intrinsic
path on the Grassmannian, not just the distance between projections, and
not a minimization over all unrestrained matrices.

Write

```
D_rho(U,V) = min_{W unitary/orthogonal, W(U)=V}
               sum_{j=1}^n rho(sigma_j(I-W)).
```

`rho(s)=s` gives full nuclear/trace displacement; `rho(s)=s^p` gives the
Schatten-`p` power, whose minimizer also minimizes the Schatten norm;
`rho_tau(s)=sqrt(tau^2+s^2)-tau` with `tau>0` gives the smoothed
(Charbonnier/pseudo-Huber) spectral penalty. For the first two,
`D_rho` is related to classical unitarily invariant *norms*; the last
functional is not itself a homogeneous norm. Real and complex feasible
sets are different, even when the principal angles coincide.

The **principal-angle formula** for a cost, **attainment of its infimum**,
**the form of a minimizer**, **classification of every minimizer**,
**stability/error bounds**, and **Lean formalization** are separate claims.

## 3. Exact claim-by-claim matrix

These labels are for *internal priority assessment* and not additional
rows of the original 29-result Davis--Kahan source inventory.

| ID | Mathematical claim and exact scope | Status in `b2519945` | Closest verified prior art / priority judgment |
| --- | --- | --- | --- |
| DK-1 | 28 source results proved and one false printed real Proposition 4.4 identified, across the original's reviewed real/complex, unbounded and ideal-norm scopes | Formalized, source-semantic audit documented | **Strong formalization/source-correction contribution**, not a claim that sine-theta theory itself was invented here |
| DK-2 | Real R4, two equal positive angles, full trace improvement for every `0<theta<pi/2`, arbitrarily close to zero | Formalized: `SmallAngleCounterexample.lean` and source audit | Realification of Davis--Kahan's **1970 complex phase**; potentially new *explicit identification of the false printed real short-angle claim*, not a new phase idea |
| DK-3 | `N(P-Q)<=N(I-W)` for every transporter and every unitarily invariant seminorm | Formalized: `ProjectionDisplacement.lean` | Standard pinching/commutator consequence; **known mathematics or immediate classical deduction** |
| DK-4 | `N(I-R)<=sec(alpha/2)N(I-W)` for acute subspaces, sharp at each fixed angle **uniformly over norm class**, with `2/sqrt(3)` at `alpha<=pi/3` | Formalized: `SharpDisplacement.lean`, fixed-angle sharpness | Classical principal-angle singular values + DK-3; **useful sharp formulation**, not demonstrated first-publication mathematics. Not individually optimal for every norm |
| DK-5 | Exact global real four-dimensional trace minimum `4sin(theta)` for the repeated-angle family | Formalized: `TraceOptimality.lean` | Follows immediately from DK-3 and attaining witness; **new certified statement in this development**, short classical deduction |
| DK-6 | Unrestricted finite-dimensional **complex** equal-rank trace optimum `2 sum sin(theta_j)` (zero/right angles included) | Formalized: `ComplexCrossedDefects.lean`, `ComplexPhaseTrace.lean`, `ComplexTracePrincipalAngles.lean` | Old phase mechanism and BLR unitary-completion problem; an exact formula not located verbatim, but short principal-plane/commutator deduction; **undetermined priority** |
| DK-7 | Real/complex finite-dimensional projector trace decomposition into two directed sine-map trace norms, with possibly unequal ranks | Formalized: `ForTauCeti/.../Projection/TraceSine.lean` | Classical block principal-angle identities; **likely known/easy consequence**, no first-publication claim |
| SP-1 | **Unrestricted complex planar** Schatten-`p` `1<p<2` minimum over *all* unitary line transporters and canonical threshold `acos((2-p)/p)` | Formalized: `SchattenPlanarOptimization.lean`, `SchattenPhaseTransition.lean` | BLR (2001) knew failure below `p=2`, incl. right angle, but the complete threshold/phase law was not located. **Credible distinct exact classification; priority unresolved** |
| SP-2 | For `p=3/2`, critical angle `acos(1/3)` and explicit symmetry-breaking phase | Formalized scalar/planar: `SchattenThreeHalves.lean` and SP-1 | Specialization of SP-1, **not an independent substantial novelty claim** |
| SP-3 | Complex arbitrary-rank `D_{s^p}(U,V)=sum_i m_p(theta_i)` for `1<p<2` | Complete conventional proof candidate in `schatten_optimization.tex`, with compiled gradient/variation/realization sublemmas | **Highest-potential analytic extension** if final global no-mixing reduction survives independent review; not yet a compiled global theorem |
| SP-4 | Every local minimum of unrestricted complex Schatten-`p` transport is global; infinite-dimensional Schatten-ideal extension | Conventional arguments in `schatten_optimization.tex` | Potentially interesting but **separate unverified generalizations**; ideal-class hypotheses and zero singular values especially need review |
| SM-1 | Exact **all-pairs complex** finite-dimensional Charbonnier spectral-penalty minimum, attained, explicit phase transition | **Formalized**: `SmoothedPrincipalAngles.lean`, `SmoothedSubspaceOptimization.lean`, `SmoothedPhaseMinimum.lean` | Penalty and constraint each classical; **best completed mathematical originality candidate**, with no identical source located yet |
| SM-2 | Explicit globally minimizing complex unitary via clipped functional calculus of positive cosine operator | **Formalized**: `SmoothedExplicitOptimizer.lean` | A concrete constructive strengthening of SM-1; may be an elementary companion to SM-1, but substantial for applications |
| SM-3 | Quadratic growth from optimum below strict angle cutoff, with explicit constant and Frobenius distance for **every admissible complex transporter** | **Formalized**: `SmoothedSubspaceStability.lean` | **Distinct and credible mathematical addition** if not implied by older error-bound/strong-convexity theorem |
| SM-4 | Global convex-relaxation tightness when commuting unitary factor is relaxed to commuting contraction (weighted nuclear cost) | **Formalized for the stated supplied structural class**: `SmoothedCommutantOptimization.lean`; instantiated in all-pairs argument | Strong proof mechanism; present as supporting theorem, not a generic statement for all convex relaxations |
| SM-5 | Complete classification of all smoothed optimizers, and broad spectral-penalty single-peak extension | Complete finite complex iff in `SmoothedNonacuteClassification`; joint attainment in `SmoothedPhaseDefectAttainment`; unique normalized parameters, full multiplicity product and topology in `SmoothedParameterNormalization`, `SmoothedMultiplicityParameters`, `SmoothedParameterTopology` | All-angle global classification and independent projection/defect homeomorphism compiled for `tau>0`, including compactness, rank-sector separation and exact simple-active count. Broad-penalty extension, local-to-global, component counts, manifold dimensions and ideal optimization remain open |
| R-1 | Exact real R4 rank-two minimum for *every continuous nondecreasing spectral penalty*, including separate determinant classes | Conventional proof draft in `real_four_dimensional_transport.tex` | Strong exact finite-dimensional problem; old matrix optimization warns against presenting mere nonminimality as new. **Not certified** |
| R-2 | All-dimensional real optimization reduces to weighted matching in angle blocks of real dimension at most four | Conventional proof draft `real_matching_transport.tex`, with compiled positive-gradient block decomposition in `RealBlockDescent.lean` and related modules | **Potentially strongest structural new theorem**, but exceptional-gradient assembly and global matching bound are **not compiled** |
| R-3 | For Schatten `1<p<2`, Charbonnier, and nuclear limits, matching reduces to minimum of **two sorted adjacent-pair sums** | Conventional derivation in `real_matching_transport.tex`; numerical checks corroborate but are not proofs | Would yield efficient exact algorithms and optimality thresholds; **submodularity and final reduction need independent proof review** |
| R-4 | Real-minus-complex optimal nuclear penalty is at most `2-sqrt(3)` regardless of dimension, with sharp equality cases | Conventional proof draft only; low-dimensional example realizes constant | **High-value sharp field-gap theorem** if globally true; proof of exclusion of higher-dimensional maxima must be scrutinized |
| R-5 | Charbonnier real-minus-complex gap at most `2eta(1-sqrt(1-1/(4eta^4)))`, explicit equality class | Conventional proof draft only; `eta=(tau+sqrt(tau^2+4))/2` | Another high-value result, **not yet verified**, depends on R-2/R-3 and tie-surface Hessian analysis |

**A compilation boundary is not a novelty boundary:** SP-3 and R-2 may be
mathematically true and publishable before Lean formalization, but an article
about *machine-checked* theorems cannot attribute their unrestricted scope
to the compiler until the matching declarations exist and build.

## 4. Strongest completed mathematics: exact smoothed transport

With `tau>0` define

```
rho_tau(s) = sqrt(tau^2+s^2) - tau,
eta = (tau + sqrt(tau^2+4))/2,
tau = eta - eta^(-1),   eta > 1,
theta_c = acos(eta^(-2)).
```

For a principal angle `theta in [0,pi/2]`, the scalar cost derived in
`SmoothedPhaseMinimum.lean` is

```
mu_tau(theta) =
  { 2( sqrt(tau^2 + 2 - 2cos(theta)) - tau ), theta <= theta_c;
  { 2 eta sin(theta) - 2 tau,                  theta >= theta_c.
```

The formulas agree at the threshold. The complex all-pairs theorem asserts

```
min_{W:WU=V} sum_{j=1}^n rho_tau(sigma_j(I-W))
     = sum_{i=1}^k mu_tau(theta_i).
```

In particular the scalar phase correction is zero through the critical
angle and (above it) can be chosen of magnitude
`delta(theta)=acos(eta^2 cos(theta))`. The optimizer is assembled in the
accepted finite-dimensional operator API, with repeated, zero, and right
angles rather than an assumption of a supplied coordinate chart.

A surprisingly effective identity, proved for the **literal singular-value
functional** in `SmoothedSpectralCost.lean`, is

```
sum_j rho_tau(sigma_j(I-W))
       = || eta W - eta^(-1) I ||_1 - n tau
```

for unitary `W`. This converts the smooth nonlinear spectral objective into
an **unequally weighted nuclear approximation problem** without removing
the nonconvex transporter constraint. The authors' certificate uses the
projection/intertwiner structure, not a theorem that every nuclear
minimization under arbitrary unitary constraints decouples.

**Further completed result:** Below a bound `beta` satisfying
`0<=beta<=pi/2` and `cos(beta)>eta^(-2)`, all principal angles at most
`beta` imply, for every feasible `T`,

```
 [cos(beta)-eta^(-2)]
 ------------------------------------ * ||T-R||_F^2
 2 sqrt(tau^2+2-2cos(beta))

       <= Psi_tau(T) - Psi_tau(R).
```

Here `R` is the selected **nonacute direct rotation** for the pair and
`Psi_tau` is the full literal spectral penalty. The coefficient is
positive by hypothesis. This controls *all* feasible near-minimizers,
not only a supplied principal-plane ansatz; see
`smoothed_transport_growth_of_principalAngles_le` in
`SmoothedSubspaceStability.lean`. A complete global description of every
minimizer at and beyond the threshold remains conventional.

### What is and is not established about originality

- **Known:** the Charbonnier/smooth hyperbola penalty as a spectral
  regularizer; the cosine--sine/principal-angle chart; nuclear norm duality;
  and unitary-to-subspace completion constraints (BLR Problem 1.1).
- **Not located directly in sources inspected:** the exact global **weighted
  nuclear coset minimum**, its smoothed principal-angle threshold and
  minimizing phase, plus the global quantitative growth inequality.
- **Unresolved:** whether a more general classical *weighted unitary
  Procrustes*, *nuclear norm completion*, or *distance to a subgroup*
  result implies SM-1 by a short specialization; and whether a spectral
  error-bound theorem specializes to SM-3. Negative keyword search does not
  answer either question.

This is the leading target for **independent referee-style mathematical
review** and a possible research paper distinct from the Davis--Kahan
formalization account.

## 5. Schatten `1<p<2`: a real phase transition, but two proof levels

For an angle `theta`, define the scalar constrained phase value

```
m_p(theta) = min_{0<=delta<=theta}
  [ 2sin((theta+delta)/2) ]^p
  + [ 2sin((theta-delta)/2) ]^p.
```

The **Lean-verified unrestricted complex planar theorem** states that this
is the global Schatten power among *all* complex `2x2` unitary transports
between the model lines, not merely among phase-parametrized candidates.
For `1<p<2` and `0<theta<pi/2`, the canonical transport is optimal if and
only if

```
theta <= acos((2-p)/p).
```

At `p=3/2` the cutoff is `acos(1/3)` (approximately `70.53` degrees),
with an explicit branch of nonzero minimizing phase above it. At `p=1`,
contrast the old complex phase mechanism: nonminimality can occur at
arbitrarily small angles. At `p>=2`, BLR's Q-norm result supplies the
old optimality mechanism.

The **proposed higher-rank formula**

```
min_{W:WU=V} ||I-W||_p^p = sum_i m_p(theta_i)
```

is **not a formal theorem in the snapshot**. The gap is a universal
**no-cross-plane-mixing** reduction over the full stabilizer fiber. The
repository proves many first- and second-variation lemmas, two-phase
spectral restrictions, feasibility of blocks, and positive-gradient real
block structure, but these are not equivalent to final global
subadditivity or independent plane optimality. Particular care is needed
when eigenvalue `1` makes second derivatives of the `p`-power singular.
The draft explicitly treats the null part differently; that treatment
needs independent inspection.

If finished and reviewed, SP-3 would plausibly support a new contribution:
all-principal-angle exact formula, necessity of the cutoff for arbitrary
rank, classification of symmetry-breaking minimizers, and a nearest
commuting-unitary interpretation. Its existence cannot be inferred
simply by taking direct sums of the already-proved planar minimizers:
that produces an **upper** bound, not a matching lower bound for mixing
transporters.

## 6. Real transport: matching structure and a dimension-free penalty gap

The conventional drafts exploit a field-sensitive point: a complex phase
can have a one-dimensional eigenspace, whereas nontrivial real rotations
need paired real directions. This causes parity and matching phenomena.

The proposed **real** minimum for a broad monotone spectral cost is a
minimum over matchings of principal-angle indices. Each singleton uses a
real planar rotation or reflection, and each edge combines two angles
in a real four-dimensional block. The draft's central reduction takes
stationary transports, uses their spectral gradient to obtain invariant
real blocks of dimensions at most four, then optimizes each block.

For nuclear cost and two angles `theta1>=theta2`, the draft's exact R4
formula is

```
min_{W real} ||I-W||_1
  = min{ 4 sin((theta1+theta2)/2), 2+4 sin(theta2/2) }.
```

For many angles the stronger **sorted two-sum** claim uses symmetry,
monotonicity, and submodularity of the edge cost: either pair adjacent
sorted angles, or reflect the largest and pair the remainder. Those last
ordering and global-minimum steps have not been formalized. Separate
numerical multistart comparisons help find counterexamples but cannot
supply the missing proof.

The claimed nuclear additive field gap is

```
0 <= D_real(U,V) - D_complex(U,V) <= 2-sqrt(3).
```

For one nonzero angle `theta=pi/3`,
`D_real=min{4sin(theta/2),2}=2`, whereas
`D_complex=2sin(theta)=sqrt(3)`. Thus the constant is **attained**;
what remains to prove globally is that additional angles cannot produce
more than this. At `tau>0`, the corresponding claimed smoothed bound is

```
0 <= D_real,tau - D_complex,tau
  <= 2eta [ 1 - sqrt(1-1/(4eta^4)) ].
```

The conventional manuscript derives equality cases and limiting behavior;
none is a **compiled all-dimensional real-field theorem** here. The
claim is strong enough that the independent proof of the compact
ordered-angle maximization, the tie-surface Hessian, reflection options,
and right-angle boundary cases deserves highest scrutiny.

**Research merit if sound:** an exact polynomial-time (after sorting,
linear number of scalar evaluations) solver for these real transport
objectives, plus a sharp error guarantee for complex relaxation. This is
substantively more distinctive than restating the old trace nonminimality.

## 7. Earlier mathematical literature: what it actually covers

This section distinguishes direct source inspection from source leads.
Source identifiers `LIT-*` in `PROPOSITION_4_4_LITERATURE_MAP.md` provide
the longer historical chain.

| Source | Inspected evidence | What it establishes / what it does not |
| --- | --- | --- |
| Davis--Kahan (1970), *The Rotation of Eigenvectors by a Perturbation. III*, SIAM JNA **7**, DOI `10.1137/0707001` | Example 4.2; Props 4.3, 4.4; §4, older audit | Their complex scalar phase already reduces trace displacement; their stated real short-angle full-norm minimization fails. The present real small-angle source correction is an exact audited identification, not invention of scalar phases |
| Sz.-Nagy (1940s), Kato, *Perturbation Theory for Linear Operators* (1966), Chapter I §4.6; Murphy, *C*-Algebras and Operator Theory* (1990), Lemma 6.2.1 | Kato and Murphy construction inspected in prior audit; earliest Sz.-Nagy work via later historical sources | The projection-intertwining polar unitary and operator-norm nearby-projection bounds predate the project. The secant inequality should be presented as sharp classical-geometric consequence unless exact priority can be established |
| Bolotnikov--Li--Rodman (2001), *Minimal Distortion Problems for Classes of Unitary Matrices*, Electronic J. Linear Algebra **8**, 26--46, DOI `10.13001/1081-3810.1058` | **Official journal PDF**, Problem 1.1, Thms 3.1/4.2/4.5, Lemma 3.3 (printed p.36) | Poses exactly `min ||U-I||` over subspace transporters; proves Q-norm and Frobenius cases and demonstrates Schatten `1<=p<2` nonminimality. Does not in the statements inspected give the exact angle-dependent planar cutoff, all-rank real matching, or smoothed weighted-nuclear formula |
| Qiu--Zhang--Li (2005/06), *Unitarily Invariant Metrics on the Grassmann Space*, SIAM JMAA **27**, 507--531, DOI `10.1137/040607605` | §5 checked in older audit | Grassmann metrics and repetition of the real minimality assertion; *intrinsic path length*, projector/chord distances, and quotient ambient-unitary distance must not be conflated |
| Zhang--Qiu (2010), *From Subadditive Inequalities of Singular Values to Triangle Inequalities of Canonical Angles*, SIAM JMAA **31**, 1606--20, DOI `10.1137/09074841X` | Printed p.1615 checked in previous audit | Explicit awareness of trace-norm nonminimality, so generic `p=1` counterexample is not new; not an exact real small-angle source-level correction |
| Aubrun--Szarek (2017), *Alice and Bob Meet Banach*, AMS MSM 223 | **Author-hosted Chapter 5**, p.116, Table 5.1; Appendix B equations/exercises inspected via a third-party textual reproduction only | Appendix B defines **our exact quotient objective** and prints an all-`p` canonical-angle expression for it; this fails for `p<2` (below). A further correction worth careful primary-edition verification. Its geodesic metric is a **different** objective |
| Aubrun--Szarek posted errata, 7 September 2023 | **Author-hosted PDF**, 2 pp. | The displayed errata do not list the quotient metric/exercise issue. Absence is not proof that a later printing did not amend it |
| Chubb--Flammia (2017), *Approximate Symmetries of Hamiltonians*, J. Math. Phys. **58**, 082202, DOI `10.1063/1.4998921` | Final arXiv and older author PDF reviewed in prior research record | A nearby **ambient** commuting unitary and approximate symmetry constructions are prior art; the proposed contribution is *exact* norm-specific correction, not first existence of commuting rounding |
| Lobos--Salazar Cavazos--Nadakuditi--Fessler (2026), SIAM JIS **19**, 839--878, DOI `10.1137/25M175891X` | Primary metadata/full text identified in previous pass | Smooth singular-value/hyperbola penalties are known; their inverse-problem objective differs from the unitary transporter coset. Don't claim to invent Charbonnier penalties |
| Antonini--Cavalletti (2026), *Geometry of Grassmannians and Optimal Transport of Quantum States*, Annali SNS Pisa **27**, 201--254 | Primary journal PDF pages cited in paper context | Wasserstein transport with an intrinsic Hilbert--Schmidt Grassmannian base cost, not minimizing a spectral penalty of an ambient unitary transporting a subspace |
| Adrian Lewis (1996), spectral-function differentiability (Math. Oper. Res. **21**, pp. 576ff) | Primary printed p.577 examined in prior pass | Differential calculus for spectral functions is standard; don't attribute its mechanisms to the present project |

### Directly testable discrepancy in Aubrun--Szarek

The author's Chapter 5 Table 5.1 labels its real and complex Grassmannian
metric the **quotient of the extrinsic Schatten norm** and records the
diameter `sqrt(2)*(2k)^(1/p)` over its displayed `p` range. The
Appendix B reproduction, equation (B.13), defines

```
h_p(E,F) = min_{W orthogonal, W(E)=F} ||I-W||_p.
```

Exercise B.12 asserts `h_p(E,F)=2^(1/p) [sum_j
(2sin(theta_j/2))^p]^(1/p)`; the solution hint even states
**entrywise singular-value domination** of an arbitrary transporter by
the direct rotation. The latter is false even for `p>=2` (although
norm-optimality can still hold there).

For **two orthogonal real lines** `E,F` in `R^2`, `theta=pi/2`:

```
W_can = rotation by pi/2;
s(I-W_can) = (sqrt(2), sqrt(2));
||I-W_can||_p = sqrt(2)*2^(1/p).

W_ref = reflection interchanging E and F;
s(I-W_ref) = (2,0);
||I-W_ref||_p = 2.
```

For every `1<=p<2`, `sqrt(2)*2^(1/p)>2`; hence the **stated
extrinsic quotient formula** fails for this example. Already at `p=1`,
all pairs of real lines admit a reflection of cost two, so the book's
claimed diameter `2sqrt(2)` for `Gr(1,R^2)` cannot be correct under the
quoted extrinsic definition. **There is a stronger all-rank complex
consequence of the already formalized trace theorem:** for `k<=n/2`,

```
diam_{h_1} Gr(k,C^n)
 = max_{U,V} 2 sum_{j=1}^k sin(theta_j) = 2k,
```

attained by mutually orthogonal `k`-planes; the author-hosted table
instead gives `2sqrt(2)k`. This formula is an immediate consequence of
the verified complex all-pairs trace minimum, not an independently new
piece of optimization. At `p=2` the planar rotation and reflection both
have value two; the hint's **entrywise** singular-value domination still
fails because `sqrt(2) > 0` in the second coordinate.

**Important limitation:** the underlying orthogonal/unitary transport
problem and Schatten-`p<2` failures were known by BLR (2001). Finding
another incorrect printed extension is a **source-correction result**, not
proof that all `p<2` nonminimality is new. Also, the author's Chapter 5
**geodesic** formula is not automatically disproved by this extrinsic
reflection: disconnected-group components and path-length objective
matter. Before contacting authors or asserting a bibliographic erratum,
obtain the actual publisher or author Appendix B PDF, check the version,
normalization, and any later print corrections. The inspected online
Appendix B is a third-party textual reproduction, not the authenticated
2017 printed book.

Sources:
- [Aubrun--Szarek author page](https://case.edu/artsci/math/szarek/ABMB/ABMB.html)
- [Author-hosted Chapter 5, Table 5.1](https://case.edu/artsci/math/szarek/ABMB/ABMBchapter5.pdf)
- [Authors' errata (2023)](https://case.edu/artsci/math/szarek/ABMB/errata.pdf)
- [Appendix B text reproduction (unverified edition)](https://dokumen.pub/alice-and-bob-meet-banach-the-interface-of-asymptotic-geometric-analysis-and-quantum-information.html)
- [BLR original journal PDF](https://journals.uwyo.edu/index.php/ela/article/download/117/117/117)

## 8. Where a referee could reasonably object

1. **Conflating formal verification and mathematical originality.** State
   them separately and cite actual declarations, not a change log.
2. **Calling a classical mechanism a new theorem:** polar projection
   intertwining, principal-angle lists, old scalar phases, nuclear norm
   duality, finite spectral-function calculus, and Q-norm minimization all
   have earlier owners.
3. **Upgrading structural lemmas to a global optimization theorem.** The
   full mixed-eigenspace inequality is what must rule out exotic
   transporters. A formula for constructed block competitors is only an
   upper bound on the unrestricted infimum.
4. **Assuming the same optimum over R and C.** Real pairing constraints
   give strict field gaps; do not copy the complex formula into a real
   corollary without parity/equality analysis.
5. **Confusing the metric domains.** The Grassmannian's intrinsic geodesic
   distance, chordal projection distance, and extrinsic quotient of
   `||I-W||_p` do not have the same minimizers or all the same formulas.
6. **Overclaiming all-norm sharpness.** The secant constant is sharp across
   the whole family of UI norms at a fixed angle, not for each one.
7. **Taking `p`-power derivatives at zero as smooth for `1<p<2`.** The
   first variation is controlled; conventional second-variation arguments
   require null-phase splitting or perturbations of sufficient order.
8. **Overstating uniqueness.** One explicitly constructed optimizer does
   not classify all optimizers. Supercritical repeated angles can admit
   continuous families; right-angle defects must be addressed separately.
9. **Drawing publication priority from a keyword search.** An equivalent
   theorem may live under weighted polar decomposition, block-matrix
   Procrustes, matrix nearness with symmetry, quotient metrics, or
   commuting-unitary approximation rather than under the term `transport`.
10. **Treating numerics as proofs.** Differential-evolution and multistart
    searches are useful for falsification; they do not prove a global
    two-sum formula or a Hessian maximum principle.
11. **Moving YWS back into the Davis--Kahan paper.** That source has a
    separate stub and separate historical uncertainties.

## 9. Ranked next investigations and acceptance tests

| Priority | Action | A decisive success criterion | Consequence |
| --- | --- | --- | --- |
| 1 | Independent **mathematical** review of SM-1/SM-2/SM-3 and the exact Lean statements | Verify every optimizer is feasible; the nuclear support certificate applies to **all** commuting competitors and transports; stability constant is as stated | A defensible core of a standalone optimization paper now |
| 2 | Broaden the exact-prior-art chain for weighted nuclear / constrained unitary cosets | Read general matrix-nearness/weighted Procrustes theorems, not just titles; write an implication or non-implication proof for each | Establish whether SM-1 is mathematical novelty or a special case |
| 3 | Close SP-3 for **arbitrary** complex rank | Full formalized/global theorem or independently referee-checked conventional proof that prohibits cross-plane mixing including zero phases | Exact all-rank Schatten `1<p<2` optimization, likely the strongest next theorem |
| 4 | Close R-2 real matching lower bound, especially **zero and maximal gradient** blocks | Block decomposition covers every optimizer in all determinant components and every boundary configuration; matching attainment proof | Structural real optimization theorem |
| 5 | Verify R-3 submodularity and sorted reduction | Precise crossing/uncrossing inequalities and two configurations for odd/even lists, independently checked | Fast exact real solver |
| 6 | Review R-4/R-5 globally, not just sharp examples | Independent compactness, boundary, tie-Hessian and induction proof; equality cases checked with degenerate angles | Sharp dimension-free field-penalty gap with equality classification |
| 7 | Obtain **authenticated** Aubrun--Szarek Appendix B/errata versions | Same quotient definition, exponent range, formula and claimed majorization verified in original PDF/print; authors consulted as appropriate | Possible independent mathematical correction, not core optimization priority |
| 8 | Decide publication split and edit the journal text conservatively | Every assertion in a checked-only paper matches an actual Lean theorem's hypotheses | Avoid a paper with unsupported novelty language |

Where feasible, ask a skeptical operator theorist or matrix analyst to
attempt to disprove the optimization and field-gap claims **before** working
on exposition. Concrete falsification tests include random repeated angles,
zero angles, right angles, nontrivial fixed subspaces, reflections, unequal
angle pairs, both determinant components of the real orthogonal group,
and `p` values arbitrarily near one and two.

## 10. Publication and communication recommendations

**Formalization article.** Lead with the audited 28-plus-one Davis--Kahan
coverage, the original theorem's full scope, the verified failure of the
specifically printed real Proposition 4.4, and the formalized replacements.
The exact complex trace and projection-direction decomposition are good
substantive formalized mathematics. Describe sharp displacement as a
*verified sharp replacement*, not first invention of subspace geometry.
Keep the more specialized smoothed and still-conventional optimization
research in the accompanying context or a different mathematical paper
unless it becomes integral to the story.

**New optimization article (candidate).** A plausible mathematical spine is:
(a) precise real/complex *extrinsic quotient* objective, (b) exact
unrestricted complex smoothed formula and constructive optimizer, (c)
its sharp phase threshold and quadratic growth below it, (d) the exact
complex Schatten `p<2` threshold and an all-rank theorem once completed,
(e) real pairing/matching and sharp field gap if their unrestricted proofs
survive. The paper should directly compare BLR Problem 1.1 and the
Aubrun--Szarek quotient metric, and distinguish intrinsic distance.
Formal verification is a methodological strength, but a matrix-analysis
referee will still ask: **what mathematical fact could not be read off
from a known theorem?**

**Possible separate correction note.** Verify Appendix B and the author
errata, then explain the rank-one reflection, the invalid singular-value
vector inequality, the corrected range or corrected quotient formula,
and what survives about intrinsic geodesic distance. Do not frame this
as an independent discovery of trace nonminimality, already explicit in
BLR and earlier Davis--Kahan phase examples.

**Careful claim templates (for future writing, not automatic manuscript edits):**

- Defensible: "We formalize a sharp real counterexample to the printed
  Proposition 4.4 at arbitrarily small positive principal angles."
- Defensible: "For every positive smoothing parameter, our Lean development
  proves an exact global minimum and constructs an optimizer for complex
  finite-dimensional equal-rank subspace transport under the singular-value
  Charbonnier penalty."
- Defensible with historical qualifier: "An exact angle formula and
  stability bound for this constrained smoothed problem were not found
  in the primary sources surveyed."
- Not defensible now: "We discovered that full trace-norm minimization
  fails for direct rotations" (1970/2001 precedents).
- Not defensible now: "We solved unrestricted higher-rank real Schatten
  transport in Lean" (last matching/sorting endpoint not certified).
- Not defensible now: "This is the first exact subspace transport
  optimization theorem" (BLR Problem 1.1 and classical Q-norm cases).

## 11. Evidence, negative-search limits, and continuation notes

**Repository source inspected for this report:** `b251994524e7f4a5145f3a045b757cad30c6dbf9`.
The status distinctions above were checked against Lean declaration
statements, `PAPER_CONTEXT.md`, and the conventional LaTeX fragments.
This review did **not** run an independent Lean compilation: the repository
records successful focused and aggregate builds for the declared endpoints;
none of those established statuses is downgraded on that account.
No theorem was added to the original 29-source-result inventory.

**Primary-source verification in this pass:** BLR's 2001 journal PDF,
including the actual screenshots of Theorem 3.1 (printed p.33) and Lemma
3.3 (printed p.36); Aubrun--Szarek's author-hosted Chapter 5 Table 5.1;
and the author's posted September 2023 errata. **Secondary textual
inspection:** Appendix B, Exercise B.12, equation (B.13), and Appendix E
hint via a book-text reproduction; original print pending. Earlier
`PROPOSITION_4_4_LITERATURE_MAP.md` and `PAPER_CONTEXT.md` record
more extensive sources and their precise pages, including Davis--Kahan,
Kato, Murphy, Zhang--Qiu, Lewis and recent Grassmann/Finsler work.

**Negative searches done in the cumulative campaign:** unitary/subspace
minimal distortion and Schatten `p` phase transitions; constrained
unitary completion weighted nuclear; Charbonnier/pseudo-Huber smoothed
unitary transport and principal angles; nearest block diagonal commuting
unitary; Grassmann extrinsic versus intrinsic quotient metrics; real
orthogonal matching, parity, and field gaps; matrix-nearness with
singular-value penalties; 2026 spectral regularization. No matching
full SM-1 or R-2/R-5 statement surfaced in these queries. This is only
**search-method evidence**. It is *not* proof of first publication.

**Sources needing deeper reading:** weighted orthogonal/unitary Procrustes
and polar decompositions with spectral trace costs; nuclear support
functionals under two-block unitary constraints; exact nonlinear
Grassmann quotient distances; broad spectral-function matrix nearness
results; paper versions and citation chains behind the BLR Theorem 4.5;
current published printing of the Aubrun--Szarek Appendix B statement;
and potential post-2026 (or recently posted) results overlapping the
smoothed minimum. Compare hypotheses and optimization domains
algebraically; matching keywords alone is insufficient.

**Future agent rule:** update the relevant table row with (i) exact theorem
statement and fields, (ii) verified Lean endpoint *or* explicit conventional
proof status, (iii) primary-source page/statement and its mathematical
implication, (iv) actual open mathematical/provenance gap. Do not import
internal novelty triage, source-hunt logs, agent process, or provisional
real matching statements wholesale into `paper.tex`.

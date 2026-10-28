# Spectral subspace transport: current research plan

Updated 27 October 2026. Mathematical checkpoint `ff3c1657d` includes the
field-independent nuclear equality certificate and exact real equality-
attainment criterion. The subsequent smoothed-power campaign proves the
closed-family finite complex minimum/attainment theorem C1b, including zero smoothing, and
ambient spectral decomposition C1a: every finite complex constrained local
minimum has actual paired phase blocks with acute/right means and a
self-adjoint kernel restriction, with exact cost splitting. The shared C2
phase law and the closed unrestricted canonical criterion are now also
proved. C5 now proves the full closed-family value, finite-cost feasibility
and attainment theorem in arbitrary complex Hilbert dimension. The full
default build passed **21,495 jobs**, warnings as errors, after
`lake exe cache get`.
The earlier spectral checkpoint was `96aeb922d`
(accounting `2b481b94d`). See the
[unification and provenance note](spectral-transport-unification.md) for the
structural explanation, exact theorem map and source-authentication boundaries.

Start here on a new machine. The
[dated research handoff](schatten-research-handoff-2026-10-26.md) contains the
long proof history and implementation details. Its dated entries retain their
original status; this plan and its current-frontier summary take precedence.
[Paper context](../papers/dk_formalization_journal/PAPER_CONTEXT.md) separates
compiled mathematics from manuscript integration. Manuscript and visualization
changes remain assigned separately.

## Objective and a useful completion boundary

The success criterion is a cohesive, publication-worthy central theory,
not completion of every open item below. The central thesis is: spectral
penalties select optimal phases, the scalar field imposes compatibility,
and operator ideals govern infinite-dimensional feasibility and attainment.
The active real equality-certificate milestone is now proved. The
[publication-core assessment](spectral-transport-publication-core.md) examines
the proposed general penalty argument in
`papers/dk_formalization_journal/spectral_penalty_transport.tex`; it is
conjectural and excluded from the verified manuscript. Its concrete
two-parameter smoothed-power specialization is now proved, including the
Hilbert-space lift. The completion and attribution audit at `cda45e2d4`
checks the displayed core against actual declarations and records its
remaining historical authentication limits. Evaluate that assessment before
choosing any optional theorem campaign.

Develop exact extrinsic transport optimization over **every** unitary or
orthogonal W taking K to L, with objective `||I-W||_p` or an explicitly specified
spectral penalty. The intended theory explains the minimum, every optimizer,
field dependence, phase transitions, infinite-dimensional feasibility, and a
useful correction construction. Path length, matrix-logarithm distance, and
frame-fitting Procrustes problems have different objectives or constraints.

The complex theory already has exact infinite-dimensional strict-exponent and
smoothed classifications and the complete nuclear certificate. The real equality-attainment criterion is now complete; unrestricted real
classification above that bound is a secondary extension. A journal contribution
can have a precise, complete scope before every extension below is solved.
Historical originality requires its own theorem-level literature comparison.

## Completed organizing theorem and audited completion boundary

The publication-core assessment specifies five principal statements and their
status. C1/C2 and the operator-ideal lift C5 are proved for
`rho_(p,tau)(s)=(tau^2+s^2)^(p/2)-tau^p`, `1<=p<=2`, tau>=0:

1. **Completed:** C1b's exact value/attainment formula for `1<=p<=2`,
   `tau>=0`, equal-rank subspaces of finite complex Hilbert space. Its
   declaration is `SmoothedPowerTransport.exists_unitary_minimizing_transport_principalAngles_of_nonneg`
   in `SmoothedPowerBoundary.lean`, prefix `TauCeti.DavisKahan.FiniteDimensional`.
   C1a supplies actual paired coordinates; their angle trace and the common
   convex/nuclear reflection bound give the lower bound. Canonical independent
   phases attain it. Continuity of scalar minimum values and each fixed
   unitary cost extends the bound to zero smoothing; the native Schatten
   power identity is proved. No entire optimizer-set limit is asserted.
2. **Completed:** the shared scalar phase law, including critical equality,
   unique positive stationary/global-minimum phase beyond the threshold,
   right-angle behavior, and exact zero-smoothing scalar identifications.
   `SingleCrossingMinimum` supplies the classical sufficient principle;
   actual log-ratio differentiation and normalized `N/(d-c)^2` monotonicity
   verify its hypotheses across positive smoothing. The old Schatten
   stationary-uniqueness proof now consumes this common principle too.
   `SmoothedPowerPhaseSelection.lean` and `SmoothedPowerPhaseEndpoints.lean`
   give the exact declarations. The main ambient consequence is
   `SmoothedPowerTransport.nonacuteDirectRotation_isMin_iff_principalAngles_critical`
   in `SmoothedPowerCanonicalCriterion.lean`: for the full closed finite
   complex family, canonical rotation is optimal iff every principal-angle
   cosine lies above the critical surface. This does not classify all optimizers.
3. **Completed:** C5's exact Hilbert-space family value and attainment.
   `SmoothedPowerTransport.exists_unitary_minimizing_transport_of_projection_cost_ne_top`
   in `SmoothedPowerGlobalAttainment.lean`, prefix
   `TauCeti.DavisKahan.InfiniteDimensional`, assumes complemented subspaces,
   finite family cost of the projection difference and balanced crossed
   defects. The native domain is Schatten-p at zero smoothing and
   Hilbert--Schmidt at positive smoothing. The theorem attains the intrinsic
   directed-angle sum and compares every ambient complex transporter, in
   arbitrary Hilbert dimension. The shared moving-target lower-bound lift
   also covers infinite costs. Every regular regime shares one finite active
   correction and canonical tail construction; only the nuclear corner uses
   the existing signed-root attainer. Feasibility over either field follows
   from the existing native restricted-unitary/index theorem. This does not
   classify every family optimizer or give a real planar formula.
4. **Audit completed:** the publication-core note checks the displayed
   hypotheses, field and ideal scope, value/classification distinctions and
   exact source mappings. The finite labelled-angle/intrinsic multiplicity
   equality remains an explicitly unformalized interface, used by no displayed
   core proof. Further classification, topology, stability and endpoint set
   limits are not publication gates. Historical priority remains qualified;
   original-source authentication questions are preserved in the provenance
   map. No further large proof campaign is part of this completed core.

The shared `UnitaryPhaseHessian` replaces the duplicated Schatten and
Charbonnier Hessian/overlap calculations. `UnitarySpectralRestriction` now
also replaces their duplicated classical two-phase restriction proofs.
`SmoothedPowerTransport.spectral_decomposition_of_isLocalMinOn_transports`
(prefix `TauCeti.DavisKahan.FiniteDimensional`, source `SmoothedPowerSpectralDecomposition.lean`)
constructs all actual paired blocks and the full kernel from ambient local
minimality; `SmoothedPowerFeasibleBlocks` certifies their feasible common
variation. C1a assumes no prescribed planes; C1b now proves the unrestricted
closed-family principal-angle minimum and an actual attainer. C2 and its
closed unrestricted canonical criterion are also proved. See T15–T18 in
the provenance map. T19/T20 now record the native domains, generic lifting
principle and full family Hilbert extension.

The proposed C² penalty-shape theorem has not been refuted, but is not yet
formally verified. The concrete family now has its own common proof and scalar minimum
principle and a proved ideal lift. The core audit is complete. Optional
topology, stability, or exhaustive real matching/endpoint-family extensions
require a separate research decision. The assessment contains
the dependency diagram, closest-source comparison and a proof-supported abstract.

## Current proved frontier

Throughout the Hilbert statements, the space is complete and the subspaces are
orthogonally complemented. Separability is not assumed. Defect balance means
an actual isometry between `halmosSourceDefect K L` and
`halmosTargetDefect K L`, or the finite-dimensional defect-dimension condition
in a theorem that constructs that isometry. Ambient unitary equivalence alone
does not imply feasibility with finite ideal displacement.

| Regime | Lean-verified scope | Starting evidence |
| --- | --- | --- |
| Complex full smoothed-power family, `1<=p<=2`, `tau>=0` | Exact intrinsic angle-sum value and finite-cost attainment in arbitrary complete Hilbert dimension iff projection cost is finite and crossed defects balance. Native domain: Schatten-p at zero smoothing, Hilbert--Schmidt at positive smoothing. Finite complex canonical optimality has the exact C2 critical surface. | `SmoothedPowerGlobalAttainment.lean`, `SmoothedPowerFeasibility.lean`, finite `SmoothedPowerCanonicalCriterion.lean`. |
| Complex `1<p<2`, finite dimension | Exact angle value, attainment, every optimizer, finite multiplicity/defect parameters, topology, thresholds and local-to-global. | `DavisKahan/FiniteDimensional/DirectRotation/SchattenGlobalAttainment.lean` and the classification/topology consumers. |
| Complex `1<p<2`, arbitrary Hilbert dimension | Native Schatten projection difference and balanced defects give exact attainment. Every optimizer is canonical on the inactive tail and differs by a finite active correction. Every optimizer has independent finite multiplicity-projection and defect-unitary coordinates. | `DavisKahan/InfiniteDimensional/DirectRotation/SchattenGlobalAttainment.lean`, `SchattenOptimizerClassification.lean`, `SchattenMultiplicityTopology.lean`. |
| Complex nuclear endpoint | Trace-class projection difference and balanced defects give exact attainment and a certificate for **every** optimizer. Complete independent signed-root and spectral-projection parameters are proved. | `DavisKahan/Geometry/Polar/NuclearOptimizerCertificate.lean`, `NuclearRootClassification.lean`, `NuclearRootSpectralFactors.lean`. |
| Complex nuclear optimizer topology | The entire displacement family is compact in every native Schatten-q carrier, `q>=1`. All optimizers have the same displacement Schatten profile. | `NuclearRootIdealCompactness.lean`, `NuclearRootProfile.lean`. |
| Complex Charbonnier, `tau>0` | Native Hilbert--Schmidt projection difference and defect balance give exact finite-cost feasibility/attainment. Complete optimizer classification, canonical tail, finite multiplicity topology and closed uniqueness threshold are proved. | `DavisKahan/InfiniteDimensional/DirectRotation/CharbonnierGlobalAttainment.lean`, `CharbonnierOptimizerClassification.lean`, `CharbonnierMultiplicityTopology.lean`, `CharbonnierUniquenessThreshold.lean`. |
| Real `1<=p<2`, finite dimension | Unrestricted matching value and attaining ambient orthogonal transporters are proved. Nuclear weights, field-equality parity and canonical-value criteria are proved. | `DavisKahan/FiniteDimensional/DirectRotation/RealNuclearMatching.lean`, `RealNuclearFieldEquality.lean`, `RealNuclearOptimality.lean`. |
| Real nuclear roots, compact Hilbert pairs | Exact numerical root-existence iff: every strictly acute sine eigenspace has real dimension divisible by four, equivalently even source-side multiplicity. Right-angle factors exist under defect balance. The constructed orthogonal transport attains the projection nuclear lower bound. In the trace-class case, every equality attainer is a signed root and parity is also necessary for equality attainment. | `NuclearRootSpectralFactors.lean`, `NuclearRealRootCriteria.lean`, donor `RealSpectralSignExistence.lean`. |
| Complex `p>=2` | Canonical transport gives a finite-cost global attainer under native Schatten difference and balanced defects. | Generic `InfiniteDimensional.exists_unitary_minimizing_schatten_transport_of_projection_sub_ne_top` in `SchattenGlobalAttainment.lean`. |

Finite-cost complex local-to-global is proved in both strict Schatten and
Charbonnier Hilbert theories (`SchattenLocalGlobal.lean`,
`CharbonnierLocalGlobal.lean`). Do not extend these conclusions to infinite-cost
local minima or the nuclear endpoint without another theorem. The unrestricted
real local-to-global analogue is already refuted by finite-dimensional examples.

Subcritical/critical data stability is also **already proved**:
`SchattenOptimizerDataStability.lean` handles changing both subspaces;
`SchattenCorrectionDataStability.lean` handles changing the input unitary.
The closed-critical constant is `p/(2-p)`. These bounds do not supply a global
objective-excess bound for arbitrary near-minimizers in nonunique regimes.

## Intrinsic nuclear description and the new spectral factors

Write `Delta=P_K-P_L`, `S=|Delta|`, `C=section3CosAngleOperator K L`,
`R=nonacuteDirectRotation K L D`, `J=K.reflection`, and
`V=nuclearTransportDual K L D`. The independent bounded-operator root is A:

- A is self-adjoint and `|A|=S`.
- A commutes with `V C`.
- `J A J = -A`.

The actual relative unitary is `Z=C+VA` and the transporter is `T=R Z*`.
`nuclearSignedSineEquivOptimizers_complex` gives literal inverse maps between
these roots and **all** ambient complex nuclear optimizers when Delta is trace
class. The root construction and its optimality are RCLike-generic:
`nuclearSignedSineTransport_nuclearENorm` and
`nuclearSignedSineTransport_isMin`. A real root therefore attains the projection
lower bound over real competitors. Existence of a real root is a separate issue.

For compact Delta, on every actual nonzero S-eigenspace `N_mu`, the root is

`A x = mu (2 P_mu x - x)`.

The independent local conditions are

`IsStarProjection P_mu`, `Commute P_mu (VC)_mu`,
`P_mu J_mu + J_mu P_mu = J_mu`.

The coefficients are actual invariant restrictions. The product of these local
spaces is homeomorphic to the entire root set in operator norm
(`exists_nuclearSignedSine_spectral_homeomorph`), and in the complex trace-class
case to the entire ambient optimizer set
(`exists_nuclear_optimizer_spectral_homeomorph_complex`). The zero eigenspace
has no free factor. At a right angle, the cosine is zero and its commutation
condition imposes no extra restriction. The local projection space has not yet
been reduced in Lean to a named Grassmannian or right-defect unitary group.

Generic donor proofs, in dependency order:

1. `ForTauCeti/Analysis/InnerProductSpace/SignedModulusProjection.lean`:
   unique supported sign projection, with no compactness assumption.
2. `SpectralProjectionFactors.lean`: arbitrary infinite projection-family
   assembly on the actual eigenspaces of a compact self-adjoint operator.
3. `CompactModulusFactors.lean`: full fixed-modulus root product homeomorphism.
4. `CompactModulusSymmetryFactors.lean`: exact local symmetry equations and
   independent constrained product homeomorphism.
5. `CompactModulusIdeal.lean` and
   `ForTauCeti/Analysis/OperatorIdeal/Family/SchattenConvergence.lean`:
   interlacing/dominated convergence and compactness in the accepted ideal norm.

These spectral and ideal-analysis foundations use classical mathematics. Their
formal implementation does not establish a historical-first claim.

## Completed structural real nuclear bridge

### Completed bridge: numerical real root existence

`TauCeti.exists_spectral_sign_projection_iff_four_dvd_finrank_real` now proves
the finite G/J-compatible projection iff, using an orthogonal complex structure
on the J-fixed half. All skew-adjointness, involution and anticommutation
hypotheses are retained. This is a classical linear-algebra construction.

For actual compact transport pairs, the following are now compiled in
`NuclearRealRootCriteria.lean` (namespace `TauCeti.DavisKahan`):

- `finrank_sine_eigenspace_eq_two_mul_source_side_real`: full nonzero sine
  dimension equals twice `dim_R(K ∩ N_s)`.
- `nuclearSignedSineSpectralFactors_nonempty_iff_four_dvd_real`: exact acute
  local solvability; `nuclearSignedSineSpectralFactors_nonempty_one_real`:
  unconditional right-angle factor under the stated defect completion.
- `nuclearSignedSineParameters_nonempty_iff_four_dvd_real` and
  `nuclearSignedSineParameters_nonempty_iff_even_source_multiplicity_real`:
  exact arbitrary-rank root existence by the existing independent product.
- `exists_real_nuclear_transport_of_sine_parity`: actual orthogonal transport
  attaining `||P-Q||_1`, with finite cost when Delta is trace class.

Zero sectors have no free root factor. The source-side multiplicity is an
actual eigenspace intersection, not yet a new compiled equality with the
finite `Nat.card` angle-count expression in the matching theorem. That literal
identification is a useful remaining corollary. No necessity assertion for
all real equality attainers follows merely from this root-existence iff.

### Completed: necessity of the real equality certificate

The trace-support proof and dual calibration now work over either field,
using the compact Gram trace identity and the accepted Hilbert--Schmidt
column API. `nuclear_eq_projection_sub_iff_certificate` characterizes every
actual finite-bound equality attainer. In `NuclearRootClassification.lean`,
`nuclear_eq_projection_sub_signed_sine_parameters` extracts its independent
root and `nuclearSignedSineEquivProjectionBoundAttainers` gives a literal
bijection with all equality attainers, real or complex.

For trace-class real Delta and D,
`exists_real_nuclear_transport_eq_projection_sub_iff_even_source_multiplicity`
is the exact arbitrary-rank equality-attainment criterion. The full sine
dimension version is `exists_real_nuclear_transport_eq_projection_sub_iff_four_dvd`.
`nuclear_projection_sub_lt_transport_of_sine_dimension_real` proves pointwise
strict cost when parity fails; it does not assert a uniform infimum gap.

### Secondary: real minimizers when the lower bound is unattainable

Finite real matching values and constructed attainers are already proved.
They do not classify all real minimizers. Analyze ties between matchings,
equal-angle mixing, both determinant classes and zero-gradient/reflection
blocks. Investigate the infinite-rank matching problem, including whether an
infimum matching is attained, tail convergence, and construction of an actual
orthogonal transporter. Quantitative field gaps should follow from established
classification/equality statements; earlier draft gap formulas are research
claims requiring counterexample tests.

## Secondary directions: connect exponent and smoothing regimes

The proposed explanation is the change in the optimizer's active spectrum:
for `1<p<2`, every optimizer has a finite active correction; at `p=1`, freedom
can occur on infinitely many nonzero angle blocks. Both endpoint structures
are proved; convergence of the **entire families** between them remains open.

Work first with trace-class Delta and balanced defects so the same pair has
finite cost across the endpoint comparison. Distinguish convergence of values,
limits of selected optimizers, and approximation of **every** endpoint optimizer.
A finite-dimensional closed-minimizer-graph theorem already exists in
`ForTauCeti/Analysis/InnerProductSpace/SchattenExponentContinuity.lean`; it does
not prove convergence of all infinite-dimensional optimizer sets.

There is now a compiled scalar obstruction at the quadratic right-angle
endpoint: `phasePower_two_right_angle` is flat, while
`not_tendsto_zero_of_right_angle_subquadratic_minimizers` excludes convergence
to its zero phase from exact subquadratic scalar minimizers. Both are in
`SchattenPhaseMinimum.lean`. Do not promote this to an ambient set-limit theorem
without the additional argument. The unification note derives a common scalar
logarithmic-curvature sufficient principle with compiled exact hypotheses;
finite-dimensional quantitative smoothing-value bounds remain conventional
claims. These are distinct from the proved value-continuity boundary argument.

Study `p downarrow 1`, `p uparrow 2` and the appropriate Charbonnier limit.
Specify whether the cost is a norm or its p-th power. At defects or thresholds,
endpoint families can have additional freedom, so do not assume every endpoint
optimizer is approximable from an open exponent range. Use ideal-norm compactness
where its hypotheses actually apply. Check normalization and the ideal dictated
by Charbonnier's quadratic behavior near zero.

## Secondary directions: geometry, stability and an application

Reduce the nuclear local factors to complex Grassmannians on acute phase halves,
right-defect unitary factors, and their real counterparts. Prove connectedness
before identifying rank strata with connected components. Derive dimensions,
component counts and uniqueness statements at the exact supported scope.
Strict-exponent and Charbonnier multiplicity homeomorphisms already exist;
do not restart their construction.

Extend existing stability into the nonunique regimes using distance to the
**whole optimizer set**. Identify the correct ideal topology and distinguish
data perturbations from objective excess. Critical planar quartic growth and
failure of quadratic growth are proved; a positive growth estimate for every
ambient near-minimizer is a separate target. Singular-value sequence identities
are stronger claims than the already proved Schatten-moment profiles.

A useful application target is finite spectral reconstruction from approximate
subspace data, with explicit feasibility error, objective error and distance to
the optimizer family. Nearest commuting-unitary correction and its canonical
stability are existing foundations. A full algorithmic guarantee must justify
how computed data and truncation errors enter the theorem. No experimental,
statistical or physical-implementation guarantee has been established here.

After these results, consider one spectral-penalty theorem with explicit shape
and ideal assumptions that explains the successful regimes and their failures.
Avoid replacing completed concrete mathematics with an unfinished abstraction.

## Novelty and publication boundaries

Read [the archived supplied review](historical-priority-review-2026-10-26.md)
and the [novelty record](../papers/dk_formalization_journal/MATHEMATICAL_NOVELTY_REVIEW_2026-10-24.md)
before searching again. The ambient objective, phase-improvement mechanism,
Q-norm canonical regime and projection-index obstruction have historical
precedents. The review found no equivalent real matching/parity or complete
intermediate-exponent classification in its examined sources; that is qualified
negative evidence. Newly completed infinite-dimensional and nuclear optimizer
theorems require further theorem-level comparison. The attributed Aubrun--Szarek
Exercise B.12 lead still has a printed-edition authentication limitation.

The proved publication core is: full-family complex values and attainment,
phase transitions, exact ideal feasibility, nuclear equality certificates and
real compatibility, with hypotheses explicit. Existing optimizer classifications
and selected correction consequences support it at their stated regimes;
classifying every optimizer for every family member is not a completion gate. More Lean declarations alone do not
establish historical priority. Keep compiled theorems, conventional proofs,
conjectures, and refuted statements distinct. The 29-result Davis--Kahan source
inventory is unchanged by this independent research program.

## Reproduce and resume on another machine

The current C5 full default build passed **21,495 jobs**, warnings as errors;
log `/tmp/dkps-unification/family-hilbert-core-full.log`. Its focused target
passed 7,544 jobs. Ordinary Lake builds do not
require coordination submodules. Do not transfer `.lake` as source or depend on
old `/tmp` logs. The real parity-converse campaign's full default build passed
**21,427 jobs**, with warnings as errors, after consuming Tau Ceti's dimension
necessity and retiring the local copy. The earlier spectral-factor checkpoint
was `96aeb922d` (21,413 jobs); ideal compactness was `395d6dd0f` (21,399 jobs).

Pinned inputs: Lean `v4.36.0-rc1`, Tau Ceti
`b3de655482f7b86c77d8982566e5a73801fd64fa`, Mathlib
`2cabef97b63d3275776b8b060d802de6a6fa1055`.
`lakefile.toml`, `lake-manifest.json` and `lean-toolchain` are authoritative.

At handoff the local tracking ref `origin/main` was
`fb0298d7d8f1404c0f194174fe3ade94e73ed386`; main was 124 commits ahead before
these documentation updates. This is local-ref information, not a fresh remote
poll. For transfer, use a self-contained Git bundle named
`dkps-schatten-research-2026-10-27.bundle`, generated outside the repository
with the commands below. Its advertised main ref, inspected with `git bundle list-heads`,
identifies the exact included checkpoint. A remote clone alone may omit the
recent mathematics until main is pushed or the bundle is fetched.

On the source machine, after all handoff commits:

```bash
git bundle create /tmp/dkps-schatten-research-2026-10-27.bundle main
git bundle verify /tmp/dkps-schatten-research-2026-10-27.bundle
git bundle list-heads /tmp/dkps-schatten-research-2026-10-27.bundle
```

After copying that bundle to the new machine:

```bash
git clone /path/to/dkps-schatten-research-2026-10-27.bundle aiq-dkps-formalization
cd aiq-dkps-formalization
git remote set-url origin <normal-authenticated-repository-url>
python3 .llm_resource_tally/tool install
lake exe cache get
lake build
```

Read `AGENTS.md`, this plan, and
`dev/lean-proof-engineering-lessons.md` before editing. Work on main with one
agent. Use accepted Tau Ceti/Mathlib APIs directly and retain only unmerged
foundations in ForTauCeti. Before **each** focused or full build, retrieve the
cache. Useful focused target:

```bash
lake exe cache get
lake build DavisKahan.Geometry.Polar.NuclearRealRootCriteria
```

This builds the current root, spectral-factor and real-obstruction dependencies.
Keep successful build logs quiet. Commit a green logical milestone promptly,
include the exact model attribution, and publish resource accounting before
handoff. No new checker machinery is required. For virtiofs guests, follow the
existing local-ext4 Lake-cache instructions in AGENTS.md. The old host had very
little free disk space; this is an environment constraint rather than a theorem
obstruction.

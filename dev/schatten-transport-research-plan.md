# Spectral subspace transport: current research plan

Updated 27 October 2026. Mathematical checkpoint: `96aeb922d`; accounting
checkpoint: `2b481b94d`. This document was reconciled with the Lean declarations
at that HEAD. Subsequent documentation commits do not change that mathematics.

Start here on a new machine. The
[dated research handoff](schatten-research-handoff-2026-10-26.md) contains the
long proof history and implementation details. Its dated entries retain their
original status; this plan and its current-frontier summary take precedence.
[Paper context](../papers/dk_formalization_journal/PAPER_CONTEXT.md) separates
compiled mathematics from manuscript integration. Manuscript and visualization
changes remain assigned separately.

## Objective and a useful completion boundary

Develop exact extrinsic transport optimization over **every** unitary or
orthogonal W taking K to L, with objective `||I-W||_p` or an explicitly specified
spectral penalty. The intended theory explains the minimum, every optimizer,
field dependence, phase transitions, infinite-dimensional feasibility, and a
useful correction construction. Path length, matrix-logarithm distance, and
frame-fitting Procrustes problems have different objectives or constraints.

The complex theory already has exact infinite-dimensional strict-exponent and
smoothed classifications and the complete nuclear certificate. The largest
remaining mathematical gap is the real classification. A journal contribution
can have a precise, complete scope before every extension below is solved.
Historical originality requires its own theorem-level literature comparison.

## Current proved frontier

Throughout the Hilbert statements, the space is complete and the subspaces are
orthogonally complemented. Separability is not assumed. Defect balance means
an actual isometry between `halmosSourceDefect K L` and
`halmosTargetDefect K L`, or the finite-dimensional defect-dimension condition
in a theorem that constructs that isometry. Ambient unitary equivalence alone
does not imply feasibility with finite ideal displacement.

| Regime | Lean-verified scope | Starting evidence |
| --- | --- | --- |
| Complex `1<p<2`, finite dimension | Exact angle value, attainment, every optimizer, finite multiplicity/defect parameters, topology, thresholds and local-to-global. | `DavisKahan/FiniteDimensional/DirectRotation/SchattenGlobalAttainment.lean` and the classification/topology consumers. |
| Complex `1<p<2`, arbitrary Hilbert dimension | Native Schatten projection difference and balanced defects give exact attainment. Every optimizer is canonical on the inactive tail and differs by a finite active correction. Every optimizer has independent finite multiplicity-projection and defect-unitary coordinates. | `DavisKahan/InfiniteDimensional/DirectRotation/SchattenGlobalAttainment.lean`, `SchattenOptimizerClassification.lean`, `SchattenMultiplicityTopology.lean`. |
| Complex nuclear endpoint | Trace-class projection difference and balanced defects give exact attainment and a certificate for **every** optimizer. Complete independent signed-root and spectral-projection parameters are proved. | `DavisKahan/Geometry/Polar/NuclearOptimizerCertificate.lean`, `NuclearRootClassification.lean`, `NuclearRootSpectralFactors.lean`. |
| Complex nuclear optimizer topology | The entire displacement family is compact in every native Schatten-q carrier, `q>=1`. All optimizers have the same displacement Schatten profile. | `NuclearRootIdealCompactness.lean`, `NuclearRootProfile.lean`. |
| Complex Charbonnier, `tau>0` | Native Hilbert--Schmidt projection difference and defect balance give exact finite-cost feasibility/attainment. Complete optimizer classification, canonical tail, finite multiplicity topology and closed uniqueness threshold are proved. | `DavisKahan/InfiniteDimensional/DirectRotation/CharbonnierGlobalAttainment.lean`, `CharbonnierOptimizerClassification.lean`, `CharbonnierMultiplicityTopology.lean`, `CharbonnierUniquenessThreshold.lean`. |
| Real `1<=p<2`, finite dimension | Unrestricted matching value and attaining ambient orthogonal transporters are proved. Nuclear weights, field-equality parity and canonical-value criteria are proved. | `DavisKahan/FiniteDimensional/DirectRotation/RealNuclearMatching.lean`, `RealNuclearFieldEquality.lean`, `RealNuclearOptimality.lean`. |
| Real nuclear roots, compact Hilbert pairs | Exact equivalence between global root existence and independent local projection solvability. Every strictly acute sine eigenspace must have real dimension divisible by four. | `NuclearRootSpectralFactors.lean`, `NuclearRealRootCriteria.lean`. |
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

## First priority: close the real theory

### 1. Prove sufficiency of the local numerical parity test

Already compiled:
`nuclear_spectral_phase_square` gives `(VC)^2=(s^2-1)I` on `N_s`.
For real `0<s<1`, a compatible projection has even rank, and reflection exchanges
its range and kernel. Thus `4 | finrank_R N_s` is necessary for any real root
(`nuclearSignedSineParameters_four_dvd_sine_eigenspace_real`).

**Next precise lemma to prove:** in a finite real Hilbert block, let G be
skew-adjoint with `G^2=-c^2 I`, `c>0`; let J be a self-adjoint orthogonal
involution anticommuting with G. Prove existence of an orthogonal projection P
with `Commute P G` and `P J+J P=J` iff the real block dimension is divisible by
four. Necessity is compiled in `RealSpectralSignObstruction.lean`; sufficiency
still needs proof. Retain all the stated G/J hypotheses when testing it.

A route to investigate: identify the J-fixed half-space M, prove G exchanges
the two J eigenspaces, identify the block with `M (+) M`, and construct a local
factor from an orthogonal complex structure on M. The existing
`AlmostComplexStructure.exists_skew_unitary_iff_even_finrank_real` supplies the
exact even-dimension criterion on M. This route is proposed, not compiled.

Then prove the half-dimension identification for actual principal-side angle
spaces; `4 | dim_R N_s` should become even principal-angle multiplicity. Handle
`s=1` separately: right-angle factors should exist under defect balance without
this parity restriction. Assemble all factors with the **already proved**
`nuclearSignedSineParameters_nonempty_iff_spectral_factors`. No new infinite
spectral-sum construction is needed.

### 2. Prove necessity of the real equality certificate

The complex trace argument gives every complex nuclear optimizer's signed root.
It has not yet proved that every **real** transporter attaining `||Delta||_1`
has that structure. Establish the real equality case directly or by a justified
complexification preserving the required ideals, costs and transport data.
Do not infer it from generic root sufficiency or finite matching value equality.

Together with the parity converse this would give an arbitrary-rank real
criterion for attaining the complex/projection lower bound and classify all
such real attainers.

### 3. Classify every real minimizer when the lower bound is unattainable

Finite real matching values and constructed attainers are already proved.
They do not classify all real minimizers. Analyze ties between matchings,
equal-angle mixing, both determinant classes and zero-gradient/reflection
blocks. Investigate the infinite-rank matching problem, including whether an
infimum matching is attained, tail convergence, and construction of an actual
orthogonal transporter. Quantitative field gaps should follow from established
classification/equality statements; earlier draft gap formulas are research
claims requiring counterexample tests.

## Second priority: connect exponent and smoothing regimes

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

Study `p downarrow 1`, `p uparrow 2` and the appropriate Charbonnier limit.
Specify whether the cost is a norm or its p-th power. At defects or thresholds,
endpoint families can have additional freedom, so do not assume every endpoint
optimizer is approximable from an open exponent range. Use ideal-norm compactness
where its hypotheses actually apply. Check normalization and the ideal dictated
by Charbonnier's quadratic behavior near zero.

## Third priority: explicit geometry, stability and one certified application

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

The theorem package sought is: exact values, every optimizer, field dependence,
endpoint transitions and one quantitative correction consequence, with all
feasibility and ideal hypotheses explicit. More Lean declarations alone do not
establish historical priority. Keep compiled theorems, conventional proofs,
conjectures, and refuted statements distinct. The 29-result Davis--Kahan source
inventory is unchanged by this independent research program.

## Reproduce and resume on another machine

Everything mathematically required is committed. Ordinary Lake builds do not
require coordination submodules. Do not transfer `.lake` as source or depend on
old `/tmp` logs. The last mathematical full default build passed **21,413 jobs**
with warnings as errors; checkpoint `96aeb922d`. The preceding ideal-compactness
checkpoint is `395d6dd0f` (21,399-job full build).

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

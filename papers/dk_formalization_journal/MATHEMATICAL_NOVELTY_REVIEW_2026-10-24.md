# Mathematical novelty review: Davis--Kahan and spectral-penalty transport

**Research record, not manuscript prose.** 24 October 2026. Repository snapshot:
`b251994524e7f4a5145f3a045b757cad30c6dbf9` (source archive dated
2026-10-24 08:51). Scope: the Davis--Kahan formalization and subsequent
finite-dimensional subspace-transport optimization program. **YWS is excluded**;
its source investigation and conference stub live in
`../yws_formalization_conference/`.

**Question:** What has the project established that could be an original
mathematical result, as opposed to a formalization achievement, an explicit
correction of a printed statement, or a consequence of standard projection
and matrix geometry?

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
| SM-5 | Complete classification of all smoothed optimizers, and broad spectral-penalty single-peak extension | Conventional drafts in `smoothed_transport.tex`, `spectral_penalty_transport.tex` | **Not yet formalized**. For classification distinguish strict subcritical, threshold, supercritical multiplicities, and right-angle defects |
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

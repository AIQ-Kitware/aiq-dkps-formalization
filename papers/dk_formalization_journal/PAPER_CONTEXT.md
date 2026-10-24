# Paper context: established claims, boundaries, and editorial decisions

**As of:** 24 October 2026
**Inspected source snapshot:** `b00c5c8c35e1aab826064285c530260fd558da9b` for the source-facing claims below; subsequent Schatten research is recorded separately in this file.
**Paper:** *Formalizing the Davis--Kahan Perturbation Theorems in Lean*  
**Scope of this record:** working context for authors and future manuscript agents. This is deliberately **not** an appendix or a source of text to paste into the paper.

The Yu--Wang--Samworth source-version audit and manuscript fragments are in
`../yws_formalization_conference/`; this paper covers Davis--Kahan.

Start here when updating `paper.tex`. The fact that an assertion appears in an old draft, a development note, or a prior agent's answer does not make it current. Follow the evidence links below and preserve differences between source claims, Lean-verified statements, and mathematical arguments outside Lean.

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
  inferred from trace optimality.
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
problem requires a globally unitary operator. Do not claim an improvement of
their final theorem by comparing against the older author's PDF: the 2016
PDF has a `6 epsilon/Delta` bound that v3 replaced. The current relevance is
an exact optimization formulation with a stronger global-unitarity constraint,
not a claimed replacement of their ground-space result.

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

The conventional draft also describes all acute minimizing transporters:
on the multiplicity space of each supercritical angle they are the canonical
rotation times `exp(i delta(theta) S)`, with `S` any self-adjoint unitary.
The resulting families are disjoint unions of complex Grassmannians; for
distinct positive angles there are exactly `2^k` minimizers when exactly
`k` angles are supercritical. Uniqueness is equivalent to every angle being
at most the cutoff. This characterization uses the unformalized higher-rank
block argument and is not a new compiled result.

- Main file: `paper.tex`; optional red-framed working variant: `paper_working.tex` (sets `DKWorkingDraft`).
- Mathematical text built by the manuscript: `counterexample.tex`, `sharp_displacement.tex`. The all-pairs complex theorem is now in the checked manuscript. The only red-framed provisional theorem is the **real** line/hyperplane result, gated by `includeUnformalizedRealTransport` in `paper_working.tex`. The old `sharp_displacement_unformalized.tex` is a retired conventional proof note, not included in either manuscript. `sharp_displacement_verified.tex` is also an older detailed record.
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

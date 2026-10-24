# Journal claims to evidence

This file maps the principal claims in `paper.tex` to current repository
evidence. Read `PAPER_CONTEXT.md` for the publication boundaries. The YWS source audit
is in `../yws_formalization_conference/`. This journal manuscript concerns
Davis--Kahan.

| Manuscript claim | Evidence | Qualification |
|---|---|---|
| The maintained Davis--Kahan inventory has 29 source targets. | `dev/davis-kahan-1970-formalization-result-inventory.json` | Count the inventory rows, not source files or Lean declarations. |
| All 29 targets are verified in the current build. | Same inventory: `verification = proved_in_build` for every row. | This is kernel/build verification of the associated formal statements. |
| All 29 targets have accepted semantic/source-correspondence review. | Same inventory: `semantic_certification = accepted` for every row; supporting audits under `DavisKahan/Sources/DavisKahan1970/Audits/`. | Semantic review is a separate claim from kernel acceptance. |
| 28 Davis--Kahan targets are proved at reviewed source scope and Proposition 4.4 is refuted as printed. | Same inventory: 28 `disposition = proved_exact`; `DK-4.4-prop` has `disposition = refuted_as_transcribed`. | Do not summarize this as “29 theorems proved.” |
| The selected sine-theta theorem covers the real/complex, unbounded, unitarily invariant norm formulation with finite and ordered half-infinite form-gap alternatives. | `DavisKahan/Sources/DavisKahan1970/SineTheta/Presentation.lean`, theorem `sinTheta_unbounded_formGap_whereDefinedUIN_rclike`; related definitions in the same source layer. | Describe only the hypotheses actually encoded. In particular, do not claim extra domain generality from the forward-inclusion formulation alone. |
| The selected Lean sine-theta theorem is stated on a positive trial-coordinate `sin Theta0` operator, and its rectangular Sylvester representative has exactly that operator as its modulus. | `DavisKahan/Sources/DavisKahan1970/SineTheta/Presentation.lean`: `sourceDirectedSinThetaOperator`, `sourceDirectedSinThetaOperator_eq_modulus`, and `sinTheta_unbounded_formGap_whereDefinedUIN_rclike`; supporting review in `papers/dk_formalization_workshop/notes/SINE_THETA_NORM_SOURCE_REVIEW.md`. | Keep the operator types distinct: the rectangular block maps trial coordinates into the ambient space, while the positive sine is an endomorphism of trial coordinates. |
| Davis--Kahan Proposition 4.4 is false for every positive acute principal angle; every proposed positive angle cutoff is contradicted by an explicit real 4D pair. | `ShortRotationCounterexample.lean`; `SmallAngleCounterexample.lean`; `Section4SmallAngle.lean`, `arbitrarilySmall_fullDisplacement_refuted`. | The fixed `pi/4` example is a special case; the parameterized family is user-confirmed compiled. Phase adjustment itself occurs in Davis--Kahan Example 4.2. |
| The printed proof of Proposition 4.4 uses an invalid full-displacement norm step. | `ShortRotationCounterexample.lean` and the source-review material surrounding Section 4. | State the failed inequality concretely rather than merely saying the proof has a gap. |
| A Q-norm version of the Proposition 4.4 conclusion is valid. | `DavisKahan/FiniteDimensional/DirectRotation/QNorm.lean`, including `IsQNorm` and `directRotation_fullDisplacement_qnorm`. | Do not automatically identify this formal class with every commonly named norm family unless separately proved/cited. |
| The formalization required reusable operator-theoretic foundations beyond the paper-specific statements. | `ForTauCeti/` and Davis--Kahan foundation layers, including partial/unbounded operators, spectral/form-gap machinery, symmetric operator ideals, principal-angle/direct-rotation geometry, and Sylvester results. | Discuss mathematical capabilities, not raw module counts, unless a fresh reproducible census is provided. |
| AI assisted the formalization and prose preparation. | Repository/model provenance and the explicit disclosure in `paper.tex` and `appendix_process.tex`. | No learning-effectiveness or workflow-effectiveness claim is made. |

## Claims deliberately removed from the journal manuscript

The following evidence may remain in the repository for other papers or
historical analysis, but it should not be used to expand this journal article's
contribution statement:

- downstream application-project coverage;
- token/resource accounting and cost extrapolation;
- model/co-author provenance as an empirical result;
- practitioner surveys or human--LLM workflow taxonomy; and
- broad process-study conclusions from the workshop paper.

The journal manuscript retains an explicit disclosure that AI models contributed
to proof development and drafted or edited prose. The author's learning
trajectory is not a mathematical contribution of this paper.

The workshop paper is still a useful source of editorial improvements, especially
its explicit separation of formal verification from source correspondence.

## Additional small-angle result (outside the 29-target source inventory)

| Claim | Evidence | Status in this revision |
|---|---|---|
| For every 0 < theta < pi/2 the two principal angles equal theta. | `counterexample.tex`, target frame and projection calculation; `SmallAngleCounterexample.principalAngles_eq`. | Conventional proof and compiled Lean theorem; see submission/VALIDATION.md. |
| The canonical direct displacement has trace norm 8 sin(theta/2); the competitor has 4 sin(theta). | `counterexample.tex`, polar-factor identification and singular-value lists. Lean lemmas `kyFanSum_displacement_R`, `kyFanSum_displacement_W` use the equivalent square-root form for the former. | Conventional proof, symbolic checks, and compiled Lean singular-value/trace lemmas. |
| No positive largest-angle threshold repairs Proposition 4.4. | Mathematical corollary in `counterexample.tex`; `arbitrarilySmall_fullDisplacement_refuted`; source-facing alias in `Section4SmallAngle.lean`. | New result, separately tracked. Do not add a thirtieth historical source target. |
| The 2005 Grassmann-space paper repeats the pi/3 extremal assertion. | Qiu--Zhang--Li, Section 5, item 3; `submission/LITERATURE_AUDIT.md`. | Particular item verified from author-uploaded text; no claim against the main metric theorems. |
| General norm-class limitations and Q-norm minimization predate this work. | Bolotnikov--Li--Rodman (2001), Theorem 3.1 and Lemma 3.3. | Explicit prior art; no new Q-norm principle or first-discovery claim. |

## Additional displacement estimates and working-draft consequences

| Claim | Evidence | Status |
|---|---|---|
| For every admissible orthogonal/unitary `W`, `N(P_U-P_V) ≤ N(I-W)` in every finite-dimensional real/complex inner-product space, for every unitarily invariant seminorm `N`. | `DavisKahan/FiniteDimensional/DirectRotation/ProjectionDisplacement.lean`, theorem `projectionDifference_uiNorm_le_displacement` and Ky Fan corollary. | Compiled and confirmed by the user on 23 October 2026. No acute restriction. |
| For every `0 < theta < pi/2`, the real witness satisfies `cos(theta/2) * ‖I-R_theta‖₁ = ‖I-W_theta‖₁`. | `DavisKahan/FiniteDimensional/DirectRotation/TraceRatio.lean`, theorem `SmallAngleCounterexample.cos_half_mul_directTrace_eq_competitorTrace`. | Compiled and confirmed by the user on 23 October 2026. This identity alone does not prove global optimality. |
| The real four-dimensional projection difference has trace norm `4 sin(theta)`; `Wequiv theta` attains the global minimum. | `DavisKahan/FiniteDimensional/DirectRotation/TraceOptimality.lean`: `SmallAngleCounterexample.kyFanSum_projectionDifference` and `SmallAngleCounterexample.exists_traceMinimizer`. | Compiled and confirmed by the user, 23 October 2026. |
| For all finite-dimensional real/complex acute pairs, all UI seminorms and all admissible competitors, `cos(alpha/2) N(I-R) ≤ N(I-W)`. | `DavisKahan/FiniteDimensional/DirectRotation/SharpDisplacement.lean`: `cos_half_mul_uiNorm_directRotation_le_projection`, `cos_half_maxPrincipalAngle_mul_uiNorm_directRotation_le_displacement`. | Compiled and confirmed. |
| At every positive acute angle the multiplicative factor `sec(alpha/2)` is necessary; the common factor on `alpha ≤ pi/3` is `2/sqrt(3)`. | `SharpDisplacement.lean`: `SmallAngleCounterexample.fixedAngle_sharpFactor_attained`, `factor_necessary_at_fixedAngle`, `pi_div_three_common_factor_necessary`, `uiNorm_directRotation_le_two_div_sqrt_three_mul_displacement`. | Compiled and confirmed. |
| For every acute pair, `sqrt(2)` is a valid UI-seminorm displacement factor. No smaller uniform constant suffices by approaching the right-angle endpoint. | `SharpDisplacement.lean`: `uiNorm_directRotation_le_sqrt_two_mul_displacement` and fixed-angle necessity; analytic limit in `sharp_displacement_verified.tex`; new focused declaration `SmallAngleCounterexample.sqrt_two_common_factor_necessary` in `SharpDisplacementLimit.lean`. | Uniform bound compiled and confirmed. The limit theorem is an additional source implementation awaiting a focused build. |
| The phase-modified complex two-dimensional unitary attains trace displacement equal to projector distance, including right angles. | `ComplexTraceOptimality.lean`: `phaseUnitary_global_trace_minimizer`. | Compiled and confirmed. |
| Full trace is additive under orthogonal operator block sums; every finite principal-plane model with unchanged summand admits an attained global trace minimum; unitary coordinate transport preserves this equality. | `ForTauCeti/.../BlockTrace.lean`, `ComplexTraceAssembly.lean`, `ComplexTraceFiniteModel.lean`: `phasePlaneModel_global_trace_minimizer`, `phasePlaneModel_with_fixed_global_trace_minimizer`, `AttainsProjectionTraceBound.conjugate`. | Compiled and confirmed. |
| For **any** two finite-dimensional real/complex projections, without equal-rank or acute-angle assumptions, `‖P_U-P_V‖₁=‖P_(Vperp) P_U‖₁+‖P_(Uperp) P_V‖₁`; furthermore their positive moduli split on orthogonal supports. | `ForTauCeti/Analysis/InnerProductSpace/Projection/TraceSine.lean`: `projectionDifference_sq_eq_directed_gram_sum`, `operatorAbs_projectionDifference_eq_directed_sine_sum`, `kyFanSum_projectionDifference_eq_directed_sines`. | Lean theorem present in the `b00c5c8` source snapshot; the author's updated formalization includes this theorem. Applies to the ambient full Ky Fan sum, not arbitrary infinite-dimensional operators. |
| Every finite-dimensional equal-rank **complex** subspace pair, without any acuteness or supplied-coordinate hypothesis, has a global trace minimizer with `‖I-W‖₁=‖P_U-P_V‖₁=2 sum sin(theta_j)`; every admissible competitor has at least this displacement. | `DavisKahan/FiniteDimensional/DirectRotation/ComplexPhaseTrace.lean`: `exists_global_complex_trace_minimizer`; `ComplexCrossedDefects.lean`: `crossedDefectsEquivalent_of_finrank_eq`; `ComplexTracePrincipalAngles.lean`: `kyFanSum_projectionDifference_eq_two_sum_sin_principalAngles`, `exists_global_complex_trace_minimizer_with_principalAngles`. The all-pairs phase proof is independent of any supplied principal-plane model. | **Formalized unconditionally in the current source snapshot**. All-minimizers classification, real all-pairs optimum, and infinite-dimensional trace-ideal variants remain separate questions. |

`paper.tex` includes `sharp_displacement.tex`, which now states and proves
the exact complex all-pairs trace optimum and directed-sine decomposition
in the checked manuscript. The only provisional switch is
`\includeUnformalizedRealTransportfalse`; `paper_working.tex` enables the
red-framed real rank-one/hyperplane theorem. The full complex theorem is no
longer provisional. The historical Davis--Kahan source-result inventory remains 29.

The axiom/interface audit is
`DavisKahan/Sources/DavisKahan1970/Audits/SmallAngleCounterexample.lean`.
The user-reported 23 October 2026 compilation of the three targeted modules is recorded in `submission/VALIDATION.md`.

## Schatten optimization research extension (24 October 2026)

These results are additional research, outside the 29 historical source targets.
The conventional extension draft `schatten_optimization.tex` is not included by
`paper.tex`.

| Claim | Evidence | Status and boundary |
|---|---|---|
| For `1 < p < 2` and an acute positive principal angle, the canonical phase is the unique global scalar-phase minimizer exactly when `p cos(theta) >= 2-p`, including equality. Above that threshold the unique minimizing phase is interior and satisfies the stationary-amplitude equation. | `SchattenPhaseTransition.lean`: `canonical_phase_unique_min_of_subcritical`, `exists_unique_phase_minimizer_of_supercritical`, `canonical_phase_isMinOn_iff`. | Compiled in the direct-rotation aggregate. This optimizes the closed scalar interval `[0, theta]`; it does not by itself exclude other unitary transports. |
| The attained scalar minimum is nonnegative, equals `2^p` at a right angle, and bounds the canonical power sum by the factor `2^(1-p/2)`, with right-angle equality. | `SchattenPhaseMinimum.lean`: `exists_attains_phaseMinimum`, `phaseMinimum_right_angle`, `canonical_phase_power_le_factor_mul_minimum`, `canonical_phase_power_eq_factor_right_angle`. | Compiled for the stated exponent ranges. A global matrix comparison needs the unrestricted reduction separately. |
| For finite Schatten exponents at least one, every physical planar angle has an admissible bundled complex unitary attaining the scalar minimum, whose actual Schatten norm is the corresponding `p`-th root. | `SchattenPhaseTransport.lean`: `scalarPhaseTransport_transports`, `scalarPhaseTransport_schatten`, `exists_scalarPhaseTransport_minimizer`. | Compiled using the accepted Tau Ceti Schatten seminorm. Minimality is within the scalar-phase family. |
| For arbitrary equal-rank complex projections, the unrestricted minimum power sum is the sum of the independent scalar minima over their principal angles. | `schatten_optimization.tex`, Theorem `thm:schatten-independent-planes`, using the spectral first variation and the negative second variation in Proposition `prop:schatten-no-mixing`. | Conventional proof draft under review; not Lean-certified. Do not describe the matrix reduction or its global corollaries as formally proved. |
| The optimizing phase has square-root onset, and the minimum value is continuously differentiable but not twice differentiable at the exponent-dependent acute transition. | `schatten_optimization.tex`, equation `eq:schatten-transition-asymptotics`. | Conventional asymptotic argument under review; not Lean-certified. |
| The exact interior-angle classification and unrestricted reduction are plausible candidates for mathematical novelty. | Primary-source comparisons recorded in `PAPER_CONTEXT.md`; Bolotnikov--Li--Rodman (2001) is the closest identified prior work. | Provisional assessment. Failed searches do not establish priority; the phase mechanism, right-angle failure, Q-norm theory, spectral derivative, and projection decomposition are prior art. |

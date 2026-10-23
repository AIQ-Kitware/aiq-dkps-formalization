# Journal claims to evidence

This file maps the principal claims in `paper.tex` to current repository
evidence. It is deliberately narrower than the historical draft2 accounting
notes: this journal manuscript is about Davis--Kahan, with YWS as a secondary
application/audit case.

| Manuscript claim | Evidence | Qualification |
|---|---|---|
| The maintained Davis--Kahan inventory has 29 source targets. | `dev/davis-kahan-1970-formalization-result-inventory.json` | Count the inventory rows, not source files or Lean declarations. |
| All 29 targets are verified in the current build. | Same inventory: `verification = proved_in_build` for every row. | This is kernel/build verification of the associated formal statements. |
| All 29 targets have accepted semantic/source-correspondence review. | Same inventory: `semantic_certification = accepted` for every row; supporting audits under `DavisKahan/Sources/DavisKahan1970/Audits/`. | Semantic review is a separate claim from kernel acceptance. |
| 28 Davis--Kahan targets are proved at reviewed source scope and Proposition 4.4 is refuted as printed. | Same inventory: 28 `disposition = proved_exact`; `DK-4.4-prop` has `disposition = refuted_as_transcribed`. | Do not summarize this as “29 theorems proved.” |
| The selected sine-theta theorem covers the real/complex, unbounded, unitarily invariant norm formulation with finite and ordered half-infinite form-gap alternatives. | `DavisKahan/Sources/DavisKahan1970/SineTheta/Presentation.lean`, theorem `sinTheta_unbounded_formGap_whereDefinedUIN_rclike`; related definitions in the same source layer. | Describe only the hypotheses actually encoded. In particular, do not claim extra domain generality from the forward-inclusion formulation alone. |
| The selected Lean sine-theta theorem is stated on a positive trial-coordinate `sin Theta0` operator, and its rectangular Sylvester representative has exactly that operator as its modulus. | `DavisKahan/Sources/DavisKahan1970/SineTheta/Presentation.lean`: `sourceDirectedSinThetaOperator`, `sourceDirectedSinThetaOperator_eq_modulus`, and `sinTheta_unbounded_formGap_whereDefinedUIN_rclike`; supporting review in `papers/dk_formalization_workshop/notes/SINE_THETA_NORM_SOURCE_REVIEW.md`. | Keep the operator types distinct: the rectangular block maps trial coordinates into the ambient space, while the positive sine is an endomorphism of trial coordinates. |
| Davis--Kahan Proposition 4.4 is false as printed. | `DavisKahan/Sources/DavisKahan1970/Section4.lean`; `DavisKahan/FiniteDimensional/DirectRotation/ShortRotationCounterexample.lean`. | The formal witness is four-dimensional and uses principal angle `pi/4`. |
| The printed proof of Proposition 4.4 uses an invalid full-displacement norm step. | `ShortRotationCounterexample.lean` and the source-review material surrounding Section 4. | State the failed inequality concretely rather than merely saying the proof has a gap. |
| A Q-norm version of the Proposition 4.4 conclusion is valid. | `DavisKahan/FiniteDimensional/DirectRotation/QNorm.lean`, including `IsQNorm` and `directRotation_fullDisplacement_qnorm`. | Do not automatically identify this formal class with every commonly named norm family unless separately proved/cited. |
| The formalization required reusable operator-theoretic foundations beyond the paper-specific statements. | `ForTauCeti/` and Davis--Kahan foundation layers, including partial/unbounded operators, spectral/form-gap machinery, symmetric operator ideals, principal-angle/direct-rotation geometry, and Sylvester results. | Discuss mathematical capabilities, not raw module counts, unless a fresh reproducible census is provided. |
| YWS is a downstream statistical specialization supported by its own Lean layer. | `YuWangSamworth2015/YuWangSamworth2015/CitationSurface.lean`, theorem modules under `Symmetric/` and `Rectangular/`. | YWS is secondary in this journal manuscript. |
| The YWS source audit found two printed defects. | `YuWangSamworth2015/` audit/grounding files and machine-checked correction/refutation declarations. | The defects are equation (4)'s missing square and Theorem 3's rank-boundary convention. |
| The current YWS census has 24 tracking entries: 22 printed-source entries and 2 explicit additions; all 24 are verified and 7 rows use corrected statements. | `snapshots/census_macros.tex` and the underlying YWS census generator/source. | “7 corrected rows” does not mean seven independent source defects. |
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

## Quantitative displacement theorems (beyond the 29 printed results)

| Mathematical result | Lean evidence | Scope |
|---|---|---|
| Universal projection-distance bound `N(P_U-P_V) <= N(I-W)`. | `DavisKahan/FiniteDimensional/DirectRotation/ProjectionDisplacement.lean`, `projectionDifference_uiNorm_le_displacement`. | Finite-dimensional real/complex, arbitrary UI seminorm; no acuteness needed. |
| Sharp bound `cos(alpha/2) N(I-R) <= N(P_U-P_V) <= N(I-W)` (and its `sec(alpha/2)` formulation). | `SharpDisplacement.lean`, `cos_half_arcsin_projectionGap_mul_uiNorm_directRotation_le_projection`, `cos_half_arcsin_projectionGap_mul_uiNorm_directRotation_le_displacement`, `cos_half_maxPrincipalAngle_mul_uiNorm_directRotation_le_displacement`. | Acute real/complex pairs; full UI seminorm interface. The sharp factor is uniform across norm classes, not individually sharp for every norm. |
| Sharpness for every fixed positive acute maximum angle, and constants `2/sqrt(3)` at `pi/3` and `sqrt(2)` on the acute range. | `SharpDisplacement.lean`, real-family sharpness and uniform estimates; `TraceRatio.lean`. | Sharpness achieved by the real four-dimensional trace-norm example, not by every individual UI norm. |
| Global real-family minimum `min_{WU=V_theta} ||I-W||_1 = 4 sin(theta)`. | `TraceOptimality.lean`, exact projection distance and attained minimum using `W_theta`. | Real four-dimensional parameterized family, all `0<theta<pi/2`. |
| Global complex trace minimizers of explicit phase-plane models (including zero/right angles), their finite direct sums, and supplied ambient unitary models. | `ComplexTraceOptimality.lean`, `ComplexTraceAssembly.lean`, `ComplexTraceFiniteModel.lean`. | Requires a specified principal-plane model/ambient equivalence; not a general arbitrary-subspace-pair theorem. |
| Every equal-dimensional complex pair has minimum `2 sum sin(theta_j)`. | Conventional proof in `sharp_displacement.tex`, optional red box only. | The Lean proof of a decomposition for an arbitrary pair remains to be supplied; excluded from checked-only version. |

The October 23 source archive at commit `5b9c81c4739607f74547f3c55813ebbfc4f00696`
contains the additional Lean declarations. They are separate targeted build
modules; their presence does not alter the original 29-result source census.
`submission/VALIDATION.md` gives the compilation/reproduction boundary.

## Prior-art boundaries

Davis--Kahan Example 4.2 already contains the complex phase mechanism.
Bolotnikov--Li--Rodman (2001) establishes Q-norm optimality in related
settings and counterexamples for Schatten `1 <= p < 2`.
Qiu--Zhang--Li (2005) repeats the short-angle assertion in Section 5;
Zhang--Qiu (2007) analyzes projection-difference principal sines;
Zhang--Qiu (2010) explicitly notes general trace-norm nonminimality.
The exact real short-angle contradiction and uniform sharp package are
presented as formalized deductions, not as claimed first discoveries.
See `PROPOSITION_4_4_LITERATURE_MAP.md` and
`submission/LITERATURE_AUDIT.md`.

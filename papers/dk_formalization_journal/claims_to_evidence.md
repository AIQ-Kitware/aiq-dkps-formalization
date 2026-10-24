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
| Every equal-rank complex subspace pair, without any acuteness hypothesis, admits a global trace minimizer of value `N₁(P_U-P_V)=2 sum sin(theta_j)`. | Conventional Halmos/CS argument in red-framed `sharp_displacement_unformalized.tex`. The verified finite-plane and transport lemmas require an ambient coordinate equivalence not yet produced for arbitrary pairs. | **Unconditional Lean theorem still outstanding.** |

`paper.tex` always includes `sharp_displacement_verified.tex`. Only the global
complex theorem in `sharp_displacement_unformalized.tex` is controlled by
`\includeUnformalizedDisplacementtrue`; set it false for a verified-only
submission. The historical Davis--Kahan source-result inventory remains 29.

The axiom/interface audit is
`DavisKahan/Sources/DavisKahan1970/Audits/SmallAngleCounterexample.lean`.
The user-reported 23 October 2026 compilation of the three targeted modules is recorded in `submission/VALIDATION.md`.

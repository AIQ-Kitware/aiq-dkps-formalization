# Paper context: established claims, boundaries, and editorial decisions

**As of:** 23 October 2026  
**Inspected source snapshot:** `b00c5c8c35e1aab826064285c530260fd558da9b` (following `1c5805c`, `439c910`)
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

**Verification basis.** The user reported successful Lean builds for the source-level results, the small-angle family, the projection-distance bound, fixed-angle sharpness, real global optimality, and complex finite-model theorems on 23 October 2026. The subsequently updated source revision `b00c5c8` adds the unconditional complex and directed-sine trace theorems, imported by `DirectRotation/All.lean`; see `submission/VALIDATION.md` and `claims_to_evidence.md`. This manuscript revision changes no Lean modules. Its PDF builds verify typesetting only.

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

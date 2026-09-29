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
| The current source-facing sine-theta theorem covers the real/complex, unbounded, unitarily invariant norm formulation with finite and ordered half-infinite form-gap alternatives. | `DavisKahan/Sources/DavisKahan1970/SineTheta/Presentation.lean`, theorem `sinTheta_unbounded_formGap_whereDefinedUIN_rclike`; related definitions in the same source layer. | Describe only the hypotheses actually encoded. In particular, do not claim extra domain generality from the forward-inclusion formulation alone. |
| The Lean rectangular sine map represents the source positive sine operator at the norm level. | Mathematical identity `S* S = E0* (I-P) E0 = I - E0* P E0`, so `|S|` is the source positive sine operator; review in `papers/formalization_process/notes/SINE_THETA_NORM_SOURCE_REVIEW.md`; implementation in the Davis--Kahan sine/ideal layers. | Do not say the rectangular map and positive sine operator are literally the same operator: their source/target spaces differ. |
| Davis--Kahan Proposition 4.4 is false as printed. | `DavisKahan/Sources/DavisKahan1970/Section4.lean`; `DavisKahan/FiniteDimensional/DirectRotation/ShortRotationCounterexample.lean`. | The formal witness is four-dimensional and uses principal angle `pi/4`. |
| The printed proof of Proposition 4.4 uses an invalid full-displacement norm step. | `ShortRotationCounterexample.lean` and the source-review material surrounding Section 4. | State the failed inequality concretely rather than merely saying the proof has a gap. |
| A Q-norm version of the Proposition 4.4 conclusion is valid. | `DavisKahan/FiniteDimensional/DirectRotation/QNorm.lean`, including `IsQNorm` and `directRotation_fullDisplacement_qnorm`. | Do not automatically identify this formal class with every commonly named norm family unless separately proved/cited. |
| The formalization required reusable operator-theoretic foundations beyond the source-facing statements. | `ForTauCeti/` and Davis--Kahan foundation layers, including partial/unbounded operators, spectral/form-gap machinery, symmetric operator ideals, principal-angle/direct-rotation geometry, and Sylvester results. | Discuss mathematical capabilities, not raw module counts, unless a fresh reproducible census is provided. |
| YWS is a downstream statistical specialization supported by its own source-facing Lean layer. | `YuWangSamworth2015/YuWangSamworth2015/CitationSurface.lean`, theorem modules under `Symmetric/` and `Rectangular/`. | YWS is secondary in this journal manuscript. |
| The YWS source audit found two printed defects. | `YuWangSamworth2015/` audit/grounding files and machine-checked correction/refutation declarations. | The defects are equation (4)'s missing square and Theorem 3's rank-boundary convention. |
| The current YWS census has 24 tracking entries: 22 printed-source entries and 2 explicit additions; all 24 are verified and 7 rows use corrected statements. | `snapshots/census_macros.tex` and the underlying YWS census generator/source. | “7 corrected rows” does not mean seven independent source defects. |

## Claims deliberately removed from the journal manuscript

The following evidence may remain in the repository for other papers or
historical analysis, but it should not be used to expand this journal article's
contribution statement:

- downstream application-project coverage;
- token/resource accounting and cost extrapolation;
- model/co-author provenance as an empirical result;
- practitioner surveys or human--LLM workflow taxonomy; and
- broad process-study conclusions from the workshop paper.

The workshop paper is still a useful source of editorial improvements, especially
its explicit separation of formal verification from source correspondence.

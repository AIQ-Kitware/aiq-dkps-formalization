# Davis--Kahan 1970 formalization result inventory

**This file, not the 272 source atoms or the 50 organizational rows, is the denominator for 100% formalization.**

The denominator contains exactly the four Section 2 headline theorems and every named theorem, proposition, lemma, and corollary Davis--Kahan actually establish in the paper. Section 10, explicitly unresolved/deferred claims, proof equations, examples, numerical working, historical/external results, and theorem-adjacent remarks do not count.

- Counted results: **29**
- Result-boundary reviews accepted: **29/29**
- Currently hostile-certified terminal: **29**
- Awaiting closure: **0**
- Printed statements that are NOT locally self-contained: **1**
- Result-only semantic sweep: `dev/davis-kahan-1970-result-semantic-review-2026-08-12.md`
- Compiler-checkable theorem surface: `DavisKahan/Sources/DavisKahan1970/Audits/ResultSemanticSurface.lean`

Each result below explicitly partitions its primary source block into atoms inside the printed result statement and adjacent fidelity-only atoms outside it. Cross-block atoms are shared scope clauses (not extra results).

## Source-alignment taxonomy

- `locally_exact` — the printed statement is self-contained and Lean matches it directly.
- `paper_faithful_nonlocal_source_interpretation` — the result is true and Lean is faithful, but the correspondence relies on source semantics stated elsewhere in the paper. The row must carry an accepted `nonlocal_source_interpretation` record, and the generated audit packet puts that record in front of the reviewer for adjudication.
- `refuted_as_transcribed` — the printed statement is meaningful and mathematically false; an exact counterexample plus a separate repair record are required. Proposition 4.4 is the canonical case, and the middle category is never a softened version of it.

| Result | Kind | Alignment | Self-contained | Disposition | Compiler | Semantic review | Boundary |
|---|---|---|---|---|---|---|---|
| `S2-sin-theta` | unnumbered_theorem | `locally_exact` | yes | `proved_exact` | `proved_in_build` | `accepted` | `accepted` |
| `S2-tan-theta` | unnumbered_theorem | `paper_faithful_nonlocal_source_interpretation` | **no** | `proved_exact` | `proved_in_build` | `accepted` | `accepted` |
| `S2-sin-two-theta` | unnumbered_theorem | `locally_exact` | yes | `proved_exact` | `proved_in_build` | `accepted` | `accepted` |
| `S2-tan-two-theta` | unnumbered_theorem | `locally_exact` | yes | `proved_exact` | `proved_in_build` | `accepted` | `accepted` |
| `DK-3.1-prop` | proposition | `locally_exact` | yes | `proved_exact` | `proved_in_build` | `accepted` | `accepted` |
| `DK-3.2-prop` | proposition | `locally_exact` | yes | `proved_exact` | `proved_in_build` | `accepted` | `accepted` |
| `DK-3.3-prop` | proposition | `locally_exact` | yes | `proved_exact` | `proved_in_build` | `accepted` | `accepted` |
| `DK-3.4-prop` | proposition | `locally_exact` | yes | `proved_exact` | `proved_in_build` | `accepted` | `accepted` |
| `DK-3.1-thm` | theorem | `locally_exact` | yes | `proved_exact` | `proved_in_build` | `accepted` | `accepted` |
| `DK-3.1-cor` | corollary | `locally_exact` | yes | `proved_exact` | `proved_in_build` | `accepted` | `accepted` |
| `DK-3.5-prop` | proposition | `locally_exact` | yes | `proved_exact` | `proved_in_build` | `accepted` | `accepted` |
| `DK-3.2-cor` | corollary | `locally_exact` | yes | `proved_exact` | `proved_in_build` | `accepted` | `accepted` |
| `DK-4.1-prop` | proposition | `locally_exact` | yes | `proved_exact` | `proved_in_build` | `accepted` | `accepted` |
| `DK-4.1-cor` | corollary | `locally_exact` | yes | `proved_exact` | `proved_in_build` | `accepted` | `accepted` |
| `DK-4.2-prop` | proposition | `locally_exact` | yes | `proved_exact` | `proved_in_build` | `accepted` | `accepted` |
| `DK-4.3-prop` | proposition | `locally_exact` | yes | `proved_exact` | `proved_in_build` | `accepted` | `accepted` |
| `DK-4.4-prop` | proposition | `refuted_as_transcribed` | yes | `refuted_as_transcribed` | `proved_in_build` | `accepted` | `accepted` |
| `DK-5.1-thm` | theorem | `locally_exact` | yes | `proved_exact` | `proved_in_build` | `accepted` | `accepted` |
| `DK-5.2-thm` | theorem | `locally_exact` | yes | `proved_exact` | `proved_in_build` | `accepted` | `accepted` |
| `DK-5.1-lem` | lemma | `locally_exact` | yes | `proved_exact` | `proved_in_build` | `accepted` | `accepted` |
| `DK-6.1-lem` | lemma | `locally_exact` | yes | `proved_exact` | `proved_in_build` | `accepted` | `accepted` |
| `DK-6.2-lem` | lemma | `locally_exact` | yes | `proved_exact` | `proved_in_build` | `accepted` | `accepted` |
| `DK-6.1-prop` | proposition | `locally_exact` | yes | `proved_exact` | `proved_in_build` | `accepted` | `accepted` |
| `DK-6.1-thm` | theorem | `locally_exact` | yes | `proved_exact` | `proved_in_build` | `accepted` | `accepted` |
| `DK-6.2-thm` | theorem | `locally_exact` | yes | `proved_exact` | `proved_in_build` | `accepted` | `accepted` |
| `DK-6.3-thm` | theorem | `locally_exact` | yes | `proved_exact` | `proved_in_build` | `accepted` | `accepted` |
| `DK-6.3-lem` | lemma | `locally_exact` | yes | `proved_exact` | `proved_in_build` | `accepted` | `accepted` |
| `DK-8.1-thm` | theorem | `locally_exact` | yes | `proved_exact` | `proved_in_build` | `accepted` | `accepted` |
| `DK-8.2-thm` | theorem | `locally_exact` | yes | `proved_exact` | `proved_in_build` | `accepted` | `accepted` |

## Results whose printed statement is not locally self-contained

### `S2-tan-theta` — Single-angle tangent theorem

- Interpretation review: **accepted** (paper_faithful_nonlocal_source_interpretation), reviewed 2026-08-12
- Kept distinct from the canonical refutation `DK-4.4-prop`

**The interpretive issue.** The printed Section 2 tangent theorem states only the ordered spectral gap and H_0 = 0. It states neither the matching-dimension condition (1.5) nor the crossed-dimension condition (3.5), and (3.5) is not introduced anywhere in the paper until Section 3. The Lean statements of the ambient conclusion nevertheless carry a crossed-defect hypothesis corresponding to (3.5). A reviewer must decide whether that hypothesis formalizes semantics the paper already imposes nonlocally, or strengthens the printed result.

**Chronological mismatch.** The theorem is printed in Section 2, before (3.5) exists in the exposition, and is proved in Section 6, after (3.5) has been standing since Section 3. The Section 2 display therefore does not locally carry the qualification that makes the ambient tangent quantity a meaningful finite norm in the general infinite-dimensional case.

**Nonlocal source material used to read the statement.**

- Section 1 paper-wide convention that some results are vacuous when certain norms fail to exist, with no repetition of the qualification at the individual statements.
- Section 3 standing convention, fixed immediately after the proof of Proposition 3.2, that (3.5) as well as (1.5) is assumed for the remainder of the paper except where the contrary is stated.
- Proposition 3.2 and its remark: (3.5) is equivalent to direct-rotation existence outside the acute case, is automatic when either P-space or its orthocomplement is finite-dimensional, and is not implied by (1.5) in infinite dimension (bilateral-shift example).
- Section 3 angle-operator/polar passage: the partial isometry J_0 with J_0 Theta_0 = Theta_1 J_0 exists as described in the direct-rotation setting fixed by that standing convention.
- Section 6 proof context: the printed ambient conclusion is proved in Section 6, inside the standing scope, by comparing the two tangent corners through J_0 and applying Lemmas 6.1 and 6.2.

**Supporting source atoms.**

- `S1-block-residual.norm-existence-vacuity-convention` — `paper_wide_convention` — Paper-wide convention: some of the paper's results are vacuous when certain norms occurring in them fail to exist, and the source will not repeat that qualification at the individual statements.
- `S1-block-residual.eq-1-5` — `related_dimension_condition` — Exact mathematical content of source equation (1.5) as reconstructed in the distributable TeX.
- `S1-ui-norms.ambient-angle-doubling` — `related_unqualified_claim` — Section 1 states, in anticipation of the Section 3 direct-rotation construction and without restating a dimension hypothesis, that the nonzero angle data of the ambient angle operator are those of Theta_0 occurring twice, once from each side.
- `S2-tan-theta.ambient-conclusion` — `printed_statement_clause` — delta ||tan Theta|| <= ||H||.
- `DK-3.2-prop.eq-3-5` — `omitted_qualification` — Exact mathematical content of source equation (3.5) as reconstructed in the distributable TeX.
- `DK-3.2-prop.finite-crossing-automatic` — `automatic_case` — Under the assumed (1.5), condition (3.5) holds automatically whenever either dim P-space or dim P-perp-space is finite.
- `DK-3.2-prop.bilateral-shift-counterexample` — `scope_separating_example` — The bilateral-shift example on two-sided square-summable sequences satisfies (1.5) with nested P-space and Q-space, has crossing subspaces of dimensions 1 and 0, and therefore fails (3.5): the matching-dimension conditions do not imply the crossing-dimension condition in infinite dimension.
- `S3-standing-scope.crossed-dimension-standing-assumption` — `later_standing_assumption` — Standing convention: (3.5) is assumed as well as (1.5) for the remainder of the paper, except where the contrary is explicitly stated, so a direct rotation always exists and the development uses its direct special case (3.6).
- `DK-3.1-thm.angle-operator-partial-isometry` — `proof_context_dependency` — For the direct rotation, Theta_j = arccos C_j, the two angle operators are isometric-equivalent apart from the dimensionalities of their null spaces, and the polar resolution S_0 = J_0 sin Theta_0 gives a partial isometry J_0 of the closed range of Theta_0 onto that of Theta_1 with J_0 Theta_0 = Theta_1 J_0.
- `DK-6.3-thm.tangent-proof-temporary-boundedness` — `proof_context_dependency` — The Section 6 tangent proof temporarily supposes that all operators are bounded and that S_0 is compact, and defers the removal of both restrictions to the Appendix to Section 6.
- `DK-6.3-thm.ambient-wholeSpace-assembly` — `proof_context_dependency` — The ambient conclusion is assembled from the directed one: tan Theta has the two-corner block form built from J_0, tan Theta_0 and tan Theta_1, the two corners have equal unitarily invariant norms through J_0, and Lemmas 6.1 and 6.2 then give delta ||tan Theta|| <= ||H||.

**Where Lean makes the implicit semantics explicit.**

- `TauCeti.DavisKahan1970.tanTheta_wholeSpace_paperUINorm_of_crossedDefectsEquivalent`
  - Carries `h35 : CrossedDefectsEquivalent U V`, the constructive form of (3.5) (an isometric equivalence of the two crossed defect spaces), and concludes both `N.Mem (paperTanAngleOperatorC U V)` and the sharp inequality. Membership in the norm's ideal is a conclusion, which is the explicit form of the source's vacuity convention.
- `TauCeti.DavisKahan1970.tanTheta_unbounded_ambient_paperUINorm_exact`
  - Same (3.5) hypothesis at unbounded self-adjoint scope over complex scalars, with the norm-ideal membership again concluded.
- `TauCeti.DavisKahan1970.tanTheta_wholeSpace_paperUINorm`
  - Alternative bounded route assuming uniform transversality `‖sin Theta‖ < 1` instead of (3.5). This is a strictly stronger hypothesis than the source's standing condition and is registered as a specialization, not as the source-shaped form.
- `TauCeti.DavisKahan.Frontier.Section3.remark3_2_bilateralShift_separates_dimensionHypotheses`
  - Machine-checked witness that (1.5) does not imply (3.5) in infinite dimension, so the omitted qualification is substantive. It is a vacuity/nonvacuity witness, not a counterexample to the counted result.

**Accepted reading.** The printed theorem is read under the paper's own global semantics: the Section 1 vacuity convention governs the existence of the displayed norms, and the standing (3.5) is in force where the theorem is actually proved. On that reading a Lean statement that carries a crossed-defect hypothesis corresponding to (3.5), and that concludes rather than assumes membership of the tangent operator in the norm's ideal, is a source-faithful formalization of semantics the paper already imposes. It is not a claim that the Section 2 display literally contains (3.5).

**Strongest competing literal reading.** Read only the local Section 2 hypotheses and interpret the displayed norm of tan Theta as +infinity when tan Theta is unbounded. The nested infinite-dimensional half-space configuration then satisfies every printed hypothesis with a finite (indeed zero) perturbation, the directed conclusion holds with both sides zero, and the ambient conclusion fails. Under that reading the printed ambient clause would be false as transcribed and the (3.5)-qualified theorem would be its repair.

**Why this is not a refutation.** In that configuration tan Theta is not a bounded operator and the displayed unitarily invariant norm does not exist, so the witness exhibits a missing nonvacuity qualification rather than a finite-valued failure of the inequality. The paper declares such cases vacuous in advance. The literal reading would equally convict the Section 1 angle-doubling sentence and later developments that silently use the direct rotation. This is therefore deliberately not classified as refuted_as_transcribed; contrast DK-4.4-prop, where all objects exist, the compared quantities are finite, and the printed conclusion is false.

**Semantic conclusion.** S2-tan-theta is a true counted result whose exact formal representation requires nonlocal source semantics that the repository makes explicit rather than assumes silently. The interpretation is accepted. A later hostile scope audit found that the first pair of `unbounded ambient` endpoints still kept the Ritz compression bounded; the Appendix explicitly allows both `A_0` and `Lambda_1` to be unbounded. That stronger scope is now represented by `tanTheta_unboundedCompression_ambient_paperUINorm_exact` and `tanTheta_unboundedCompression_ambient_paperUINorm_real_exact`.

The accepted reading is hash-pinned to the distributable specification, the source-fidelity inventory, and the cited atoms; any edit to that material makes it stale and the result checker fails closed.

## Current closure queue

Empty. All 29 counted results are terminal on all three axes.

`S2-tan-theta` is terminal after a hostile Appendix-scope correction. The earlier `tanTheta_unbounded_ambient_*_exact` declarations cover an unbounded ambient operator with a bounded Ritz compression. The Appendix-complete declarations `TauCeti.DavisKahan1970.tanTheta_unboundedCompression_ambient_paperUINorm_exact` and `..._real_exact` additionally allow the Ritz compression `A_0` itself to be a genuinely unbounded self-adjoint closed operator semibounded above in form, while retaining a bounded residual/perturbation and the sharp factor-one ambient inequality.

## Printed-statement boundary reviews

### `S2-sin-theta` — Single-angle sine theorem

- Exact source anchor: Section 2, sin theta theorem
- Included same-block atoms: `S2-sin-theta.ui-norm-scope`, `S2-sin-theta.gap-hypothesis`, `S2-sin-theta.directed-conclusion`
- Cross-block shared scope atoms: `S2-unbounded-scope.infinite-dimensional-scope`, `S2-unbounded-scope.arbitrary-ui-scope`, `S2-unbounded-scope.unbounded-selfadjoint-scope`, `S2-unbounded-scope.bounded-residual-needed`, `S2-unbounded-scope.half-infinite-gap-intervals`
- Explicitly excluded same-block atoms:
  - `S2-sin-theta.family-distinctness` — `expository_commentary_not_result` — The four Section 2 theorem families are distinct rather than mere restatements.
- Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### `S2-tan-theta` — Single-angle tangent theorem

- Exact source anchor: Section 2, tan theta theorem
- Included same-block atoms: `S2-tan-theta.ordered-gap-hypothesis`, `S2-tan-theta.rayleigh-ritz-hypothesis`, `S2-tan-theta.directed-conclusion`, `S2-tan-theta.ambient-conclusion`
- Cross-block shared scope atoms: `S2-sin-theta.ui-norm-scope`, `S2-unbounded-scope.infinite-dimensional-scope`, `S2-unbounded-scope.arbitrary-ui-scope`, `S2-unbounded-scope.unbounded-selfadjoint-scope`, `S2-unbounded-scope.bounded-residual-needed`, `S2-unbounded-scope.half-infinite-gap-intervals`
- Explicitly excluded same-block atoms:
  - none
- Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### `S2-sin-two-theta` — Double-angle sine theorem

- Exact source anchor: Section 2, sin 2 theta theorem
- Included same-block atoms: `S2-sin-two-theta.gap-hypothesis`, `S2-sin-two-theta.directed-conclusion`, `S2-sin-two-theta.ambient-conclusion`
- Cross-block shared scope atoms: `S2-sin-theta.ui-norm-scope`, `S2-unbounded-scope.infinite-dimensional-scope`, `S2-unbounded-scope.arbitrary-ui-scope`, `S2-unbounded-scope.unbounded-selfadjoint-scope`, `S2-unbounded-scope.bounded-residual-needed`, `S2-unbounded-scope.half-infinite-gap-intervals`
- Explicitly excluded same-block atoms:
  - none
- Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### `S2-tan-two-theta` — Double-angle tangent theorem

- Exact source anchor: Section 2, tan 2 theta theorem
- Included same-block atoms: `S2-tan-two-theta.ordered-gap-hypothesis`, `S2-tan-two-theta.strong-offdiagonal-hypothesis`, `S2-tan-two-theta.no-extra-pole-hypothesis`, `S2-tan-two-theta.directed-conclusion`, `S2-tan-two-theta.ambient-conclusion`
- Cross-block shared scope atoms: `S2-sin-theta.ui-norm-scope`, `S2-unbounded-scope.infinite-dimensional-scope`, `S2-unbounded-scope.arbitrary-ui-scope`, `S2-unbounded-scope.unbounded-selfadjoint-scope`, `S2-unbounded-scope.bounded-residual-needed`, `S2-unbounded-scope.half-infinite-gap-intervals`
- Explicitly excluded same-block atoms:
  - `S2-tan-two-theta.pole-exclusion-derived` — `proof_or_derivation_not_result` — Section 7 derives the needed nonvanishing cosine factors from the printed hypotheses.
- Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### `DK-3.1-prop` — Acute direct rotation existence and uniqueness

- Exact source anchor: Proposition 3.1
- Included same-block atoms: `DK-3.1-prop.existence`, `DK-3.1-prop.uniqueness`, `DK-3.1-prop.positive-diagonal-characterization`
- Cross-block shared scope atoms: none
- Explicitly excluded same-block atoms:
  - none
- Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### `DK-3.2-prop` — Nonacute existence criterion

- Exact source anchor: Proposition 3.2
- Included same-block atoms: `DK-3.2-prop.existence-iff-crossing-dimensions`, `DK-3.2-prop.nonuniqueness`, `DK-3.2-prop.eq-3-5`
- Cross-block shared scope atoms: none
- Explicitly excluded same-block atoms:
  - `DK-3.2-prop.crossing-square-minus-one` — `proof_detail_not_in_printed_statement` — On the crossing subspaces U^2 x=-x.
  - `DK-3.2-prop.finite-crossing-automatic` — `post_result_scope_remark_not_in_printed_statement` — Under the assumed (1.5), condition (3.5) holds automatically whenever either dim P-space or dim P-perp-space is finite.
  - `DK-3.2-prop.bilateral-shift-counterexample` — `remark_or_example_not_result` — The bilateral-shift example on two-sided square-summable sequences satisfies (1.5) with nested P-space and Q-space, has crossing subspaces of dimensions 1 and 0, and therefore fails (3.5): the matching-dimension conditions do not imply the crossing-dimension condition in infinite dimension.
- Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### `DK-3.3-prop` — Principal square-root characterization

- Exact source anchor: Proposition 3.3
- Included same-block atoms: `DK-3.3-prop.principal-square-root`, `DK-3.3-prop.square-root-converse`
- Cross-block shared scope atoms: none
- Explicitly excluded same-block atoms:
  - `DK-3.3-prop.reflection-conjugacy` — `pre_result_setup_not_in_printed_statement` — With X=P-Pperp and Q_-=XQX, U^{-1}=XUX.
  - `DK-3.3-prop.eq-3-6` — `proof_or_derivation_not_result` — Exact mathematical content of source equation (3.6) as reconstructed in the distributable TeX.
  - `DK-3.3-prop.eq-3-7` — `proof_or_derivation_not_result` — Exact mathematical content of source equation (3.7) as reconstructed in the distributable TeX.
  - `DK-3.3-prop.eq-3-8` — `proof_or_derivation_not_result` — Exact mathematical content of source equation (3.8) as reconstructed in the distributable TeX.
- Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### `DK-3.4-prop` — Square as a direct rotation

- Exact source anchor: Proposition 3.4
- Included same-block atoms: `DK-3.4-prop.u-square-direct-rotation`
- Cross-block shared scope atoms: `S3-standing-scope.crossed-dimension-standing-assumption`
- Explicitly excluded same-block atoms:
  - none
- Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### `DK-3.1-thm` — Classification of pairs of subspaces

- Exact source anchor: Theorem 3.1
- Included same-block atoms: `DK-3.1-thm.complete-invariant`, `DK-3.1-thm.converse-angle-data`
- Cross-block shared scope atoms: none
- Explicitly excluded same-block atoms:
  - `DK-3.1-thm.angle-operator-partial-isometry` — `pre_result_setup_not_in_printed_statement` — For the direct rotation, Theta_j = arccos C_j, the two angle operators are isometric-equivalent apart from the dimensionalities of their null spaces, and the polar resolution S_0 = J_0 sin Theta_0 gives a partial isometry J_0 of the closed range of Theta_0 onto that of Theta_1 with J_0 Theta_0 = Theta_1 J_0.
  - `DK-3.1-thm.reconstruction` — `proof_detail_not_in_printed_statement` — The pair is reconstructed from the angle data and J0.
- Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### `DK-3.1-cor` — Compact classification by angle eigenvalues

- Exact source anchor: Corollary 3.1
- Included same-block atoms: `DK-3.1-cor.compact-complete-invariants`, `DK-3.1-cor.allowed-angle-sequence`, `DK-3.1-cor.theta1-match`
- Cross-block shared scope atoms: none
- Explicitly excluded same-block atoms:
  - none
- Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### `DK-3.5-prop` — Angle commutation and eigenspace geometry

- Exact source anchor: Proposition 3.5
- Included same-block atoms: `DK-3.5-prop.commutation`, `DK-3.5-prop.eigenvector-rotation-angle`, `DK-3.5-prop.acute-maximal-characterization`
- Cross-block shared scope atoms: none
- Explicitly excluded same-block atoms:
  - `DK-3.5-prop.direct-rotation-exponential` — `pre_result_setup_not_in_printed_statement` — U=exp(J Theta).
  - `DK-3.5-prop.cos-square-projector` — `pre_result_setup_not_in_printed_statement` — cos^2 Theta=PQP+Pperp Qperp Pperp.
- Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### `DK-3.2-cor` — Reversal symmetry

- Exact source anchor: Corollary 3.2
- Included same-block atoms: `DK-3.2-cor.swap-invariance`
- Cross-block shared scope atoms: none
- Explicitly excluded same-block atoms:
  - none
- Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### `DK-4.1-prop` — Pointwise and singular-value extremality of the direct rotation

- Exact source anchor: Proposition 4.1
- Included same-block atoms: `DK-4.1-prop.orthonormal-angle-lower-bounds`, `DK-4.1-prop.singular-value-minimality`
- Cross-block shared scope atoms: none
- Explicitly excluded same-block atoms:
  - `DK-4.1-prop.vz-factorization` — `section_setup_not_result` — Every unitary V carrying P to Q is written V=UZ with Z block diagonal in the Section 4 setup.
  - `DK-4.1-prop.closest-q-vector-proof-step` — `proof_or_derivation_not_result` — The pointwise comparison uses Qx/||Qx|| as the closest unit vector in Q-space.
  - `DK-4.1-prop.eq-4-1` — `proof_or_derivation_not_result` — Exact mathematical content of source equation (4.1) as reconstructed in the distributable TeX.
  - `DK-4.1-prop.eq-4-2` — `proof_or_derivation_not_result` — Exact mathematical content of source equation (4.2) as reconstructed in the distributable TeX.
- Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### `DK-4.1-cor` — UI-norm minimality of direct rotation displacement

- Exact source anchor: Corollary 4.1
- Included same-block atoms: `DK-4.1-cor.ui-minimality-on-p`
- Cross-block shared scope atoms: none
- Explicitly excluded same-block atoms:
  - none
- Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### `DK-4.2-prop` — Basis-angle square-sum extremality

- Exact source anchor: Proposition 4.2
- Included same-block atoms: `DK-4.2-prop.basis-sine-square-lower-bound`
- Cross-block shared scope atoms: none
- Explicitly excluded same-block atoms:
  - `DK-4.2-prop.trace-identification` — `proof_or_derivation_not_result` — The lower bound is identified with tr(S0* S0).
- Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### `DK-4.3-prop` — Squared displacement UI-norm minimality

- Exact source anchor: Proposition 4.3
- Included same-block atoms: `DK-4.3-prop.squared-displacement-global-minimum`
- Cross-block shared scope atoms: none
- Explicitly excluded same-block atoms:
  - `DK-4.3-prop.plane-parameterization` — `proof_detail_not_in_printed_statement` — On each principal two-plane V has the displayed a_j,b_j parameterization.
  - `DK-4.3-prop.operator-norm-displacement-minimum` — `post_result_consequence_not_in_printed_statement` — The operator norm of 1-V is minimized by U.
  - `DK-4.3-prop.hilbert-schmidt-displacement-minimum` — `post_result_consequence_not_in_printed_statement` — The Hilbert--Schmidt norm of 1-V is minimized by U.
  - `DK-4.3-prop.arbitrary-ui-displacement-warning` — `post_result_consequence_not_in_printed_statement` — Arbitrary UI norms of 1-V need not be minimized by U.
  - `DK-4.3-prop.eq-4-3` — `proof_or_derivation_not_result` — Exact mathematical content of source equation (4.3) as reconstructed in the distributable TeX.
  - `DK-4.3-prop.eq-4-4` — `proof_or_derivation_not_result` — Exact mathematical content of source equation (4.4) as reconstructed in the distributable TeX.
  - `DK-4.3-prop.eq-4-5` — `proof_or_derivation_not_result` — Exact mathematical content of source equation (4.5) as reconstructed in the distributable TeX.
  - `DK-4.3-prop.eq-4-6` — `proof_or_derivation_not_result` — Exact mathematical content of source equation (4.6) as reconstructed in the distributable TeX.
- Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### `DK-4.4-prop` — Full-displacement counterexamples and Proposition 4.4 as printed

- Exact source anchor: Proposition 4.4
- Included same-block atoms: `DK-4.4-prop.printed-proposition4-4`
- Cross-block shared scope atoms: none
- Explicitly excluded same-block atoms:
  - `DK-4.4-prop.example4-1-real-reflection` — `remark_or_example_not_result` — Example 4.1 gives a real reflection with singular values 2,0 versus two equal direct-rotation singular values and defeats the Ky Fan 2 norm for theta>pi/3.
  - `DK-4.4-prop.example4-2-complex-phase` — `remark_or_example_not_result` — Example 4.2 uses V=e^{i delta}U and shows the full-displacement UI minimum can fail in complex space.
  - `DK-4.4-prop.printed-sharp-threshold` — `sharpness_commentary_not_designated_result` — The paper asserts the pi/3 threshold is sharp in view of the examples.
- Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### `DK-5.1-thm` — Banach-space Sylvester lower bound

- Exact source anchor: Theorem 5.1
- Included same-block atoms: `DK-5.1-thm.banach-hypotheses`, `DK-5.1-thm.sylvester-lower-bound`
- Cross-block shared scope atoms: none
- Explicitly excluded same-block atoms:
  - `DK-5.1-thm.roles-interchange` — `post_result_scope_remark_not_in_printed_statement` — A and B roles/hypotheses may be interchanged.
  - `DK-5.1-thm.one-sided-unbounded-extension` — `post_result_scope_remark_not_in_printed_statement` — The proof covers densely-defined unbounded A with bounded inverse hypothesis while B,X remain bounded.
- Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### `DK-5.2-thm` — Semibounded self-adjoint Sylvester theorem

- Exact source anchor: Theorem 5.2
- Included same-block atoms: `DK-5.2-thm.hilbert-unbounded-hypotheses`, `DK-5.2-thm.hilbert-unbounded-conclusion`
- Cross-block shared scope atoms: none
- Explicitly excluded same-block atoms:
  - none
- Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### `DK-5.1-lem` — Strong-cutoff convergence of singular values

- Exact source anchor: Lemma 5.1
- Included same-block atoms: `DK-5.1-lem.strong-cutoff-convergence`
- Cross-block shared scope atoms: none
- Explicitly excluded same-block atoms:
  - none
- Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### `DK-6.1-lem` — Direct-sum UI-norm comparison and converse

- Exact source anchor: Lemma 6.1
- Included same-block atoms: `DK-6.1-lem.ordered-sylvester-forward`, `DK-6.1-lem.ordered-sylvester-converse`
- Cross-block shared scope atoms: none
- Explicitly excluded same-block atoms:
  - none
- Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### `DK-6.2-lem` — Reflection-pinch contraction

- Exact source anchor: Lemma 6.2
- Included same-block atoms: `DK-6.2-lem.pinching-contraction`
- Cross-block shared scope atoms: none
- Explicitly excluded same-block atoms:
  - none
- Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### `DK-6.1-prop` — Sine proof, ambient limitation, and symmetric sine theorem

- Exact source anchor: Proposition 6.1
- Included same-block atoms: `DK-6.1-prop.symmetric-sine-theorem`
- Cross-block shared scope atoms: none
- Explicitly excluded same-block atoms:
  - `DK-6.1-prop.sine-proof-residual-identity` — `proof_detail_not_in_printed_statement` — The symmetric sine proof rewrites the relevant off-diagonal block as the Sylvester residual identity.
  - `DK-6.1-prop.source-counterexample-need-two-sided` — `remark_or_example_not_result` — The source exhibits the failure of the ambient/symmetric conclusion when the needed two-sided placement is dropped.
  - `DK-6.1-prop.eq-6-1` — `proof_or_derivation_not_result` — Exact mathematical content of source equation (6.1) as reconstructed in the distributable TeX.
- Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### `DK-6.1-thm` — Generalized sine theorem

- Exact source anchor: Theorem 6.1
- Included same-block atoms: `DK-6.1-thm.generalized-sine-hypotheses`, `DK-6.1-thm.generalized-sine-conclusion`, `DK-6.1-thm.unequal-dimension-scope`
- Cross-block shared scope atoms: none
- Explicitly excluded same-block atoms:
  - none
- Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### `DK-6.2-thm` — Pairwise-gap square-norm sine theorem

- Exact source anchor: Theorem 6.2
- Included same-block atoms: `DK-6.2-thm.second-generalized-sine`
- Cross-block shared scope atoms: none
- Explicitly excluded same-block atoms:
  - `DK-6.2-thm.rank-corrected-operator-consequence` — `post_result_consequence_not_in_printed_statement` — The stated rank-corrected operator-norm consequence follows.
- Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### `DK-6.3-thm` — Tangent proof machinery, Example 6.1, and generalized tangent theorem

- Exact source anchor: Theorem 6.3
- Included same-block atoms: `DK-6.3-thm.generalized-tangent-theorem`
- Cross-block shared scope atoms: none
- Explicitly excluded same-block atoms:
  - `DK-6.3-thm.tangent-setup-identities` — `proof_or_derivation_not_result` — Equations (6.2)--(6.6) provide the block identities used in the generalized tangent proof.
  - `DK-6.3-thm.tangent-proof-temporary-boundedness` — `proof_or_derivation_not_result` — The Section 6 tangent proof temporarily supposes that all operators are bounded and that S_0 is compact, and defers the removal of both restrictions to the Appendix to Section 6.
  - `DK-6.3-thm.ambient-wholeSpace-assembly` — `proof_or_derivation_not_result` — The ambient conclusion is assembled from the directed one: tan Theta has the two-corner block form built from J_0, tan Theta_0 and tan Theta_1, the two corners have equal unitarily invariant norms through J_0, and Lemmas 6.1 and 6.2 then give delta ||tan Theta|| <= ||H||.
  - `DK-6.3-thm.example6-1` — `remark_or_example_not_result` — Example 6.1 gives the explicit 2x2 counterexample showing one-sided placement is essential for the tangent conclusion.
  - `DK-6.3-thm.eq-6-2` — `proof_or_derivation_not_result` — Exact mathematical content of source equation (6.2) as reconstructed in the distributable TeX.
  - `DK-6.3-thm.eq-6-3` — `proof_or_derivation_not_result` — Exact mathematical content of source equation (6.3) as reconstructed in the distributable TeX.
  - `DK-6.3-thm.eq-6-4` — `proof_or_derivation_not_result` — Exact mathematical content of source equation (6.4) as reconstructed in the distributable TeX.
  - `DK-6.3-thm.eq-6-5` — `proof_or_derivation_not_result` — Exact mathematical content of source equation (6.5) as reconstructed in the distributable TeX.
  - `DK-6.3-thm.eq-6-6` — `proof_or_derivation_not_result` — Exact mathematical content of source equation (6.6) as reconstructed in the distributable TeX.
- Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### `DK-6.3-lem` — Finite-rank near-maximizer leakage estimate

- Exact source anchor: Lemma 6.3
- Included same-block atoms: `DK-6.3-lem.approximation-number-leakage`
- Cross-block shared scope atoms: none
- Explicitly excluded same-block atoms:
  - none
- Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### `DK-8.1-thm` — Branch selection and spectral repulsion

- Exact source anchor: Theorem 8.1
- Included same-block atoms: `DK-8.1-thm.acute-iff-spectral-placement`, `DK-8.1-thm.existence-correct-q`, `DK-8.1-thm.part-i-compression`, `DK-8.1-thm.part-ii-eigenvalue`, `DK-8.1-thm.part-iii-gauge`
- Cross-block shared scope atoms: none
- Explicitly excluded same-block atoms:
  - `DK-8.1-thm.branch-problem` — `pre_result_motivation_not_result` — Small double-angle trigonometric quantities alone do not select angles near zero; the chosen reducing subspace matters.
  - `DK-8.1-thm.exclude-pi-over-four` — `proof_or_derivation_not_result` — Equations (8.1)--(8.2) exclude theta=pi/4 and then theta>pi/4 under the selected placement.
  - `DK-8.1-thm.spectral-repulsion-interpretation` — `post_result_interpretation_not_result` — Strong off-diagonal eigenvector rotation forces definite eigenvalue displacement as described.
  - `DK-8.1-thm.eq-8-1` — `proof_or_derivation_not_result` — Exact mathematical content of source equation (8.1) as reconstructed in the distributable TeX.
  - `DK-8.1-thm.eq-8-2` — `proof_or_derivation_not_result` — Exact mathematical content of source equation (8.2) as reconstructed in the distributable TeX.
- Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### `DK-8.2-thm` — Smallness selects the acute branch

- Exact source anchor: Theorem 8.2
- Included same-block atoms: `DK-8.2-thm.smallness-alternative`, `DK-8.2-thm.double-angle-bound-retained`, `DK-8.2-thm.acute-branch-conclusion`
- Cross-block shared scope atoms: `S3-standing-scope.crossed-dimension-standing-assumption`
- Explicitly excluded same-block atoms:
  - `DK-8.2-thm.homotopy-proof` — `proof_or_derivation_not_result` — The perturbation proof uses the continuous spectral-projector homotopy and the displayed arcsine bound.
  - `DK-8.2-thm.residual-reduction` — `proof_or_derivation_not_result` — The residual form is reduced by changing the complementary perturbation block while preserving the residual/spectral data.
  - `DK-8.2-thm.sin2-unequal-dimension-extension` — `post_result_scope_remark_not_in_printed_statement` — The source states a sin2 extension to unequal comparison dimensions.
  - `DK-8.2-thm.no-tan2-unequal-dimension-extension-known` — `historical_knowledge_state` — No analogous tan2 extension was known.
- Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

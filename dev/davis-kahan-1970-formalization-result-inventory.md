# Davis--Kahan 1970 formalization result inventory

**This file, not the 266 source atoms or the 49 organizational rows, is the denominator for 100% formalization.**

The denominator contains exactly the four Section 2 headline theorems and every named theorem, proposition, lemma, and corollary Davis--Kahan actually establish in the paper. Section 10, explicitly unresolved/deferred claims, proof equations, examples, numerical working, historical/external results, and theorem-adjacent remarks do not count.

- Counted results: **29**
- Result-boundary reviews accepted: **29/29**
- Currently hostile-certified terminal: **25**
- Awaiting result-statement semantic closure: **4**
- Result-only semantic sweep: `dev/davis-kahan-1970-result-semantic-review-2026-08-12.md`
- Compiler-checkable theorem surface: `DavisKahan/Sources/DavisKahan1970/Audits/ResultSemanticSurface.lean`

Each result below explicitly partitions its primary source block into atoms inside the printed result statement and adjacent fidelity-only atoms outside it. Cross-block atoms are shared scope clauses (not extra results).

| Result | Kind | Disposition | Compiler | Semantic review | Boundary |
|---|---|---|---|---|---|
| `S2-sin-theta` | unnumbered_theorem | `proved_exact` | `proved_in_build` | `accepted` | `accepted` |
| `S2-tan-theta` | unnumbered_theorem | `pending_result_only_review` | `proved_in_build` | `pending_result_only_review` | `accepted` |
| `S2-sin-two-theta` | unnumbered_theorem | `proved_exact` | `proved_in_build` | `accepted` | `accepted` |
| `S2-tan-two-theta` | unnumbered_theorem | `proved_exact` | `proved_in_build` | `accepted` | `accepted` |
| `DK-3.1-prop` | proposition | `proved_exact` | `proved_in_build` | `accepted` | `accepted` |
| `DK-3.2-prop` | proposition | `proved_exact` | `proved_in_build` | `accepted` | `accepted` |
| `DK-3.3-prop` | proposition | `pending_result_only_review` | `proved_in_build` | `pending_result_only_review` | `accepted` |
| `DK-3.4-prop` | proposition | `pending_result_only_review` | `proved_in_build` | `pending_result_only_review` | `accepted` |
| `DK-3.1-thm` | theorem | `proved_exact` | `proved_in_build` | `accepted` | `accepted` |
| `DK-3.1-cor` | corollary | `proved_exact` | `proved_in_build` | `accepted` | `accepted` |
| `DK-3.5-prop` | proposition | `proved_exact` | `proved_in_build` | `accepted` | `accepted` |
| `DK-3.2-cor` | corollary | `proved_exact` | `proved_in_build` | `accepted` | `accepted` |
| `DK-4.1-prop` | proposition | `pending_result_only_review` | `proved_in_build` | `pending_result_only_review` | `accepted` |
| `DK-4.1-cor` | corollary | `proved_exact` | `proved_in_build` | `accepted` | `accepted` |
| `DK-4.2-prop` | proposition | `proved_exact` | `proved_in_build` | `accepted` | `accepted` |
| `DK-4.3-prop` | proposition | `proved_exact` | `proved_in_build` | `accepted` | `accepted` |
| `DK-4.4-prop` | proposition | `refuted_as_transcribed` | `proved_in_build` | `accepted` | `accepted` |
| `DK-5.1-thm` | theorem | `proved_exact` | `proved_in_build` | `accepted` | `accepted` |
| `DK-5.2-thm` | theorem | `proved_exact` | `proved_in_build` | `accepted` | `accepted` |
| `DK-5.1-lem` | lemma | `proved_exact` | `proved_in_build` | `accepted` | `accepted` |
| `DK-6.1-lem` | lemma | `proved_exact` | `proved_in_build` | `accepted` | `accepted` |
| `DK-6.2-lem` | lemma | `proved_exact` | `proved_in_build` | `accepted` | `accepted` |
| `DK-6.1-prop` | proposition | `proved_exact` | `proved_in_build` | `accepted` | `accepted` |
| `DK-6.1-thm` | theorem | `proved_exact` | `proved_in_build` | `accepted` | `accepted` |
| `DK-6.2-thm` | theorem | `proved_exact` | `proved_in_build` | `accepted` | `accepted` |
| `DK-6.3-thm` | theorem | `proved_exact` | `proved_in_build` | `accepted` | `accepted` |
| `DK-6.3-lem` | lemma | `proved_exact` | `proved_in_build` | `accepted` | `accepted` |
| `DK-8.1-thm` | theorem | `proved_exact` | `proved_in_build` | `accepted` | `accepted` |
| `DK-8.2-thm` | theorem | `proved_exact` | `proved_in_build` | `accepted` | `accepted` |

## Current semantic-closure queue

The result-only hostile audit has reduced the remaining mathematical surface to four precisely scoped targets. Everything else in the 29-result denominator has an accepted source-vs-Lean semantic correspondence.

### `S2-tan-theta` — Single-angle tangent theorem

Result-only audit 2026-08-12: bounded directed and bounded ambient source theorems are present over complex and real Hilbert spaces, and the unbounded directed residual theorem is present over both scalar fields. The remaining source-scope gap is the *ambient unbounded* conclusion `delta * N(tan Theta) <= N(H)` for arbitrary paper UI norm under the printed hypotheses. No existing source-facing theorem was located that combines unbounded self-adjoint ambient scope with the sharp factor-one perturbation conclusion. Keep this result nonterminal until that theorem/wrapper exists and is registered.

### `DK-3.3-prop` — Principal square-root characterization

Result-only audit 2026-08-12: the full nonacute complex Proposition 3.3 principal-unitary-square-root forward/converse characterization exists in `DavisKahan/Frontier/Section3.lean`. The registered real square/principal theorems are acute/uniformly-acute specializations; no source-facing real theorem was located for the full matched-crossed-defect nonacute statement. The exact remaining task is a real nonacute principal-square-root characterization equivalent to the printed Proposition 3.3, preferably through a scalar-generic positivity characterization rather than a complex-spectrum branch condition.

### `DK-3.4-prop` — Square as a direct rotation

Result-only audit 2026-08-12: `proposition3_4_source_full` and its equality-to-direct-rotation companion give the complete printed Proposition 3.4 over complex Hilbert spaces at the nonacute source scope. No real full-scope counterpart was located. The exact remaining task is the `R`-scalar theorem that under the printed `C0^2 >= 1/2` condition, `U^2` is the direct rotation from `Q_-` to `Q`, without replacing the source hypotheses by uniform acuteness.

### `DK-4.1-prop` — Pointwise and singular-value extremality of the direct rotation

Result-only audit 2026-08-12: the arbitrary-dimensional compact complex/real theorems already prove the orthonormal-vector angle lower bounds and approximation-number minimality for the direct rotation. The remaining counted clause is the paper's *closed-form minimum value* `2 sin(theta_k/2)` at the same infinite compact scope. `Proposition4_1_directRotationValues` supplies that identity in finite dimension, but no hostile-reviewable infinite compact theorem identifying the approximation-number sequence with the principal chord sequence was located.

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
  - `DK-3.2-prop.bilateral-shift-counterexample` — `remark_or_example_not_result` — The bilateral-shift example shows the basic P/Q dimension conditions do not imply the crossing-dimension condition.
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
- Cross-block shared scope atoms: none
- Explicitly excluded same-block atoms:
  - none
- Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### `DK-3.1-thm` — Classification of pairs of subspaces

- Exact source anchor: Theorem 3.1
- Included same-block atoms: `DK-3.1-thm.complete-invariant`, `DK-3.1-thm.converse-angle-data`
- Cross-block shared scope atoms: none
- Explicitly excluded same-block atoms:
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

- Result-only semantic review: **accepted**. Existing compiled source-facing declarations cover the full printed branch statement and parts (i)--(iii) over both source scalar fields; no new Lean theorem was required.

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
- Cross-block shared scope atoms: none
- Explicitly excluded same-block atoms:
  - `DK-8.2-thm.homotopy-proof` — `proof_or_derivation_not_result` — The perturbation proof uses the continuous spectral-projector homotopy and the displayed arcsine bound.
  - `DK-8.2-thm.residual-reduction` — `proof_or_derivation_not_result` — The residual form is reduced by changing the complementary perturbation block while preserving the residual/spectral data.
  - `DK-8.2-thm.sin2-unequal-dimension-extension` — `post_result_scope_remark_not_in_printed_statement` — The source states a sin2 extension to unequal comparison dimensions.
  - `DK-8.2-thm.no-tan2-unequal-dimension-extension-known` — `historical_knowledge_state` — No analogous tan2 extension was known.
- Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.


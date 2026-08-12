# Davis--Kahan 1970 hostile closure audit — 2026-08-12

Base audited: `2a728278a585`.

## Current verdict

**Do not claim 100% source formalization from this base.** The exact directed and ambient Section 2 tan(2 Theta) source wrappers are now closed, but a hostile semantic re-audit found additional holes elsewhere. The maintained status machinery has therefore been reopened rather than preserving the previous all-terminal snapshot.

This audit separates three independent axes:

- `status`: whether the current source-facing implementation is believed mathematically exact;
- `verification`: whether the registered Lean declarations resolve in the production build;
- `completion_certification`: whether the complete hashed public source passage has survived adversarial semantic review.

A row contributes to a 100% claim only when the statement map marks it as a completion obligation, `status` is `compiled_exact` or `refuted_as_transcribed`, `verification` is `proved_in_build`, and `completion_certification` is `accepted`.

Current explicit completion obligations: **46**. Hostile-certified terminal passages: **14** (13 exact + 1 refuted). Reopened obligations: **32**.

Question 10.4 is intentionally counted as a mixed completion obligation. Its final general-functional-calculus question is open, but the same source block states established step-function/projection identities and tan(2 Theta) specializations. The old rule that exempted every `DK-10.*` row was therefore unsound.

## Passages currently accepted by the hostile audit

`S2-sin-theta`, `S2-sin-two-theta`, `S2-tan-two-theta`, `DK-3.2-def`, `DK-3.1-thm`, `DK-3.1-cor`, `DK-3.2-cor`, `DK-4.1-cor`, `DK-4.4-prop`, `DK-5.1-lem`, `DK-6.1-lem`, `DK-6.2-lem`, `DK-6.1-thm`, `DK-6.3-lem`.

Acceptance here means only that this hostile pass found no concrete semantic hole in the registered passage. It is not permanent: any change to the public source specification or source-facing theorem surface should trigger re-audit.

## Reopened obligations

| ID | Source status | Verification | Hostile certification | Known hole(s) |
| --- | --- | --- | --- | --- |
| `S1-block-residual` | `partial_or_wrapper_missing` | `proved_in_build` | `reopened_math` | The registered TeX includes the standard residual-to-eigenvalue consequence: ordered eigenvalues lambda_j with sum_j (alpha_j-lambda_j)^2 <= \|\|R\|\|_sq^2 and \|alpha_j-lambda_j\| <= \|\|R\|\|_1. The hostile review found no source-facing Lean declaration for these displayed conclusions.<br>`equation1_8_residual_norm_minimized_by_rayleighQuotient` now proves the printed Rayleigh--Ritz minimization statement but is not registered as primary evidence for this row. |
| `S1-ui-norms` | `source_spec_incomplete` | `proved_in_build` | `reopened_source_spec` | The distributable TeX omits the unnumbered cosine-law identity immediately following source equation (1.14).<br>The TeX preserves U = exp(J Theta) = cos Theta + J sin Theta in the general Hilbert-space setup. The source-facing arbitrary-dimensional surface proves the cosine/sine resolution, while the explicit exponential identity located by the hostile review is finite-dimensional. |
| `S2-tan-theta` | `compiled_exact` | `proved_in_build` | `reopened_mapping` | The mapped real ambient declaration accepts an explicit transversality premise. A source-hypotheses-only real theorem (`tanTheta_wholeSpace_paperUINorm_real_of_crossedDefectsEquivalent`) exists, so this is evidence-selection debt rather than missing mathematics. |
| `S2-sharpness` | `compiled_exact` | `proved_in_build` | `reopened_mapping` | The hashed passage asserts optimal constants, two-dimensional equality models, direct-sum simultaneous equality for all unitary-invariant norms, and first-order sharpness. Existing sharpness machinery is richer than the current review mapping, but these separable claims are not individually certified. |
| `S2-unbounded-scope` | `compiled_exact` | `proved_in_build` | `reopened_mapping` | The passage asserts the full infinite-dimensional/unbounded/arbitrary-UI-norm scope for all four headline theorem families. The current evidence is a sample of endpoints rather than an explicit clause-by-clause four-family scope certificate. |
| `DK-3.1-def` | `compiled_exact` | `proved_in_build` | `reopened_mapping` | The block contains equations (3.1)-(3.4), unitarity block identities, singular-value/nullity assertions, and the direct-rotation definition. The current generic `.whole` clause does not certify those assertions individually. |
| `DK-3.1-prop` | `compiled_exact` | `proved_in_build` | `reopened_mapping` | Primary evidence is complex-centric even though the paper ambient convention is real or complex and real counterparts exist elsewhere in the census. Register exact real evidence explicitly. |
| `DK-3.2-prop` | `partial_or_wrapper_missing` | `proved_in_build` | `reopened_math` | The source passage says that on the two crossing subspaces every direct rotation satisfies U^2 x = -x. The hostile review did not find an exported source-facing theorem with that statement, although related reflection-product ingredients exist. |
| `DK-3.3-prop` | `source_spec_incomplete` | `proved_in_build` | `reopened_source_spec` | The anchor promises equations (3.6)-(3.8), but the distributable TeX skips source equation (3.7), the explicit block formula for Q in terms of C_0 and S_0. |
| `DK-3.4-prop` | `compiled_specialization` | `proved_in_build` | `reopened_math` | `proposition3_4_source_full` is explicitly complex-valued. The paper does not restrict Proposition 3.4 to the complex scalar field; an exact real source-facing counterpart was not located. |
| `DK-3.5-prop` | `partial_or_wrapper_missing` | `proved_in_build` | `reopened_math` | The registered passage includes the Hilbert-space identity U = exp(J Theta). The source-facing arbitrary-dimensional Proposition 3.5 surface exposes U = cos Theta + J sin Theta; the explicit exponential theorem located by the review is finite-dimensional. |
| `DK-4.1-prop` | `source_spec_incomplete` | `proved_in_build` | `reopened_source_spec` | The TeX anchor says it covers source equations (4.1)-(4.2) but only paraphrases them. The explicit minimax formula (4.1) and pointwise vector-angle inequality (4.2) are missing from the distributable specification. |
| `DK-4.2-prop` | `compiled_exact` | `proved_in_build` | `reopened_mapping` | The main inequality appears formalized, but the source block also records the trace/basis identification used in the proof. The terminal row does not separately bind that preserved mathematical assertion to Lean evidence. |
| `DK-4.3-prop` | `compiled_exact` | `proved_in_build` | `reopened_mapping` | Broader nonacute and real source theorems exist, but the primary row evidence is narrower and the hashed block contains equations (4.3)-(4.6) plus the precise UI-norm limitation. Rebind/atomize the complete source scope. |
| `DK-5.1-thm` | `compiled_exact` | `proved_in_build` | `reopened_mapping` | The source block includes the Banach-space inverse-norm form, A/B interchange, and unbounded-left extension. The repository contains strong infrastructure and literal wrappers, but the audit row does not atomically show that every printed clause is represented at real/complex source scope. |
| `DK-5-hermitian-inequalities` | `partial_or_wrapper_missing` | `proved_in_build` | `reopened_math` | The TeX states that (5.2) is not best possible unless rank C <= 1. The repository formalizes (5.1), the rank-corrected estimate, and a counterexample showing constant 1 is too small, but the hostile review found no source-facing theorem for this stronger qualitative assertion.<br>The same block asks whether the rank factor can be replaced by a universal constant. That open question should be atomically dispositioned instead of being swallowed by a terminal `.whole` clause. |
| `DK-5.2-thm` | `compiled_exact` | `proved_in_build` | `reopened_mapping` | The theorem appears available in both scalar fields, but primary evidence is not explicitly bound clause-by-clause to the paper's full real/complex source scope. |
| `DK-6.1-prop` | `compiled_exact` | `proved_in_build` | `reopened_mapping` | The source block contains the Sylvester identity (6.1), Proposition 6.1, and an explicit 2x2 counterexample showing the ambient one-sided sine conclusion fails. The counterexample exists elsewhere but is not registered as evidence for this row. |
| `DK-6.2-thm` | `compiled_exact` | `proved_in_build` | `reopened_mapping` | The source passage contains both the Hilbert--Schmidt theorem and its rank-corrected operator-norm consequence. Exact rank-consequence declarations exist but are not mapped into the row's semantic audit clauses. |
| `DK-6.3-thm` | `partial_or_wrapper_missing` | `proved_in_build` | `reopened_math` | The generalized tangent theorem itself appears covered, but the same hashed passage preserves Example 6.1: delta=1, tangent quantity 1, residual 1/sqrt(2) when spectral mass lies on the wrong side. The hostile review did not find an exact source-facing formalization of that explicit counterexample. |
| `DK-6-appendix` | `compiled_exact` | `proved_in_build` | `reopened_mapping` | The TeX explicitly preserves equations (6.7)-(6.11) and the limiting proof chain. The row maps endpoint/common-domain machinery and historically treats parts of the chain as documentation fidelity; under statement-level 100% coverage, every preserved mathematical equation needs explicit evidence/disposition. |
| `DK-7-sin2-proof` | `compiled_exact` | `proved_in_build` | `reopened_mapping` | The block contains equations (7.1)-(7.5), reflected diagonalization, the factor-one directed residual refinement, swap asymmetry, and a counterexample. The current clauses do not explicitly account for every separable identity/assertion. |
| `DK-7-tan2-proof` | `compiled_exact` | `proved_in_build` | `reopened_mapping` | The exact directed/ambient tan(2 Theta) endpoints are now closed. The proof block still contains equation (7.6), scalar singular-vector inequality, pole exclusion as a conclusion, Fan-dominance steps, and both endpoints under one coarse audit clause; atomize these for static semantic certification. |
| `DK-8.1-thm` | `compiled_exact` | `proved_in_build` | `reopened_mapping` | The theorem is usefully split into branch/(i)/(ii)/(iii), but primary evidence remains complex-centric while real counterparts exist. Bind each source conclusion explicitly in both source scalar fields. |
| `DK-8.2-thm` | `compiled_exact` | `proved_in_build` | `reopened_mapping` | A single `.whole` clause covers two alternative half-gap hypotheses, branch selection, homotopy, perturbation and residual forms, unequal-dimensional extension, and the source statement that no analogous tan(2 Theta) extension is known. These need atomic evidence/dispositions. |
| `DK-9-model` | `source_spec_incomplete` | `proved_in_build` | `reopened_source_spec` | The source transcription used in the hostile review has alpha_1=alpha_2=0 < alpha_3 < alpha_4 < ... . The distributable TeX weakens this to alpha_1=alpha_2=0 and says only that positive eigenvalues are determined by the free-beam equation and exceed 500. Re-audit the original PDF to decide whether the printed indexing asserts simplicity of all positive eigenvalues; do not choose the weaker reading to fit current Lean coverage. |
| `DK-9.1-9.4` | `compiled_exact` | `proved_in_build` | `reopened_mapping` | The primary mapped `equation_9_*` declarations are largely arithmetic wrappers conditional on analytic bounds. Genuine unconditional beam-model sine/sin(2 Theta) theorems exist elsewhere and should be the source evidence for the actual Section 9 conclusions. |
| `DK-9.5-9.7` | `compiled_exact` | `proved_in_build` | `reopened_mapping` | The current primary mapping emphasizes numerical wrappers rather than the genuine beam tangent/double-tangent theorems that discharge the analytic hypotheses. Rebind the row to the unconditional source-facing model results. |
| `DK-9.8` | `source_spec_incomplete` | `proved_in_build` | `reopened_source_spec` | The source comparison includes the asymptotic alpha_hat_k - alpha_check_k = (eps^2/30)/(500-alpha_hat_k) - O(eps^4), which is absent from the distributable TeX; the Lean comparison module explicitly says this asymptotic is intentionally not encoded.<br>The TeX asserts Weinberger's sine-square estimate and the Lehmann claim that the two lower arrowhead eigenvalues are the best lower bounds from the stated data. The repository proves the final (9.8) numbers by a sharper Davis--Kahan route and formalizes algebraic pieces conditionally, but explicitly leaves the historical Weinberger/Lehmann derivation/optimality unproved. |
| `DK-9-infinite-residual-counterexample` | `partial_or_wrapper_missing` | `proved_in_build` | `reopened_math` | The source says an arbitrarily small modification repairs the domain defect. Lean proves finite truncations lie in the operator domain and agree on every fixed prefix, but the hostile review did not find a norm-convergence/arbitrarily-small-perturbation theorem for those truncations. |
| `DK-9.9-9.11` | `compiled_exact` | `proved_in_build` | `mixed_disposition` | The numerical/Schur-complement conclusions appear formalized, but the block ends with a source assertion that the 3x3 comparison angle is the best possible bound obtainable from the stated data while explicitly deferring its proof to unresolved Question 10.2. Record that assertion separately as source-asserted/unproved rather than counting the entire block as exact. |
| `DK-10.4` | `partial_or_wrapper_missing` | `proved_in_build` | `mixed_disposition` | Question 10.4 is not a pure open-question block. Before the general-f question it states established step-function identities f(A)=P, f(A+H)=Q, f(A0)=I, the projector/sine identities, and the ambient/directed tan(2 Theta) bounds. The tan(2 Theta) bounds now have exact complex/real wrappers, but the functional-calculus identities are not atomically registered.<br>The previous checker exempted every DK-10.* row by identifier. This let established mathematics inside the Question 10.4 block escape the completion count. The row is now a mixed completion obligation until established clauses are explicitly covered and the final question separately marked open. |

## Severity buckets

### Source-specification fidelity must be repaired first

These rows cannot be certified from the checked-in TeX as written because the public specification itself is incomplete, weakened, or ambiguous: `S1-ui-norms`, `DK-3.3-prop`, `DK-4.1-prop`, `DK-9-model`, `DK-9.8`.

The known concrete defects include the missing source equations (3.7), (4.1), and (4.2), the omitted cosine-law statement after (1.14), the omitted Section 9 asymptotic surrounding (9.8), and the need to adjudicate the printed positive-eigenvalue indexing in the free-beam model against the original PDF.

### Source-facing mathematical statements still missing or too narrow

These rows have at least one preserved mathematical assertion for which this audit did not find an exact source-facing Lean statement: `S1-block-residual`, `DK-3.2-prop`, `DK-3.4-prop`, `DK-3.5-prop`, `DK-5-hermitian-inequalities`, `DK-6.3-thm`, `DK-9-infinite-residual-counterexample`.

The highest-value examples are the Section 1 residual-to-eigenvalue consequence, the arbitrary-dimensional exponential direct-rotation identity, Proposition 3.2 on the crossing subspaces, the real scalar scope of Proposition 3.4, the stronger qualitative limitation surrounding (5.2), Example 6.1, and the norm-small repair assertion in the Section 9 unbounded-residual example.

### Mathematics likely exists, but the certificate does not prove correspondence

These rows are reopened for evidence-selection or atomization rather than a known deep theorem gap: `S2-tan-theta`, `S2-sharpness`, `S2-unbounded-scope`, `DK-3.1-def`, `DK-3.1-prop`, `DK-4.2-prop`, `DK-4.3-prop`, `DK-5.1-thm`, `DK-5.2-thm`, `DK-6.1-prop`, `DK-6.2-thm`, `DK-6-appendix`, `DK-7-sin2-proof`, `DK-7-tan2-proof`, `DK-8.1-thm`, `DK-8.2-thm`, `DK-9.1-9.4`, `DK-9.5-9.7`.

The recurring failure mode is a generic `.whole` audit clause covering several separable identities/conclusions while the row points at only a subset or at a conditional arithmetic wrapper rather than the source-facing model theorem. These should be repaired by atomic claim clauses and exact declaration bindings, not by declaring the entire row terminal on reputation.

### Mixed semantic dispositions

These blocks combine established mathematics with open or source-attributed/unproved claims and therefore cannot be represented honestly by one terminal status: `DK-9.9-9.11`, `DK-10.4`.

## Regression: tan(2 Theta) really is closed

`S2-tan-two-theta` remains `compiled_exact` / `proved_in_build` / `accepted`. The current base contains exact complex and real ambient wrappers and exact complex and real directed-residual wrappers from the printed hypotheses, deriving pole exclusion internally. The hostile status reset does **not** reopen that repaired theorem.

## Hard gate

Run:

```bash
python3 scripts/check_davis_kahan_1970_statement_map.py
python3 scripts/check_davis_kahan_1970_statement_map.py --require-terminal
```

The first command should pass as an internal-consistency check. The second is expected to **fail** while any explicit completion obligation lacks hostile certification `accepted`. That failure is the intended guard against another premature 100% claim.

Once every reopened source-specification issue is repaired against the original paper, every missing/narrow source statement is compiled, every coarse audit block is atomized, and every completion obligation is independently promoted to `accepted`, the hard gate may become green. Until then the repo should describe itself as having extensive compiled coverage with a deliberately reopened semantic completion audit.

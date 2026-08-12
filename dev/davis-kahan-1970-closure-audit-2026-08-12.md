# Davis--Kahan 1970 hostile closure audit — 2026-08-12

Base audited: `2a728278a585`.

## Current verdict

> **Result-denominator pivot (2026-08-12).** The hostile audit below was intentionally broader than the project's final definition of 100%: it treated many preserved mathematical assertions as possible completion obligations. That was useful for finding source-fidelity defects, but it is **not** the formalization denominator. The current hard denominator is `dev/davis-kahan-1970-formalization-result-inventory.json`: 29 results consisting of the four Section 2 headline theorems and every theorem/proposition/lemma/corollary Davis--Kahan actually establish in Sections 3--8. Section 10 questions, explicitly deferred/unresolved claims, proof equations, examples, numerical working, and historical comparisons are source-fidelity material only. Consequently, many "reopened" findings later in this document are advisory fidelity/mapping observations rather than blockers to 100%. They must be re-evaluated against the 29 exact source statements before being promoted to result-level blockers.


**Do not claim 100% source formalization from this base.** The exact directed and ambient Section 2 tan(2 Theta) source wrappers are now closed, but a hostile semantic re-audit found additional holes elsewhere. The maintained status machinery has therefore been reopened rather than preserving the previous all-terminal snapshot.

This audit separates three independent axes:

- `status`: whether the current source-facing implementation is believed mathematically exact;
- `verification`: whether the registered Lean declarations resolve in the production build;
- `completion_certification`: whether the complete hashed public source passage has survived adversarial semantic review.

The 49 rows are organizational groups and the 266 atoms are a source-fidelity inventory. The 100% completion denominator is the separate 29-result inventory. The broader row/atom findings below remain useful adversarial evidence, but only defects in the exact statement or scope of one of those 29 results block the formalization claim.

Current maintained result denominator: **29**. Exact printed-result boundary reviews: **29/29 accepted**. Current result-level semantic terminality: **18/29**; the remaining **11** are the mathematics/review queue. The old 46-row/32-reopened counts below are retained only as historical evidence from the broader pre-pivot hostile audit and are not the current completion metric.

`DK-3.1-prop` is now result-level terminal: `TauCeti.DavisKahan1970.proposition3_1_source` packages the already-proved generic acute direct-rotation existence, uniqueness, positive diagonal blocks, crossed-block identity, and property-(i)-alone characterization at the paper's printed `TauCeti.IsAcute` hypothesis.

A result-only re-audit now also closes `DK-3.2-prop`, `DK-3.5-prop`, `DK-4.2-prop`, `DK-5.1-thm`, `DK-6.1-prop`, and `DK-6.2-thm` by selecting the already-compiled declarations that correspond exactly to their narrowed printed statements. `DK-4.1-prop` remains open for one specific source-scope bridge: the arbitrary-dimensional compact/nonacute identity giving the direct rotation approximation values as `2 * sin(theta_k / 2)`. Its pointwise and minimality clauses are already present.

### Agent 3 source-denominator update

A direct PDF/source-order re-audit established **266 source-fidelity atoms** and explicit coverage of all **64 numbered equations**. Those atoms are an omission-detection layer, not Lean proof obligations. The formalization denominator is the separate set of **29 results Davis--Kahan actually establish**.

This re-audit also repaired the five source-specification defects identified by the hostile pass: the cosine-law identity after (1.14), equation (3.7), equations (4.1)--(4.2), the strict Section 9 ordering `alpha_1 = 0 = alpha_2 < alpha_3 < alpha_4 < ...`, and the lower-bound `O(epsilon^4)` asymptotic before (9.8). Those rows remain red where mathematical or atom-to-Lean evidence still needs work; they are no longer red merely because the distributable TeX omitted the source material.

Question 10.4 remains faithfully inventoried, but it is **not** a completion obligation under the final policy: Section 10 is open-question material. Its preceding established identities may be retained and even formalized, but they do not enlarge the result denominator unless they are part of one of the 29 designated results.

### Census tooling closure

The result-selection boundary is now itself audited and machine-checked. All 266
fidelity atoms have a specific inclusion/exclusion reason and exact reverse links
to any counted result they support. All 29 counted results have accepted boundary
reviews that partition their primary source block into printed-statement atoms and
adjacent non-result material, with cross-block scope atoms identified explicitly.
The generated independent-audit packet exposes the complete 266-atom exclusion
table to the reviewer.

Accordingly, **the census/tooling campaign is closed** unless a fresh source audit
finds an omitted result or the human explicitly changes the claim boundary. The
active completion queue is the 29-result inventory, not the broad row list below.
Future work should resolve exact source-to-Lean semantics for its nonterminal
results rather than add more census machinery.

## Historical broad hostile-audit findings

The remainder of this document records the intentionally broader hostile pass that
preceded the result-denominator pivot. It remains useful as adversarial source
fidelity and implementation advice, but statements below that call proof equations,
examples, Section 9 calculations, or Section 10 material "obligations" are
**historical terminology and are not the current 100% task list**. Consult
`dev/davis-kahan-1970-formalization-result-inventory.md` for the maintained queue.

## Passages accepted by the historical broad audit

`S2-sin-theta`, `S2-sin-two-theta`, `S2-tan-two-theta`, `DK-3.2-def`, `DK-3.1-thm`, `DK-3.1-cor`, `DK-3.2-cor`, `DK-4.1-cor`, `DK-4.4-prop`, `DK-5.1-lem`, `DK-6.1-lem`, `DK-6.2-lem`, `DK-6.1-thm`, `DK-6.3-lem`.

Acceptance here means only that this hostile pass found no concrete semantic hole in the registered passage. It is not permanent: any change to the public source specification or source-facing theorem surface should trigger re-audit.

## Historically reopened rows

| ID | Source status | Verification | Hostile certification | Known hole(s) |
| --- | --- | --- | --- | --- |
| `S1-block-residual` | `partial_or_wrapper_missing` | `proved_in_build` | `reopened_math` | The registered TeX includes the standard residual-to-eigenvalue consequence: ordered eigenvalues lambda_j with sum_j (alpha_j-lambda_j)^2 <= \|\|R\|\|_sq^2 and \|alpha_j-lambda_j\| <= \|\|R\|\|_1. The hostile review found no source-facing Lean declaration for these displayed conclusions.<br>`equation1_8_residual_norm_minimized_by_rayleighQuotient` now proves the printed Rayleigh--Ritz minimization statement but is not registered as primary evidence for this row. |
| `S1-ui-norms` | `partial_or_wrapper_missing` | `proved_in_build` | `reopened_math` | PDF re-audit restored the cosine-law identity after (1.14). The remaining issue is mathematical/scope: the source asserts U = exp(J Theta) = cos Theta + J sin Theta in general Hilbert-space scope, while the explicit exponential theorem located by the hostile review is finite-dimensional. |
| `S2-tan-theta` | `compiled_exact` | `proved_in_build` | `reopened_mapping` | The mapped real ambient declaration accepts an explicit transversality premise. A source-hypotheses-only real theorem (`tanTheta_wholeSpace_paperUINorm_real_of_crossedDefectsEquivalent`) exists, so this is evidence-selection debt rather than missing mathematics. |
| `S2-sharpness` | `compiled_exact` | `proved_in_build` | `reopened_mapping` | The hashed passage asserts optimal constants, two-dimensional equality models, direct-sum simultaneous equality for all unitary-invariant norms, and first-order sharpness. Existing sharpness machinery is richer than the current review mapping, but these separable claims are not individually certified. |
| `S2-unbounded-scope` | `compiled_exact` | `proved_in_build` | `reopened_mapping` | The passage asserts the full infinite-dimensional/unbounded/arbitrary-UI-norm scope for all four headline theorem families. The current evidence is a sample of endpoints rather than an explicit clause-by-clause four-family scope certificate. |
| `DK-3.1-def` | `compiled_exact` | `proved_in_build` | `reopened_mapping` | The block contains equations (3.1)-(3.4), unitarity block identities, singular-value/nullity assertions, and the direct-rotation definition. The current generic `.whole` clause does not certify those assertions individually. |
| `DK-3.1-prop` | `compiled_exact` | `proved_in_build` | `reopened_mapping` | Primary evidence is complex-centric even though the paper ambient convention is real or complex and real counterparts exist elsewhere in the census. Register exact real evidence explicitly. |
| `DK-3.2-prop` | `partial_or_wrapper_missing` | `proved_in_build` | `reopened_math` | The source passage says that on the two crossing subspaces every direct rotation satisfies U^2 x = -x. The hostile review did not find an exported source-facing theorem with that statement, although related reflection-product ingredients exist. |
| `DK-3.3-prop` | `partial_or_wrapper_missing` | `proved_in_build` | `reopened_mapping` | Equation (3.7) is now restored exactly in the distributable TeX. The source-specification defect is closed; bind the new (3.7) atom and the other Proposition 3.3 atoms explicitly to Lean evidence. |
| `DK-3.4-prop` | `compiled_specialization` | `proved_in_build` | `reopened_math` | `proposition3_4_source_full` is explicitly complex-valued. The paper does not restrict Proposition 3.4 to the complex scalar field; an exact real source-facing counterpart was not located. |
| `DK-3.5-prop` | `partial_or_wrapper_missing` | `proved_in_build` | `reopened_math` | The registered passage includes the Hilbert-space identity U = exp(J Theta). The source-facing arbitrary-dimensional Proposition 3.5 surface exposes U = cos Theta + J sin Theta; the explicit exponential theorem located by the review is finite-dimensional. |
| `DK-4.1-prop` | `partial_or_wrapper_missing` | `proved_in_build` | `reopened_mapping` | Equations (4.1) and (4.2) are now restored explicitly in the distributable TeX. The source-specification defect is closed; bind the minimax, pointwise-angle, and headline proposition atoms explicitly to Lean evidence. |
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
| `DK-8.1-thm` | `compiled_exact` | `proved_in_build` | `accepted` | Result-only review confirms complete complex and real source-facing coverage of the branch characterization/existence and parts (i)--(iii); the earlier mapping blocker was stale. |
| `DK-8.2-thm` | `compiled_exact` | `proved_in_build` | `reopened_mapping` | A single `.whole` clause covers two alternative half-gap hypotheses, branch selection, homotopy, perturbation and residual forms, unequal-dimensional extension, and the source statement that no analogous tan(2 Theta) extension is known. These need atomic evidence/dispositions. |
| `DK-9-model` | `partial_or_wrapper_missing` | `proved_in_build` | `reopened_math` | PDF re-audit confirms the paper prints alpha_1 = 0 = alpha_2 < alpha_3 < alpha_4 < ...; the TeX now preserves that strict multiplicity-aware ordering. Formalization must justify the resulting positive-eigenvalue simplicity/multiplicity claim rather than weakening the source. |
| `DK-9.1-9.4` | `compiled_exact` | `proved_in_build` | `reopened_mapping` | The primary mapped `equation_9_*` declarations are largely arithmetic wrappers conditional on analytic bounds. Genuine unconditional beam-model sine/sin(2 Theta) theorems exist elsewhere and should be the source evidence for the actual Section 9 conclusions. |
| `DK-9.5-9.7` | `compiled_exact` | `proved_in_build` | `reopened_mapping` | The current primary mapping emphasizes numerical wrappers rather than the genuine beam tangent/double-tangent theorems that discharge the analytic hypotheses. Rebind the row to the unconditional source-facing model results. |
| `DK-9.8` | `partial_or_wrapper_missing` | `proved_in_build` | `reopened_math` | The lower-bound comparison and O(epsilon^4) asymptotic preceding (9.8) are now restored in the TeX. Remaining mathematical obligations include the Weinberger sine-square statement, Lehmann best-lower-bound assertion, the restored asymptotic, and the final (9.8) conclusions, each with an explicit disposition. |
| `DK-9-infinite-residual-counterexample` | `partial_or_wrapper_missing` | `proved_in_build` | `reopened_math` | The source says an arbitrarily small modification repairs the domain defect. Lean proves finite truncations lie in the operator domain and agree on every fixed prefix, but the hostile review did not find a norm-convergence/arbitrarily-small-perturbation theorem for those truncations. |
| `DK-9.9-9.11` | `compiled_exact` | `proved_in_build` | `mixed_disposition` | The numerical/Schur-complement conclusions appear formalized, but the block ends with a source assertion that the 3x3 comparison angle is the best possible bound obtainable from the stated data while explicitly deferring its proof to unresolved Question 10.2. Record that assertion separately as source-asserted/unproved rather than counting the entire block as exact. |
| `DK-10.4` | `partial_or_wrapper_missing` | `proved_in_build` | `mixed_disposition` | Under the final result-level policy this is source-fidelity material, not a completion obligation. Question 10.4 is an open Section 10 question; its preceding functional-calculus identities remain faithfully inventoried but do not enlarge the 29-result denominator. |

## Severity buckets

### Historical source-specification fidelity findings

The concrete source-spec defects found by the hostile review are repaired in the distributable TeX: the cosine law after (1.14), equations (3.7), (4.1), and (4.2), the strict Section 9 eigenvalue ordering, and the asymptotic preceding (9.8). The source-side denominator is now recorded atomically in `dev/davis-kahan-1970-source-atom-inventory.json`.

This does **not** certify the corresponding Lean mathematics. In particular `S1-ui-norms`, `DK-9-model`, and `DK-9.8` remain mathematical obligations, while `DK-3.3-prop` and `DK-4.1-prop` remain atom-to-evidence mapping obligations. A future source re-audit can still discover additional omissions; if it does, add an atom rather than shrinking the denominator.

### Source-facing mathematical statements still missing or too narrow

These rows have at least one preserved mathematical assertion for which this audit did not find an exact source-facing Lean statement: `S1-block-residual`, `S1-ui-norms`, `DK-3.2-prop`, `DK-3.4-prop`, `DK-3.5-prop`, `DK-5-hermitian-inequalities`, `DK-6.3-thm`, `DK-9-model`, `DK-9.8`, `DK-9-infinite-residual-counterexample`.

The highest-value examples are the Section 1 residual-to-eigenvalue consequence, the arbitrary-dimensional exponential direct-rotation identity, Proposition 3.2 on the crossing subspaces, the real scalar scope of Proposition 3.4, the stronger qualitative limitation surrounding (5.2), Example 6.1, and the norm-small repair assertion in the Section 9 unbounded-residual example.

### Mathematics likely exists, but the certificate does not prove correspondence

These rows are reopened for evidence-selection or atomization rather than a known deep theorem gap: `S2-tan-theta`, `S2-sharpness`, `S2-unbounded-scope`, `DK-3.1-def`, `DK-3.3-prop`, `DK-4.1-prop`, `DK-4.2-prop`, `DK-4.3-prop`, `DK-5.1-thm`, `DK-5.2-thm`, `DK-6.1-prop`, `DK-6.2-thm`, `DK-6-appendix`, `DK-7-sin2-proof`, `DK-7-tan2-proof`, `DK-8.2-thm`, `DK-9.1-9.4`, `DK-9.5-9.7`.

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

The currently identified source-specification omissions have been repaired against the original paper. Once every remaining missing/narrow source statement is compiled, every atom is bound to exact evidence or another honest source disposition, and every completion obligation is independently promoted to `accepted`, the hard gate may become green. Any future PDF re-audit that discovers a missed source assertion must add a new atom rather than shrinking or silently redefining the denominator. Until then the repo should describe itself as having extensive compiled coverage with a deliberately reopened semantic completion audit.

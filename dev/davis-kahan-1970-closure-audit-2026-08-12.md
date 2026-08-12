# Davis--Kahan 1970 closure audit -- 2026-08-12

This is a source-fidelity re-audit, not a restatement of the census.  Its clause
baseline is the source-first transcription audit of 2026-08-09, including that
audit's section-by-section list of hypotheses and conclusions.  Each finding in
that audit was checked against the current source-facing declarations and the
maintained resolution notes.  The three Section 4 findings raised by the final
review were then checked directly against the new theorem signatures.

The non-distributable transcription is not present in this checkout, so this
re-audit does not pretend to have re-read the private source independently.  It
uses the earlier audit's transcription-derived clause inventory as its fixed
source baseline.  The current census was used only after the declaration review,
to check that its status agrees with the result.

## Verdict

Excluding the four questions in Section 10, all 45 tracked mathematical
obligations have a terminal source-faithful outcome:

- 44 are `compiled_exact` and `proved_in_build`;
- Proposition 4.4 is `refuted_as_transcribed` by a compiled counterexample that
  satisfies its printed real-space and angle hypotheses.

No `compiled_specialization` row remains.  The four questions are reported
separately: Question 10.1 has a compiled modern resolution, while Questions
10.2--10.4 are not theorem-completion obligations.

## Clause review

For every row below, the review checked the hypotheses, scalar field,
finite/arbitrary dimension, compactness, acute versus matched-defect nonacute
scope, finite versus infinite sums, existence assertions, and the stated
conclusion.  The row identifiers are grouped only for readability.

| Source part | Rows reviewed | Result |
| --- | --- | --- |
| Sections 1--2 | `S1-block-residual`, `S1-ui-norms`; `S2-sin-theta`, `S2-tan-theta`, `S2-sin-two-theta`, `S2-tan-two-theta`, `S2-sharpness`, `S2-unbounded-scope` | Exact |
| Section 3 | `DK-3.1-def`, `DK-3.2-def`, `DK-3.1-prop`, `DK-3.2-prop`, `DK-3.3-prop`, `DK-3.4-prop`, `DK-3.1-thm`, `DK-3.1-cor`, `DK-3.5-prop`, `DK-3.2-cor` | Exact |
| Section 4 | `DK-4.1-prop`, `DK-4.1-cor`, `DK-4.2-prop`, `DK-4.3-prop` | Exact |
| Section 4 | `DK-4.4-prop` | Refuted as printed |
| Section 5 | `DK-5.1-thm`, `DK-5-hermitian-inequalities`, `DK-5.2-thm`, `DK-5.1-lem` | Exact |
| Section 6 and appendix | `DK-6.1-lem`, `DK-6.2-lem`, `DK-6.1-prop`, `DK-6.1-thm`, `DK-6.2-thm`, `DK-6.3-thm`, `DK-6-appendix`, `DK-6.3-lem` | Exact |
| Section 7 | `DK-7-sin2-proof`, `DK-7-tan2-proof` | Exact |
| Section 8 | `DK-8.1-thm`, `DK-8.2-thm` | Exact |
| Section 9 | `DK-9-model`, `DK-9.1-9.4`, `DK-9.5-9.7`, `DK-9.8`, `DK-9-infinite-residual-counterexample`, `DK-9.9-9.11` | Exact |

## Final Section 4 review

The last three specialization findings are discharged as follows.

1. Proposition 4.1 now has both printed formulations.  A reusable compact
   positive spectral selector realizes every positive approximation number by
   an orthonormal eigenvector, including repeated eigenvalues and finite-rank
   exhaustion.  Applied to the principal-sine Gram operator, it supplies
   orthonormal `v_k` with the required vector-angle lower bound.  Zero principal
   angles are omitted from the selector because their lower bound is automatic.
   The combined complex and real source wrappers also carry compactness and a
   chosen equivalence of the crossed defect spaces, so they include the
   nonacute matched-defect case as well as the singular-value formulation.

2. Corollary 4.1 now has complex and real compact matched-defect wrappers.  They
   conclude both ideal membership and minimality for every Ky-Fan-dominant
   unitarily invariant gauge; neither wrapper assumes acuteness.

3. Proposition 4.3 now uses the chosen matched-defect direct rotation in the
   block-pinching argument.  Complex and real source wrappers cover the compact
   nonacute scope and every Ky-Fan-dominant unitarily invariant gauge.  The
   conclusion remains Ky Fan/UI-gauge majorization, not the false pointwise
   approximation-number strengthening that would imply Proposition 4.4.

The source census declaration probe resolves all 999 named declarations against
`DavisKahan.All`.  The generated census therefore records 44 exact proofs, one
source-level refutation, and no remaining mathematical completion obligation
outside Section 10's questions.

# Davis--Kahan 1970 closure audit -- 2026-08-12

This is a source-fidelity re-audit, not a restatement of the census.  Its clause
baseline is the source-first transcription audit of 2026-08-09, including that
audit's section-by-section list of hypotheses and conclusions.  Each finding in
that audit was checked against the current source-facing declarations and the
maintained resolution notes.  The three Section 4 findings raised by the final
review, the Definition 3.2 infinite-dimensional separation witness, and the two
scope remarks attached to Theorem 5.1 were then checked directly against the
new theorem signatures.

The full non-distributable transcription is not present in this checkout.  The
repository now carries the exact mathematical excerpts used by this audit in
`prose/distilled_literature/DavisKahan1970_exact_source_register.tex`, with line-range and
SHA-256 provenance in `dev/davis-kahan-1970-statement-map.json`.  The static
statement-map checker can additionally compare those excerpts against the
private transcription when a local path is supplied.  The current census was
used only after declaration review, to check that its status agrees with the
result.

For an independent re-audit, generate a clean compiler certificate with
`scripts/certify_davis_kahan_1970.py --clean` and use
`dev/davis-kahan-1970-independent-audit-prompt.md`.  The certificate establishes
compilation and declaration types; semantic equivalence to the source remains a
separate row-by-row judgement.

## Current verdict after exact-wrapper closure

The independent source-first review on 2026-08-12 correctly reopened the unrestricted
Section 2 `tan 2 Theta` row because the then-registered ambient theorem still accepted
explicit pole exclusion and the directed residual conclusion was only exposed through
narrower specializations.  Both issues are now closed at the source-facing layer.

The ambient complex and real wrappers
`tanTwoTheta_wholeSpace_paperUINorm_exact` and
`tanTwoTheta_wholeSpace_paperUINorm_real_exact` take only the printed ordered-gap,
invariance, and off-diagonal hypotheses and derive pole exclusion internally.  The
directed residual complex wrapper
`tanTwoTheta_directedCorner_residual_paperUINorm_exact` upgrades the branch-free
all-Ky-Fan Section 7 specialization to every source unitarily invariant norm and also
derives pole exclusion from the printed hypotheses.  Its real counterpart
`tanTwoTheta_directedCorner_residual_paperUINorm_real_exact` uses the repository's
canonical complexification convention for real directed angles and descends the
residual norm exactly to the real projection block.

A repository-wide semantic search before adding the directed wrappers found no hidden
source-facing theorem with this exact signature under an unregistered name.  The nearest
existing results were the explicit-`hcos` Ky Fan directed corner estimate, a real
graph-coordinate/witness specialization, and the already-closed ambient theorem.

Excluding the four questions in Section 10, the maintained 45 mathematical completion
obligations therefore consist of:

- 44 `compiled_exact` / `proved_in_build` rows;
- Proposition 4.4, `refuted_as_transcribed` / `proved_in_build`.

This is the terminal source-statement inventory.  The Section 10 questions remain
source-accounting entries rather than theorem-completion obligations.  A fresh local
`lake build DavisKahan.All` plus the census declaration probe remains the compiler-side
validation required after changing the exact wrappers.

## Clause review

For every row below, the review checked the hypotheses, scalar field,
finite/arbitrary dimension, compactness, acute versus matched-defect nonacute
scope, finite versus infinite sums, existence assertions, and the stated
conclusion.  The row identifiers are grouped only for readability.

| Source part | Rows reviewed | Result |
| --- | --- | --- |
| Sections 1--2 | `S1-block-residual`, `S1-ui-norms`; `S2-sin-theta`, `S2-tan-theta`, `S2-sin-two-theta`, `S2-sharpness`, `S2-unbounded-scope` | Exact |
| Section 2 | `S2-tan-two-theta` | Exact: directed residual and ambient source wrappers, complex and real, from printed hypotheses only |
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

## Definition 3.2 and Theorem 5.1 review

The earlier closure audit inherited two stale claims from the census.  Both are
now discharged in the build rather than treated as prose-only facts.

1. Definition 3.2 is separated from uniform acuteness by a concrete pair in
   `ℓ²(ℕ × Bool, 𝕜)`, uniformly over every `RCLike` scalar field.  The two closed
   subspaces have both crossed intersections zero, while unit coordinate vectors
   have projection norms `1 / (n + 2)`.  Hence their projection gap is exactly
   one.  The audit instantiates the result over both `ℝ` and `ℂ`.

2. Theorem 5.1 includes the printed `A`/`B` interchange companion and its
   densely-defined unbounded-`A` extension.  The reusable Banach theorem needs
   only a bounded left inverse, which is weaker than the paper's literal
   two-sided `A^{-1}` hypothesis.  The source layer now additionally contains
   literal bounded wrappers carrying a two-sided inverse and its printed norm
   bound, so an auditor can compare the theorem statement without inferring that
   specialization.  These new wrappers must be compiler-certified by the clean
   certificate run before they are used as compiler evidence.

The source census declaration probe is the compiler-backed guard for named
declarations.  After the exact-wrapper repair the census has no nonterminal mathematical rows.  A clean build and declaration probe remain required to validate that the registered exact wrappers elaborate at their stated types.

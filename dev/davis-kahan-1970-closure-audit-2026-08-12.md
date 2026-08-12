# Davis--Kahan 1970 closure audit -- 2026-08-12

This is a source-fidelity re-audit, not a restatement of the census.  Its
semantic baseline is the checked-in transformative source specification
`prose/distilled_literature/DavisKahan1970_part_III.tex`, whose 49 `DK-CERT`
passages preserve the paper's mathematical presentation order and the
hypotheses, conclusions, formulas, exceptions, and scope needed for static
source-to-Lean comparison.  The maintained census is treated as a claim to test,
not as evidence.

No private modernized transcription is required by this audit or by the
certificate tooling.  A lawful copy of the original paper or a private
transcription may be used separately to re-audit the fidelity of
`DavisKahan1970_part_III.tex` itself.  The statement map hashes the checked-in
TeX passages directly, so ordinary static certification remains possible if the
private transcription is unavailable.

For an independent re-audit, generate a clean compiler certificate with
`scripts/certify_davis_kahan_1970.py --clean` and use
`dev/davis-kahan-1970-independent-audit-prompt.md`.  The certificate establishes
compilation and declaration types; semantic equivalence to the source remains a
separate row-by-row judgement.

## Current verdict after incorporating `cab61ab7`

The latest source-facing repair closes the **ambient** half of the unrestricted
Section 2 `tan 2 Theta` theorem.  The declarations
`tanTwoTheta_wholeSpace_paperUINorm_exact` and
`tanTwoTheta_wholeSpace_paperUINorm_real_exact` cover complex and real Hilbert
spaces respectively, take only the printed ordered-gap, invariance, and fully
off-diagonal perturbation hypotheses, and derive pole exclusion internally.
They therefore repair the exact ambient statement
`delta ||tan(2 Theta)|| <= 2 ||H||` without adding a quarter-angle branch or
perturbed-block spectral placement.

The two-conclusion source row is nevertheless still nonterminal.  Its directed
residual conclusion `delta ||tan(2 Theta_0)|| <= 2 ||R||` is represented by a
branch-free complex Ky-Fan corner theorem, but that theorem still accepts
explicit pole exclusion and there is no public source-facing complex+real
arbitrary-unitarily-invariant-norm wrapper from only the printed hypotheses.
The generic Ky-Fan-to-paper-norm machinery is present, so this is now a narrow
source-signature/assembly gap rather than a missing ambient perturbation
argument.

Excluding the four questions in Section 10, the maintained 45 mathematical
completion obligations therefore still consist of:

- 43 `compiled_exact` / `proved_in_build` rows;
- Proposition 4.4, `refuted_as_transcribed` / `proved_in_build`;
- one `compiled_specialization` row: `S2-tan-two-theta`, now blocked only by the
  directed residual source-facing wrapper.

Accordingly this document still does not certify 100% theorem-statement-level
source fidelity.  The new ambient declarations are incorporated as exact audit
evidence, and the remaining failure is deliberately stated at the narrower
directed-residual clause rather than the already repaired ambient clause.  The
Section 10 questions remain source-accounting entries rather than
completion obligations.

## Clause review

For every row below, the review checked the hypotheses, scalar field,
finite/arbitrary dimension, compactness, acute versus matched-defect nonacute
scope, finite versus infinite sums, existence assertions, and the stated
conclusion.  The row identifiers are grouped only for readability.

| Source part | Rows reviewed | Result |
| --- | --- | --- |
| Sections 1--2 | `S1-block-residual`, `S1-ui-norms`; `S2-sin-theta`, `S2-tan-theta`, `S2-sin-two-theta`, `S2-sharpness`, `S2-unbounded-scope` | Exact |
| Section 2 | `S2-tan-two-theta` | Ambient exact in complex and real scope; directed residual arbitrary-UI-norm source wrapper still needed |
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
declarations.  After incorporating `cab61ab7` the census deliberately retains
one nonterminal mathematical row, `S2-tan-two-theta`: the new exact ambient
complex/real declarations are registered, but a clean build does not by itself
supply the still-missing directed residual source-facing statement.

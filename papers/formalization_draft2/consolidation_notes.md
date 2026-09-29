# Journal consolidation notes

## Accepted scope (2026-09-29)

The journal paper is a Davis--Kahan paper. YWS is optional/secondary and should
appear only where it sharpens the statistical motivation, demonstrates a direct
specialization, or supplies a compact second source-audit example. Downstream
application projects and the empirical development-process study are not part of
the journal contribution.

## What to port from the workshop paper

Port improvements in mathematical and methodological precision, not the
workshop paper's empirical scope:

1. Separate kernel acceptance from semantic/source correspondence.
2. Make non-literal representation matches explicit. The main example is the
   positive source `sin Theta` operator versus the rectangular Lean map
   `(I-F0F0*)E0`; connect them through the modulus identity and unitarily
   invariant norms.
3. Distinguish source defects from formalization mistakes and from deliberate
   extensions.
4. State exactly which convention is corrected in YWS rather than referring to
   a generic “correction.”
5. Keep review/evidence mechanics reproducible but subordinate to the
   mathematical paper; detailed inventories belong in appendices.

## Updated Davis--Kahan story

The old draft was organized around a smaller, historically important
finite-interval/exterior sine-theta specialization. The maintained source-facing
endpoint has moved beyond that snapshot. The journal exposition should use
`sinTheta_unbounded_formGap_whereDefinedUIN_rclike` as the principal theorem and
explain:

- the unbounded partial-map formulation;
- trial and exact spectral decompositions;
- finite and ordered half-infinite form-gap alternatives;
- real and complex scalar support;
- where-defined unitarily invariant norm assumptions; and
- the modulus bridge from the rectangular Lean map to the source positive sine
  operator.

The result inventory is now the natural completeness claim: 29 reviewed source
targets, all build verified and semantically accepted; 28 proved at source scope
and Proposition 4.4 refuted as printed.

## Proposition 4.4

This deserves a main-text section rather than a line in an audit table. The
journal treatment should present the printed claim, the explicit `R^4`
counterexample, the norm calculation, the invalid proof step, and the Q-norm
repair. The result is a mathematical output of the formalization, not merely a
project-management finding.

## YWS role

Keep YWS shorter than Davis--Kahan. The useful points are:

- a recognizable statistical specialization of subspace perturbation bounds;
- the corrected equation (4) identity;
- the corrected rank-boundary convention in Theorem 3; and
- evidence that source correspondence must track printed conventions, not only
  theorem-shaped Lean declarations.

Do not describe seven corrected census rows as seven source defects.

## Reusable foundations

Use the current architecture. Reusable mathematical infrastructure is primarily
under `ForTauCeti/` with final `TauCeti.*` declaration names; paper-facing source
statements remain under `DavisKahan/`. Historical `ForMathlib`/migration framing
should not drive the journal narrative.

The foundations section should be capability-driven: unbounded operators and
domains, spectral/form bounds, operator ideals and unitarily invariant norms,
principal-angle/direct-rotation geometry, Sylvester equations, and the pieces of
functional calculus needed to support the source results.

## Retired draft2 material

The old draft2 resource-accounting/process narrative is retained only as
historical development material. It should not be reintroduced into the journal
manuscript. The separate `formalization_process` paper owns that research
question.

Likewise, old dependency-count snapshots are not journal evidence unless they
are deliberately refreshed and tied to a specific claim. Prefer mathematical
capability statements over module-count framing.

## Remaining editorial work

Before submission:

- verify every displayed source equation/theorem against the original paper;
- complete citation placement for mathematical antecedents and borrowed Lean
  proof ideas;
- decide how much of the full 29-row inventory belongs in print versus
  supplemental material;
- ensure the exact source-facing Lean theorem corresponding to each highlighted
  result is linked or listed in the artifact appendix;
- obtain a clean journal-style LaTeX build with bibliography in the submission
  environment; and
- perform a final source-correspondence pass independently of the fact that the
  Lean declarations compile.

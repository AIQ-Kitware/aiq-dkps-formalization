# Independent semantic audit prompt — Davis--Kahan 1970

Audit the claim that this repository has **100% formalized Davis--Kahan 1970**.
Bias toward finding a counterexample to that claim.

## Definition of 100%

The completion denominator is
`dev/davis-kahan-1970-formalization-result-inventory.json`.
It contains only results Davis--Kahan actually establish in the paper: the four
unnumbered Section 2 headline theorems plus every named theorem, proposition,
lemma, and corollary in Sections 3--8. At the current source revision there are
29 such results.

Do **not** create extra completion obligations from proof equations,
intermediate identities, definitions, examples, numerical working, sharpness
remarks outside a designated result, historical comparisons, Section 10 open
questions, or claims the paper explicitly leaves unresolved/deferred. Those
belong to source fidelity, not the formalization denominator.

A false designated result still counts: its exact printed proposition must be
formally refuted, and repository policy separately requires a best-effort
mathematical repair. Proposition 4.4 is the canonical example.

## Authoritative materials

1. `prose/distilled_literature/DavisKahan1970_part_III.tex` — distributable,
   source-order mathematical reconstruction.
2. `dev/davis-kahan-1970-source-atom-inventory.json` — fine-grained
   **source-fidelity** inventory. It is not the completion denominator.
3. `dev/davis-kahan-1970-formalization-result-inventory.json` — the 29-result
   completion denominator.
4. `dev/davis-kahan-1970-full-source-census.json` — registered Lean evidence.
5. Compiler-printed Lean theorem types / `#check` output from the certificate.

The original paper (DOI `10.1137/0707001`) remains the authority for a fresh
source-fidelity re-audit. A private modernized transcription is not required.

## Pass A — source-fidelity selection audit

Before trusting the denominator, review the paper-facing TeX and source-fidelity
inventory in paper order and ask only:

- Did we omit a theorem/proposition/lemma/corollary or one of the four Section 2
  headline theorems from the result inventory?
- Did we accidentally include something Davis--Kahan do not actually establish?
- Are Section 10 questions and explicitly deferred/unresolved claims excluded?
- Does each selected result point at source atoms covering its exact hypotheses,
  conclusions, and stated scope?
- Are all remaining source atoms explicitly classified as non-result material?
- Does every fidelity atom carry a specific boundary reason rather than an
  unexplained generic `non_result` label?
- Do `formalization_result_ids` agree exactly with the result inventory's forward
  `source_atom_ids` links?
- For each counted result, does its accepted `boundary_review` correctly partition
  the primary source block into atoms inside the printed statement and adjacent
  setup/proof/example/consequence/remark material outside it?
- Is any atom classified as proof/setup/consequence actually part of a printed
  result hypothesis, conclusion, or scope? This is the primary omission attack.

Do not reject the denominator merely because a proof equation or example lacks a
Lean theorem. That is not the project definition of 100%. Do reject it if an
excluded atom is actually part of one of the printed 29 result statements, or if
a result Davis--Kahan establish is absent from the 29-result inventory.

## Pass B — exact result-to-Lean semantic audit

For **every counted result**, compare the source statement with the registered
source-facing Lean declaration(s). Check all of the following:

- every printed hypothesis is represented and no stronger hypothesis was added;
- every printed conclusion is represented and no conclusion was weakened;
- real versus complex scope;
- finite versus infinite-dimensional scope;
- bounded versus unbounded scope where the paper states it;
- arbitrary unitary-invariant norm versus a narrower norm family;
- directed versus ambient angle/operator;
- equality/strictness, constants, signs, interval orientation, rank/dimension
  assumptions, and branch/pole conditions;
- whether a modern stronger theorem is being confused with an exact source
  wrapper.

Multiple Lean declarations may jointly cover one source result. That is fine if
their union is exactly the source statement at full scope.

For a false counted result, verify that the refutation satisfies the printed
hypotheses and actually negates the printed conclusion. Then separately inspect
the repair record and its theorem.

## Required verdict

A 100% verdict is allowed only if:

- the 29-result selection review is accepted and fresh with respect to both the
  source-fidelity inventory and the distributable TeX;
- every counted result is semantically accepted;
- every counted result has compiler-verified source-facing evidence;
- every false counted result has an exact refutation and terminal repair record;
- the hard result-level gate passes.

Report source-fidelity defects separately from formalization-result defects. A
missing proof equation in the TeX is a fidelity defect; it is not by itself a
missing Lean theorem. Conversely, a missing theorem result is a completion defect
even if every proof equation is faithfully reconstructed.

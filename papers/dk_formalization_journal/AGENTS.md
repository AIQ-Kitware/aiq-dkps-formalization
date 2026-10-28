# Formalization paper authoring instructions

This directory contains the manuscript and its generated analysis snapshots.

Before editing manuscript prose, read:

- [PAPER_CONTEXT.md](PAPER_CONTEXT.md), which keeps accepted results, mathematical
  and verification boundaries, publication decisions, and unresolved questions;
- [STYLE_GUIDE.md](STYLE_GUIDE.md), which describes the writing style and manuscript structure we want;
- [../BANNED_WORDS_AND_PHRASES.md](../BANNED_WORDS_AND_PHRASES.md), which lists prohibited vocabulary and recurring LLM writing patterns.
- [../SPECIFIC_NEGATIVE_PROMPTS.md](../SPECIFIC_NEGATIVE_PROMPTS.md), which records recurring manuscript-specific failure modes.

The YWS material previously in this article was moved to
`../yws_formalization_conference/`. Keep the Davis--Kahan paper scoped to the
1970 source and its mathematical extensions.

These rules apply to the main text, appendices, captions, and generated prose intended for the paper.

## Manuscript operating rules

- Keep the main text centered on the mathematics, formalization results, source-audit findings, foundational theory, and reported resource measurements.
- Maintain evidence and uncertainty that does not warrant publication in
  `PAPER_CONTEXT.md` and `claims_to_evidence.md`; do not insert
  editorial decisions, agent handoffs, or negative-evidence logs into the rendered paper.
- Put source-coverage bookkeeping, declaration graphs, provenance tables, exact Lean names beyond the displayed signatures, file paths, registry mechanics, and regeneration details in the appendices.
- When comparing a source theorem with Lean, state the theorem first and place its Lean signature immediately afterward. Keep shared notation above theorem-specific subsections.
- Keep the general Lean-reader guide in the appendix and refer to it before the first displayed signature.
- Keep the formalization-process description in the methods appendix. State the tools and recurring workflow without turning the manuscript into an agent handoff.
- Put references before the appendices.
- Cross-reference appendix sections explicitly whenever the main text sends a reader to supplementary evidence.
- Label incomplete resource data as retained observed telemetry, state that it is incomplete, and keep live exact, explicit backfill, pending, modeled, and extrapolated quantities separate. Do not describe the retained aggregate as a strict lower bound unless duplicate-observation risk has been ruled out.

## Citations and bibliography

- Put bibliographic metadata in `references.bib` and cite entries from the manuscript with Natbib commands.
- Use published metadata and DOI records when available.
- Cite external Lean developments when their formal work was copied, ported, adapted, generalized, or used as a substantive reference.

## Generated data

Do not hand-edit generated snapshot tables when the corresponding generator is available. Regenerate them with the existing scripts and keep raw evidence linked to exact source results and Lean declarations.


## Current publication direction (27 October 2026)

Read [FORMALIZATION_PAPER_SCOPE.md](FORMALIZATION_PAPER_SCOPE.md) before
changing the paper. This is a formalization-first manuscript. Keep the
29-result source audit, operator-theory foundations, and Proposition 4.4
correction as the primary scientific account. New optimal-transport theory
is retained in sibling `../optimal_spectral_transport/`; only a selected
matching theorem is used here to demonstrate a verified follow-on question.
Do not promote every new transport theorem into this article.

## Historical exposition and self-contained investigation (2026-10-28)

When revising the historical section, identify the primary mathematical
source and cite existing surveys (Paige--Wei, Simon on Kato,
Bottcher--Spitkovsky) for their actual scope. Explain what each
mathematical development contributed to Davis--Kahan's theorem and
which formalized dependency represents it. Do not reduce the section
to a name-and-year list, and do not displace the formalization as the
article's main contribution.

Do not conclude implementation or editorial work with unspecified
'get expert review' advice. Make remaining tasks concrete and
actionable within this repository: theorem/source correspondence,
proof exposition, literature comparison, and reproducible examples.
Follow `../SPECIFIC_NEGATIVE_PROMPTS.md`.

## Historical story and figure constraints (2026-10-28)

- The article is a formalization paper. Present the source lineage as a
  connected account of the mathematical problems solved, not a catalog of
  people and dates. Explain how principal angles, eigenvalue approximation,
  projection transport, spectral calculus, Sylvester separation, and
  symmetric ideals combine in the 1970 theorems.
- Retain precise original-source attributions, alongside surveys that
  explain the historical connections. Distinguish contributions to
  mathematics from the provenance of formal Lean implementations.
- The former illustrations have been removed deliberately. Do not
  restore the rank-one sine-theta or Proposition 4.4 displacement figures
  without an explicit new author request; retain their analytical
  calculations in prose.
- Build the bibliography from the current source and reject unresolved
  citations. Do not recommend unspecified external expert review as an
  answer to source-comparison or attribution work.

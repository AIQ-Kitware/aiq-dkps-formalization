# Formalization paper authoring instructions

This directory contains the manuscript and its generated analysis snapshots.

Before editing manuscript prose, read both:

- [STYLE_GUIDE.md](STYLE_GUIDE.md), which describes the writing style and manuscript structure we want;
- [BANNED_WORDS_AND_PHRASES.md](BANNED_WORDS_AND_PHRASES.md), which lists prohibited vocabulary and recurring LLM writing patterns.

Both apply to the main text, appendices, captions, and generated prose intended for the paper.

## Manuscript operating rules

- Keep the main text centered on the mathematics, formalization results, source-audit findings, foundational theory, and reported resource measurements.
- Put source-coverage bookkeeping, declaration graphs, provenance tables, exact Lean names beyond the displayed signatures, file paths, registry mechanics, and regeneration details in the appendices.
- When comparing a source theorem with Lean, state the theorem first and place its Lean signature immediately afterward. Keep shared notation above theorem-specific subsections.
- Keep the general Lean-reader guide in the appendix and refer to it before the first displayed signature.
- Keep the formalization-process description in the methods appendix. State the tools and recurring workflow without turning the manuscript into an agent handoff.
- Put references before the appendices.
- Cross-reference appendix sections explicitly whenever the main text sends a reader to supplementary evidence.
- Label incomplete observed resource telemetry as a lower bound in table headers and captions, and keep observed values separate from modeled or extrapolated values.

## Citations and bibliography

- Put bibliographic metadata in `references.bib` and cite entries from the manuscript with Natbib commands.
- Use published metadata and DOI records when available.
- Cite external Lean developments when their formal work was copied, ported, adapted, generalized, or used as a substantive reference.

## Generated data

Do not hand-edit generated snapshot tables when the corresponding generator is available. Regenerate them with the existing scripts and keep raw evidence linked to exact source results and Lean declarations.

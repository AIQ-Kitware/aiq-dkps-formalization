# Formalization paper authoring instructions

This directory contains the manuscript and its generated analysis snapshots.

Before editing prose in this directory, read [BANNED_WORDS_AND_PHRASES.md](BANNED_WORDS_AND_PHRASES.md). Its style constraints apply to the main text, appendices, captions, and generated prose intended for the paper.

## Manuscript structure

- Keep mathematical exposition in the main text and move audit bookkeeping, exact Lean declaration names, file paths, registry mechanics, and regeneration details to the appendix.
- The main text may reproduce the two designated Lean theorem surfaces. Avoid additional code-facing names in surrounding prose unless a mathematical point requires them.
- Treat the prerequisite-theory and formalization-provenance sections as the authoritative summaries of what was formalized. Avoid duplicating the same accounting elsewhere.
- Source-coverage registries are evidence infrastructure. Present their construction and exact counts in the appendix.
- Write for the mathematical reader. Repository workflow history and agent-facing reminders belong in project documentation rather than manuscript prose.
- Preserve the distinction between mathematical provenance and formalization provenance. Explicit formal-source citations receive credit; uncited project-local formalization receives project credit under the documented policy.

## Citations and bibliography

- Put bibliographic metadata in `references.bib` and cite entries from the manuscript with Natbib commands.
- Do not add a hand-written `thebibliography` block to `paper.tex`.
- Prefer published metadata and DOI records when a paper has appeared in a journal or proceedings; retain arXiv metadata when it is the available publication record.
- Repository and web references should identify the source URL and, when the manuscript depends on a pinned state, the audited revision or access date.

## Generated data

Do not hand-edit generated snapshot tables when the corresponding generator is available. Regenerate them with the existing scripts and keep raw evidence linked to exact source results and Lean declarations.

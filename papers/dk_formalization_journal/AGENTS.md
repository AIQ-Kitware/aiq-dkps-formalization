# Formalization paper authoring instructions

This is the Davis--Kahan formalization manuscript. User instructions determine
whether the current task is review, guidance maintenance, or manuscript editing.

## Read before writing

- [../STYLE_GUIDE.md](../STYLE_GUIDE.md): shared affirmative writing guidance.
- [STYLE_GUIDE.md](STYLE_GUIDE.md): this paper's audience, exposition, notation,
  and contribution framing.
- [../BANNED_WORDS_AND_PHRASES.md](../BANNED_WORDS_AND_PHRASES.md) and
  [../SPECIFIC_NEGATIVE_PROMPTS.md](../SPECIFIC_NEGATIVE_PROMPTS.md): rhetorical
  habits and recurring editorial mistakes.
- [AUTHORING_NOTES.md](AUTHORING_NOTES.md): accepted and rejected review
  suggestions, pending manuscript changes, and an index of supporting evidence.
- [FORMALIZATION_PAPER_SCOPE.md](FORMALIZATION_PAPER_SCOPE.md): scientific scope.
- [PAPER_CONTEXT.md](PAPER_CONTEXT.md): mathematical evidence and historical
  checkpoints; its older manuscript plans are historical, as marked there.

These instructions apply to the main text, captions, abstract, and appendices.
Shared style rules are applied according to the function of the passage: the
abstract may be compressed, while the body defines the objects it uses.

## Review and correction rounds

- Read all relevant `\jonsays`, `\agentsays`, and `\jonrsp` comments before
  proposing revisions. The author's responses can reject or qualify an earlier
  agent suggestion; do not treat every agent comment as an accepted edit.
- Use the requested macros during review-only work. Keep review comments and
  proposed changes separate from revised scientific prose.
- During guidance calibration, record future requests without applying them
  prematurely to the manuscript. Preserve notes until the user requests their
  removal, and retain macro definitions for the next round when requested.
- Separate evergreen preferences from decisions about particular passages.
  Update shared guidance only for reusable principles; keep paper-specific
  decisions and unresolved questions in `AUTHORING_NOTES.md`.
- Answer direct questions in chat when requested. A request to define a term in
  the paper calls for a definition in the correction pass, not just a chat reply.

## Scientific scope and attribution

This is a formalization-first paper about the 1970 Davis--Kahan results, their
operator-theory foundations, the Proposition 4.4 correction, and a selected
follow-on theorem. The source-result denominator remains 29. Changing the
rendered table or removing a review appendix does not change that denominator,
the source inventories, or the repository's semantic and compiler obligations.

The original complex-phase mechanism and earlier Q-norm results retain their
attribution. Compare them precisely with the real short-angle assertion being
refuted. Use the paper-directory evidence index to support direct statements
about our foundations, reuse of Mathlib and Spectra, and later Tau Ceti work.
Keep pinned revisions, PR bookkeeping, and proof-development history in author
files or non-rendered LaTeX comments. Include scholarly mathematical and formal
attribution in the rendered article.

The broader transport work is preserved under
[../optimal_spectral_transport/](../optimal_spectral_transport/). Do not expand
this article to cover every such theorem. Explain the included result within
this article; keep publication-packaging choices out of its scientific prose.
YWS submission material lives in
[../yws_formalization_conference/](../yws_formalization_conference/).

## Manuscript conventions

- State a mathematical theorem before its Lean signature; explain its specific
  predicates and cite the general Lean reader guide once before the first one.
- Define technical objects in the body with enough intuition for their use.
  Keep notation consistent and align optional colors with the Manim palette.
- Describe historical mathematical relationships explicitly and cite primary
  sources together with the Paige--Wei, Simon, and Bottcher--Spitkovsky surveys
  where they support the account. Give dates when they clarify chronology.
- Store bibliographic metadata in `references.bib` and use Natbib. Reject
  unresolved citations. Put references before appendices and use explicit
  section references when pointing to supplementary material.
- Keep a compact source-result table with an artifact path from IDs to Lean.
  Appendices serve a reader's task; author evidence need not be rendered there.
- Use the current `paper.tex` inclusion graph as the ground truth. Preserve
  existing figures unless the requested manuscript revision calls for their
  addition or removal.
- If resource data is reported, label incomplete observed telemetry and keep
  live observations, backfills, modeled quantities, and extrapolations separate.
  Do not hand-edit generated snapshots when their generator is available.
- Do not conclude editorial or research tasks with unspecified requests for
  expert review. Name a concrete source comparison, calculation, or proof task.

## Validation

For changed TeX, run `make -C papers/dk_formalization_journal paper` from the
repository root and inspect the log for errors and unresolved references. The
PDF is `build/paper.pdf`; the project configuration selects LuaLaTeX for emoji
notes and retains the previous PDF on compilation failure. Build instructions
and editor troubleshooting are in [README.md](README.md).

Documentation-only guidance changes require link and consistency review; they
do not require a Lean build or a manuscript rebuild.

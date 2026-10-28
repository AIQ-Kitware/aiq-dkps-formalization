# Author decisions and evidence

These notes support editing; they are not rendered manuscript text. They record
the 28 October 2026 review in `\jonrsp` and distinguish lasting preferences
from the pending correction pass. Current user instructions determine the stage.

## Calibration from the review

- The abstract may name established objects, summarize attribution, and make
  broad connections. Define and explain them in the body. The author rejected
  the agent's demand for more detail throughout the abstract.
- Give definitions and brief reminders where needed. “Define intertwining” is
  a request for exposition, not necessarily a direct question requiring a chat
  tutorial. Singular values need at most a quick reminder; operator ideals need
  a definition. Give an interval example rather than merely replacing
  “half-infinite” with “half-line.”
- Preserve the current follow-on heading unless the author revisits it. A
  foundation-section heading may explicitly identify formalized operator theory.
- Name what we formalized and what we reused directly. Keep detailed evidence
  accessible to authors so the scientific prose can be decisive and accurate.
- Distinguish the known complex mechanism from the apparently unreported
  identification of the error in the printed real Proposition 4.4. The intended
  novelty statement is qualified by “to the best of our knowledge”; it is not a
  claim that all ingredients or the Q-norm conclusion are new.
- The current AI-role paragraph proposed in chat was rejected. The author is
  considering discussion-section placement. Do not infer an accepted replacement
  from earlier agent suggestions. Name systems “ChatGPT and Claude” if needed;
  no expanded tool taxonomy or task-allocation narrative is requested.

## Manuscript correction pass (28 October 2026)

The accepted edits are now applied. The original review is preserved in Git;
this summary keeps the decisions available for the next round.

- Kept the abstract's accepted level of compression; revised the introduction,
  definitions, historical transitions, mathematical relationships, and headings.
  The follow-on heading is preserved. Trace-norm terminology is consistent.
- Stated the exact source-result selection criterion and kept all 29 result IDs.
  Removed the disposition column and the source-correspondence review appendix.
  The underlying inventories and result-to-Lean mapping are unchanged.
- Introduced the explicit Proposition 4.4 counterexample with the qualified
  priority claim and its mathematical predecessors. The figure caption also
  identifies it as the counterexample. Added the Frobenius Q-norm example.
- Removed the unfulfilled quantitative-bound promise, with source comments
  pointing to the additional formalized results. Removed rendered references to
  separate manuscripts and pinned dependencies; kept mathematical and formal
  attribution, with exact provenance evidence in source comments and this index.
- Added a self-contained proof outline for the matching result, including the
  real block reduction for exponents above one and compact continuation to the
  trace-norm endpoint. The theorem statement and its global scope are preserved.
- Enabled author--year citations, linked the MSC codes, and added publication
  years to the historical table. The final venue's numeric/IEEE formatting and
  any later timeline remain future choices.
- Added independent anonymization and symbol-color conditionals. The Manim role
  palette is unchanged. The perturbed operator is consistently written as
  `\widehat A`; the exact coordinate space is written as `F_ex` to distinguish
  it from the perturbation `H`. The displayed Lean declaration is unchanged and
  its caption gives the notation correspondence.
- Removed all review-note invocations from the included manuscript files and
  retained the `\jonsays`, `\agentsays`, and `\jonrsp` definitions for the
  next round.

The AI-role paragraph proposed in chat remains rejected. The article keeps a
brief disclosure naming ChatGPT and Claude. A broader discussion paragraph has
not been substituted; its wording and placement remain open for author review.

## Local evidence index

Paths below are relative to this paper directory. Prefer these existing records
and exact source declarations to a competing provenance inventory.

| Question | Evidence to consult |
| --- | --- |
| Which 29 source results were selected, and which Lean declarations represent each ID? | [Result inventory](../../dev/davis-kahan-1970-formalization-result-inventory.json), particularly `selection_definition` and each result's `id`, `source_anchor`, and `lean_declarations`. |
| How are source passages, result IDs, and declarations connected? | [Statement map](../../dev/davis-kahan-1970-statement-map.json) and [full source census](../../dev/davis-kahan-1970-full-source-census.json). The result inventory already maps the table IDs directly to declarations. |
| What is the source's mathematical scope? | [Distributable source specification](../../prose/distilled_literature/DavisKahan1970_part_III.tex) and [claims to evidence](claims_to_evidence.md). |
| What supports the correction and its literature comparison? | [Proposition 4.4 literature map](PROPOSITION_4_4_LITERATURE_MAP.md), [literature audit](submission/LITERATURE_AUDIT.md), and [claims to evidence](claims_to_evidence.md). Check each claim at the source's real/complex, norm, and angle scope. |
| Which formal results were adapted into Tau Ceti, independently re-proved there, or built on earlier donors? | [Contribution and lineage census](../../dev/tauceti/dkps-upstream-contribution-census.md) and [upstream consumption review](../../dev/tauceti/upstream-consumption-review-2026-10-22.md). These are dated evidence, not proof of current remote status. |
| Which parts have Spectra ancestry? | [Spectra provenance map](../../dev/tauceti/spectra-provenance-map.md), [preserved upstream attribution](../../retired/Spectra.UPSTREAM.md), and the Lean provenance headers. |
| Which roadmap topics correspond to donor work? | [Donor topic map](../../dev/tauceti/roadmap-topic-map.md). Topic overlap alone does not establish proof descent. |
| What notation and colors does this article use? | [Symbol macros](math_symbol_colors.tex), [notation appendix source](appendix_notation.tex), and the [Manim glossary](../../visualizations/dkvis/slides_glossary.py). |

## Optional campaign checkout

The author also identified `/home/joncrall/code/tauceti-dkps-campaign`. On this
machine the inspected checkout is at `bd68dba` (26 October 2026). It is an
optional evidence source, never a manuscript or Lean build dependency. Its
README indexes:

- `proof/campaign/STATUS.md`: last-known campaign observations and their dates;
- `docs/OPERATOR_THEORY_LEDGER.md`: roadmap items and evidence relationships;
- `docs/PROOF_LINEAGE.md` and `proof/proof_lineage.json`: a pinned proof-lineage
  case study with its stated limits;
- `docs/UPSTREAM_REVIEW_LESSONS.md`: lessons from upstream review and repair.

This checkout is read-only for this task. No refresh, remote action, or new
integration claim was made. Before claiming current upstream acceptance,
inspect the accepted revision and distinguish submission, integration, direct
adaptation, independent work, and transitive use. Add findings to the maintained
census when appropriate; this index supplies navigation rather than a new
campaign ledger.

# Paper authoring rules

The files in this directory govern manuscript writing throughout `papers/`.
Before editing paper prose, captions, headings, abstracts, or appendices, read:

- [BANNED_WORDS_AND_PHRASES.md](BANNED_WORDS_AND_PHRASES.md)
- [SPECIFIC_NEGATIVE_PROMPTS.md](SPECIFIC_NEGATIVE_PROMPTS.md)
- [STYLE_GUIDE.md](STYLE_GUIDE.md), for affirmative writing guidance, including
  the different roles of abstracts, exposition, discussion, and author notes.

Subdirectories may add manuscript-specific instructions and style guides. Those
rules supplement these shared constraints.

Read the applicable manuscript's `AGENTS.md` and style guide as well. Apply
review feedback at its stated scope: a request for a definition in the body
does not require expanding the abstract. Keep reusable preferences in the style
documents and passage-specific decisions in that manuscript's author notes.
Source and provenance evidence belongs in linked author files or non-rendered
LaTeX comments unless it serves a concrete purpose for the paper's reader.

Standalone paper sources are grouped by purpose rather than kept at the root:

- `old/formalization_comparisons/` contains literature/formalization comparison
  documents;
- `old/davis_kahan_prop_4_4/` contains the Proposition 4.4 counterexample note and
  its historical-search supplement;
- manuscript projects such as `dk_formalization_workshop/` and
  `dk_formalization_journal/` remain self-contained directories.

# Transcript-first TTS drafts

These files are an **alternative, additive drafting branch**, following `../outline.md` rather than the existing `visualizations/lectures` Manim scene plan. They are not production video scripts or a second mathematical authority. The journal manuscript and formal proof sources remain the sources of mathematical scope; mathematical dependency determines lecture progression.

## Draft set

The collection currently contains 150 numbered transcript drafts,
`000000` through `149000`, following the topical sequence in `../outline.md`.
IDs are spaced by 1,000 to permit insertions. This folder is a transcript-first
teaching branch; its narration is not a replacement for the journal sources or
formal theorem statements.

**Editorial state (2026-11-08 revision):** All 150 drafts were screened for
standalone narration. The spoken text has been revised where needed, including
reconstruction of reused examples and the missing extraction markers for
`000000`. See [`standalone-revision-report-2026-11-08.md`](standalone-revision-report-2026-11-08.md),
the per-lecture disposition, and the candidate disposition ledger for the
changes and remaining verification work. The earlier
[`standalone-review-2026-11-08.md`](standalone-review-2026-11-08.md) is
retained as the historical pre-revision audit, not as the current task list.
Editorial validation does not establish Lean compilation or synthesized-audio
quality.

## Source format

In every substantial mathematical lecture, use exactly one `<!-- BEGIN SPOKEN LECTURE -->` / `<!-- END SPOKEN LECTURE -->` pair. The material between them is the **only text for speech synthesis**. Headings mark narrative transitions; no raw Lean, LaTeX, or math-mode notation should be spoken by TTS.

After the end marker, include a **display-only companion** with reusable mathematical statements, actual Lean source correspondence, source locations, and provenance notes where relevant. Do not assume that a source excerpt compiles by itself: excerpts may depend on surrounding namespaces and typeclass hypotheses. Never invent Lean identifiers to fill a gap. Source-file provenance records DKPS origins even when the accepted theorem has moved to TauCeti; current location and origin are separate facts.

A purely orienting introduction is exempt from the Lean appendix requirement. Mathematical lessons are not.

Extract speech text with:

```bash
python3 visualizations/draft-stages/tts-lectures/extract_narration.py \
  visualizations/draft-stages/tts-lectures/001000-linear-maps-independent-of-coordinates.md \
  > /tmp/001000-narration.txt
```

Validate all newly drafted lessons with:

```bash
python3 visualizations/draft-stages/tts-lectures/extract_narration.py --check \
  visualizations/draft-stages/tts-lectures/00[123]000-*.md
```

The checker validates formatting and the spoken-only boundary. It does not compile Lean, verify theorems, or assess how the narration sounds when synthesized. Mathematical editing and an actual TTS listening pass are required before promotion.

## Independent-listening requirements

**Every narrated lesson must stand by itself.** Do not refer to preceding,
future, or numbered lectures in spoken material. A recap is allowed, but state
the relevant theorem or definition directly. For a reused numerical example,
provide the actual matrix, vector, parameter, and assumptions in the present
recording. Keep introductions about the problem at hand and endings about what
this recording establishes, without teasers for the next installment.

Talk about the mathematics and its historical attribution, not about the prompt,
source-code repository, proof assistant, or how the course was drafted.
Mathematical claims must still retain their exact hypotheses and proved scope;
implementation and lineage detail belongs below `<!-- END SPOKEN LECTURE -->`,
where the display-only Lean companion already lives. The general lecture rules
in [`../../LECTURE_STYLE_RULES.md`](../../LECTURE_STYLE_RULES.md) give more
examples, with this transcript-first audience taken to know basic linear
algebra and calculus but no prior functional analysis.

Judge independence from the **extracted narration alone**. A reader may use the
preamble's prerequisites and next-lesson links for navigation, but a listener
must not need them. The course introduction (`000000`) has an extractable
spoken region and remains exempt from needing a Lean appendix. The review
records the historical pre-revision marker defect and its disposition.

## Transcript review standard

Check independently that:

1. The lesson works without animation and builds each new concept from previously taught mathematics.
2. Its theorems include a clear setting, their required hypotheses, and a reconstructible argument.
3. Its examples distinguish a particular computation from a general statement, and include a useful boundary or failure case when applicable.
4. Every symbol to Lean connection maps to a verified declaration or explicitly identified excerpt. Track TauCeti's current implementation separately from DKPS's donor/provenance history.
5. The spoken region contains no raw code or notation that makes synthetic speech hard to follow.
6. The listener can answer a new question using the ideas, not just repeat the conclusion.

These files remain editorial lecture drafts. Past source-to-Lean correspondence checks
were textual and did not constitute proof compilation; the independent-listening
review has not rechecked those mathematical declarations. Production promotion
requires separate mathematical and actual synthesized-audio review.

# Transcript-first TTS drafts

These 150 transcript-first drafts follow `../outline.md` and are separate from the `visualizations/lectures` Manim scene plan. The journal manuscript and formal proof sources provide the mathematical scope.

## Draft set

The collection currently contains 150 numbered transcript drafts,
`000000` through `149000`, following the topical sequence in `../outline.md`.
IDs are spaced by 1,000 to permit insertions. The sequence follows mathematical dependencies.

**Editorial state (2026-11-08 revision):** All 150 drafts were screened for
standalone narration. The spoken text has been revised where needed, including
reconstruction of reused examples and the missing extraction markers for
`000000`. See [`standalone-revision-report-2026-11-08.md`](standalone-revision-report-2026-11-08.md),
the per-lecture disposition, and the candidate disposition ledger for the
changes and remaining verification work. The earlier
[`standalone-review-2026-11-08.md`](standalone-review-2026-11-08.md) is
the pre-revision audit. The extraction check passed; mathematical source
comparison and synthesized-audio review remain on the follow-up list.

**Pedagogical structure audit (2026-11-08):** The subsequent
[structural revision report](pedagogical-structure-revision-report-2026-11-08.md)
and [150-lecture disposition ledger](pedagogical-structure-by-lecture-2026-11-08.tsv)
record a second pass over openings, section progression, local context,
worked examples, proof flow, and conclusions. This pass made targeted
narration edits in 80 recordings; 70 were screened without modification.
The report lists structural repairs and follow-up mathematical checks.
The prior standalone audit remains historical.
No companion presentation or visualization work belongs to this phase.

**Human-lecture voice audit (2026-11-08):**
[`llmism-revision-report-2026-11-08.md`](llmism-revision-report-2026-11-08.md)
and [`llmism-by-lecture-2026-11-08.tsv`](llmism-by-lecture-2026-11-08.tsv)
record a narrated-text pass focused on authoring leakage, non-mathematical
hedging, recurrent formulaic transitions, and self-referential validation
language. Mathematical qualifications and historical theorem corrections were
retained; source and compilation reporting belongs in the companion/report.
The current phase covers lecture narration and structure.

## Source format

In every substantial mathematical lecture, use exactly one `<!-- BEGIN SPOKEN LECTURE -->` / `<!-- END SPOKEN LECTURE -->` pair. The material between them is the **only text for speech synthesis**. Headings mark narrative transitions; no raw Lean, LaTeX, or math-mode notation should be spoken by TTS.

After the end marker, include a **display-only companion** with reusable mathematical statements, actual Lean source correspondence, source locations, and provenance notes where relevant. Include the surrounding namespace and typeclass assumptions when quoting Lean declarations. Use actual Lean identifiers. Source-file provenance records DKPS origins even when the accepted theorem has moved to TauCeti; current location and origin are separate facts.

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

The checker validates formatting and spoken-region boundaries. Mathematical source review and a synthesized-audio listening pass are separate acceptance steps.

## Non-spoken citations and further learning (8 November 2026)

`metadata/` has a JSON sidecar for each of the 150 transcripts and a shared
bibliographic catalog. Historical attributions and claims about the scope or
wording of a published paper are anchored to exact excerpts of the extracted
spoken text, for later primary-source comparison. External videos, notes,
texts, and original papers are listed separately under `related_resources`.

**Citation metadata is never interpolated into the spoken Markdown.** The
existing `extract_narration.py` remains the sole TTS input producer. To check
all anchors and links, run `reference_metadata.py --check`; to build a single
future-server record with bibliography and offsets, use `--json 053000`.
See [sidecar documentation](metadata/README.md) and
[citation audit report](reference-metadata-report-2026-11-08.md).
The historical claim ledger records all 49 primary-passage comparisons as pending.

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

Publication follow-up: mathematical correspondence review, Lean compilation,
and synthesized-audio listening evaluation.

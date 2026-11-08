# Direct reporting in lecture audits

**Date:** 2026-11-08  
**Scope:** lecture style rules, lecture README, citation sidecar guide, four existing audit reports, and selected reference descriptions.

## Changes

The editorial rule now applies to reports and recommendations as well as narrated lectures. Reports state completed work, evidence, and the next concrete action. Historical source-audit status remains in the claim ledger and sidecars.

This revision updates nine existing repository files:

- `visualizations/LECTURE_STYLE_RULES.md`: adds the direct-reporting standard and an editing test for defensive boilerplate.
- `README.md` and `metadata/README.md`: simplify review-status and TTS-separation explanations.
- `standalone-revision-report-2026-11-08.md`, `pedagogical-structure-revision-report-2026-11-08.md`, and `llmism-revision-report-2026-11-08.md`: replace repeated non-certification paragraphs with recorded checks and specific follow-up work.
- `reference-metadata-report-2026-11-08.md`: replaces source-availability disclaimers with the 49-claim audit status and passage-comparison queue.
- `metadata/sources.json` and `metadata/134000.json`: remove generic cautionary language from bibliographic descriptions and a reading recommendation.

## Representative edits

| Before | After |
| --- | --- |
| “A source record is not itself a verification of an anchored historical claim.” | “The 49 claims are queued for primary-passage comparison.” |
| “A structural screening is not a complete theorem-by-theorem proof check.” | “The report lists structural repairs and follow-up mathematical checks.” |
| “No Lean build was run, so there is no new proof-compilation claim.” | “Next checks: compile the Lean project.” |
| “This audit does not certify that no subjective stylistic imperfections remain.” | “The TSV records remaining lexical candidates for later review.” |

Mathematically relevant qualifications in the spoken lectures remain in place. No numbered lecture transcript or display-only appendix was modified in this overlay.

## Checks

- Citation metadata: **150 sidecars**, **49 claim anchors**, **300 related-resource links** validated.
- Reference metadata regression suite: **5/5 passed**.
- Narration extractor: **150/150 inputs passed**.
- ZIP content: edited documentation and reference descriptions only.

## Subsequent work

Compare the 49 historical anchors with the primary text, starting with Proposition 4.4, Theorems 6.1–6.3 and 8.1–8.2, then record page locators and dispositions in the sidecars.

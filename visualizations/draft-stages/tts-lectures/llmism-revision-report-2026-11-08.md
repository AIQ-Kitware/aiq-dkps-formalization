# DKPS lecture narration: audit for assistant-style writing

**Date:** 8 November 2026  
**Scope:** all 150 numbered TTS recordings, `000000–149000`  
**Baseline:** apply `dkps-tts-standalone-overlay-2026-11-08.zip` and then `dkps-pedagogical-structure-overlay-2026-11-08.zip` to the uploaded source snapshot. This overlay is **incremental to that second overlay**.

## Findings and disposition

All 150 spoken regions were screened for authoring/provenance leakage, process or compilation-status commentary, defensive qualifications, repeated episode-openings, and self-referential course or proof commentary. Flagged passages were inspected in context before editing. The 86 recordings listed as `revised` in the accompanying [150-row ledger](llmism-by-lecture-2026-11-08.tsv) have targeted narration changes; the remaining 64 were screened without changes. The separate mathematical-fidelity audit remains on the work plan.

The remaining process leakage consisted of phrases such as “the source formalizes” and “the formalized rectangular theorem,” plus references to an “implementation,” “source-shaped wrapper,” and what an author or speaker could “claim.” We removed those editorial frames from the spoken passages and retained mathematical assumptions and conclusions. Compilation and editorial review status are recorded in the companion documentation.

We also found a frequent template-opening habit: 45 occurrences of “Today we will” in 150 recordings before this pass. It now occurs in six, where the surrounding setup is conversational and appropriate. One “Yesterday…” callback and a reference to “the previous theorem” were replaced with the relevant mathematics. Repeated "we have not proved"-style narration was revised when it described the speaker's progress instead of a genuine missing mathematical premise.

## What changed

- **Proof-assistant and source-wrapper language:** Recast `006000`, `069000`, `115000`, `125000`, `128000`, `129000`, `131000`, and `146000` as mathematical explanations. Specific historical assumptions remain when they affect the theorem.
- **Defensive validation-style language:** Removed unnecessary “we cannot claim,” “we have not asserted,” “not paperwork,” and similar rhetorical self-checks; retained direct positive statements of what each norm or spectral condition gives.
- **Repetitive scaffolding:** Replaced many “Today we will...” and "the point is" openings with a theorem statement, example, or concrete mathematical question. Preserved natural instructional speech and exercises in the practicum.
- **Standalone speech:** Fixed a “Yesterday...” reference (`038000`), “previous theorem” (`126000`), and several forward-looking recaps.
- **Style and workflow:** Added an authoring policy that distinguishes mathematical qualifications from authoring-process caveats, and updated the TTS README to point to this disposition record.

## Before / after examples

| Lecture | Before | After / reason |
| --- | --- | --- |
| `006000` | “a fully detailed treatment ... belongs in our later foundational proof work” | Explains directly that the one-direction Hahn–Banach extension requires an additional maximal-extension argument for the infinite-dimensional theorem; preserves an actual missing proof step. |
| `038000` | “Yesterday we constructed ... Today we will ask ...” | Defines polar decomposition locally and distinguishes its determined partial isometry from possible choices on unused directions. |
| `069000` | “the source formalizes the exact singular values...” | States that the exact singular values and spectral gap give the strict operator-norm counterexample. |
| `125000` | “If an implementation instead stores the smallest eigenvalue ...” | States the length/eigenvalue square-root relationship in mathematical terms, preserving the required factor. |
| `126000` | “both ... hypotheses changed relative to the previous theorem” | Explains directly that Theorem 6.2 uses pairwise separation and a Hilbert–Schmidt norm, instead of relying on another episode. |
| `131000` | “The formalized source result ... source-shaped wrapper...” | States the historical compactness and crossed-defect conditions alongside the more general projection argument. |
| `149000` | “an honest theorem first establishes ideal membership...” | States the ideal-membership requirement plainly, keeping the norm-class restriction. |

## Phrase-screen counts (spoken text only)

These counts measure **candidate phrases**, not the number of errors. Remaining candidates are not automatically defects.

| Candidate pattern | Baseline | Revised |
| --- | ---: | ---: |
| `formalization_or_implementation` | 5 | 0 |
| `episode_or_previous_theorem` | 2 | 0 |
| `explicit_lecture_meta` | 5 | 0 |
| `template_today_we_will` | 45 | 6 |
| `we_should` | 34 | 27 |
| `we_have_not` | 24 | 7 |
| `not_merely` | 35 | 32 |
| `rhetorical_hedge` | 7 | 1 |

The remaining “we should,” “we have not,” and “not merely” matches mostly occur in mathematically meaningful distinctions or local proof reasoning. They are retained unless a full contextual rewrite is justified. The audit should not be used as a rule to delete all cautionary phrases.

## Verification

- Every one of the 150 files has exactly one spoken start marker and one spoken end marker.
- All **150/150** pass `extract_narration.py --check` against the revised corpus.
- Every byte of every display-only mathematical/Lean appendix remains identical to the preceding pedagogical-structure baseline.
- All pre-marker metadata and the course file numbering remain unchanged; only spoken regions, style guidance, README, and these audit documents changed.
- Targeted scans of explicit compilation/proof-assistant/implementation commentary and named episode callbacks returned no matches in spoken text.
- Follow-up: mathematical-fidelity review and synthesized-audio listening. Presentations remain deferred.

## Remaining review

The TSV records all 150 dispositions and remaining lexical candidates. Subsequent narrative reviews should examine those passages in context and prioritize actual listener comprehension.

## Applying this ZIP

This ZIP is an **incremental overlay** for the current DKPS source tree **after** the standalone-listening and pedagogical-structure revisions, in that order. It contains 86 revised numbered lecture files, the style rules, the TTS README, this report, and the per-lecture ledger. Extract at the root of the DKPS repository after checking `git status` to avoid overwriting concurrent edits. The `git add` instructions in the delivery stage the exact ZIP members.

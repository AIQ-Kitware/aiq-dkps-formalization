# Feedback to Qwen: DKPS lecture narration audit

8 November 2026

## Purpose

Use this feedback when reviewing the 150 independently listenable DKPS mathematical lectures. Your audit identified real issues, especially ambiguous spoken formulas and raw notation. It also recommended changes that would damage mathematical meaning or discard correct names. The next review should distinguish **demonstrable defects** from **possible TTS risks** and **stylistic preferences**.

Review the **extracted spoken narration** in context. The display-only mathematical/Lean appendix supplies exact notation for comparison. The narration must preserve the theorem's hypotheses, mathematical distinctions, and attribution. Do not turn the transcript into an account of compilation, validation, the repository, or lecture-production decisions.

The full 67-row record is in `qwen-feedback-disposition-2026-11-08.tsv`; the companion review is `qwen-feedback-review-2026-11-08.md`. The original audit remains in `qwen-audit-results.md` and `qwen-audit-candidates-2026-11-08.tsv`.

## Review outcome

| Disposition | Rows |
| --- | ---: |
| Accepted narration corrections | 28 |
| Already resolved when reviewed | 20 |
| Extractor correction | 1 |
| Partially accepted | 1 |
| Rejected false positives | 5 |
| Retained correct wording | 4 |
| Pronunciation checks requiring actual audio | 8 |
| **Total** | **67** |

A high-confidence label in the original audit did not guarantee a valid correction. Assess each suggestion against the underlying mathematics before assigning priority.

## Specific errors to avoid

### 1. Do not normalize mathematically different notation

**Audit entries:** `072000`, `073000`, `088000` (three rejected rows; `073000` also appears in a second candidate referring to the same distinction).

**Your suggestion:** Standardize `ell two` and `L two` throughout the course.

**Problem:** These names denote different spaces:

- `ell two` / $\ell^2$: square-summable sequences.
- `L two` / $L^2$: equivalence classes of square-integrable functions on a specified measure space.

The lectures deliberately use both, and `072000` compares the sequence and function models. A global substitution would create false mathematical statements.

**Future behavior:** Before calling a notation variation inconsistent, recover the objects being denoted. Preserve distinctions between domain/codomain, source/target space, norm class, operator topology, angle branch, field, and spectrum. Suggest normalization only for different spellings of the **same** concept.

### 2. Do not shorten proper mathematical names as a speculative pronunciation fix

**Audit entry:** `048000` (`Sz.-Nagy`).

**Your suggestion:** Replace `Sz.-Nagy–Kato` by `Nagy–Kato` to avoid a pause at the period.

**Problem:** `Sz.-Nagy` is the conventional abbreviated surname of Béla Szőkefalvi-Nagy. The proposed change loses the established name without demonstrating that the TTS voice fails to say it.

**Future behavior:** Preserve named theorems, researchers, and attributions. When the concern is audio rendering, tag an exact test sentence and request a pronunciation check with the selected voice. Keep pronunciation aliases separate from mathematical naming and display text.

### 3. Keep correct attribution even when accented spelling looks inconvenient

**Audit entry:** `099000` (`Hölder`).

**Your suggestion:** Substitute an unnamed Schatten product estimate because the diacritic might be mispronounced.

**Problem:** Hölder's name is appropriate for the product inequality. A hypothetical voice failure is not a reason to remove it.

**Future behavior:** Classify this as a pronunciation candidate, not an editorial defect. Proposed audio aliases should be justified by an actual rendering error.

### 4. Equivalent mathematical readings are not inherently inconsistent

**Audit entry:** `084000` (postfix `star` versus `adjoint`).

**Your suggestion:** Make a course-wide replacement of `X star` by `X adjoint`.

**Problem:** Both are standard spoken readings of $X^*$; in context they are intelligible. The proposed sweep would generate extensive churn without a specific defect.

**Future behavior:** Flag a passage only when the local reading introduces a real ambiguity, an incorrect object, or a demonstrated listener problem. A preference for one synonym is not sufficient. The same principle applies to `p-th` / `pth` and accepted theorem labels such as `sine-two-theta`.

### 5. Do not classify ordinary typography as mathematical code

**Audit entry:** `028000` (curly quotation marks; a related instance was noted in `032000`).

**Your suggestion:** Replace typographic quotation marks as though they were raw mathematical notation.

**Problem:** Curly quotation marks serve as normal punctuation. They do not have the same meaning or extraction risk as tokens such as `P_U` or `P_{U perpendicular}`.

**Future behavior:** Separate actual spoken formula markup from ordinary punctuation. Quote a concrete extractor or audio failure before calling typography a defect.

### 6. Context rows must not be promoted to defects

**Audit entries:** `145000` (reflections mapping lines) and `115000` (`sine of twice the angle`).

These were retained because their wording and mathematics are already clear. A candidate included for neighboring context should not be counted as an actionable issue unless its own passage has a defect.

## Valuable findings to repeat

Your audit was helpful where it identified a particular failure and supplied a precise edit:

| Lecture | Confirmed issue | Resolution |
| --- | --- | --- |
| `009000` | `eye` appeared before the imaginary unit was clearly introduced | Introduced the imaginary unit and clarified its role in the polarization argument |
| `036000` | “the pair consisting of its first coordinate twice” obscured the adjoint output | Specified that both output coordinates equal the first coordinate of the input triple |
| `083000` | A stranded concluding sentence lacked a clear referent | Repaired the conclusion |
| `096000–097000` | `a one`, `a two`, `a sub k` made approximation-number indexing harder to follow | Repaired the spoken subscripts |
| `111000` | Raw `P_U` and `P_{U perpendicular}` notation occurred in speech | Restated the decomposition into components inside and orthogonal to the subspace |
| `130000`, `132000–135000`, `145000` | `sine theta over two` and related phrases obscured grouping | Replaced with expressions such as “the sine of half theta” |

The review also corrected Markdown emphasis handling in the extractor, rather than stripping readable emphasis from dozens of Markdown source files.

## Required procedure for another audit

1. **Extract the actual narration.** Do not treat headings, metadata sidecars, citations, or display-only Lean appendices as spoken content. Use `extract_narration.py` and inspect the full local paragraph.
2. **Identify the mathematical claim.** If proposing a change to notation or a theorem statement, inspect the corresponding formula, definitions, and hypotheses. State what the notation denotes before recommending substitution.
3. **Classify the evidence.** Use `confirmed_defect`, `audio_test_candidate`, `style_preference`, `already_resolved`, or `no_change`. An untested pronunciation concern belongs in `audio_test_candidate`.
4. **Propose the smallest correct edit.** Quote the exact current span and a replacement that retains mathematical content. Avoid blanket normalization, invented synonyms, or rewrites of entire paragraphs for one token.
5. **Check independence and natural speech.** The replacement must work without earlier lectures and must not introduce editorial or implementation commentary.
6. **Verify the change locally.** Reread the paragraph after replacement; check ambiguous parentheses, radicals, half-angles, norm types, and any numerical identities. Confirm extraction still works.
7. **Report only actual defects as the actionable queue.** Keep listening experiments and stylistic suggestions in separate sections. Do not relabel low-confidence possibilities as urgent issues because they occur frequently.

### Expected candidate format

For each candidate, provide:

- `lecture_id` and a quoted **current** passage (not an obsolete version).
- `classification`: one of the five categories above.
- `reason`: the precise mathematical, grammatical, or audio issue.
- `evidence`: the formula, local context, or observed audio behavior establishing that issue.
- `replacement`: exact replacement text, if `confirmed_defect`; otherwise omit.
- `impact`: the mathematical meaning that must remain unchanged.

Do not force a finding for every lecture. A lecture with no supported defect should be marked `no_change`.

## Current follow-up

The outstanding pronunciation sample is: **adjoint**, **Ky Fan**, **Sz.-Nagy**, **Hölder**, **orthonormal**, and the letter **i** in complex-number sentences. Record the synthesized voice's actual rendering and, where necessary, propose a voice-specific pronunciation alias.

The accepted wording and extractor fixes were delivered separately in `dkps-qwen-feedback-reviewed-overlay-2026-11-08.zip`. This document provides feedback to the reviewer and does not replace that lecture overlay.

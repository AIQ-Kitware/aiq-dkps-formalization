# Qwen feedback review and lecture revisions — 8 November 2026

Reviewed `qwen-audit-results.md` and all 67 entries in `qwen-audit-candidates-2026-11-08.tsv` against the current transcripts. Each entry has an individual decision in [`qwen-feedback-disposition-2026-11-08.tsv`](qwen-feedback-disposition-2026-11-08.tsv). The original feedback is retained.

## Disposition

| Decision | Feedback rows |
| --- | ---: |
| Repaired spoken wording | 28 |
| Previously resolved | 20 |
| Extractor repaired (Markdown emphasis) | 1 |
| Partially revised; conventional theorem names retained | 1 |
| Rejected false positives | 5 |
| Retained correct wording | 4 |
| Requires a listening check of the actual voice | 6 |
| Retained attribution; pronunciation to be checked by listening | 2 |
| **Total** | **67** |

Nineteen transcripts were revised. The repairs include literal projection syntax in `111000`, the definition of the imaginary unit in `009000`, the adjoint output in `036000`, approximation-number subscripts in `096000–097000`, and unambiguous half-angle expressions in `130000`, `132000–135000`, and `145000`. The stranded conclusion in `083000` was removed. `116000`, `121000`, and `149000` now explain doubled-angle formulas in spoken English.

The extractor now removes ordinary inline Markdown emphasis markers (`*...*` and `**...**`) from narration output while preserving the source Markdown and the separate mathematical/Lean appendices. An extractor regression test covers this behavior.

## Substantive false positives

**`072000`, `073000`, `088000`: `ell two` versus `L two`.** The lower-case script ell notation \(\ell^2\) denotes square-summable sequences, while \(L^2\) denotes square-integrable functions. The lectures deliberately compare the two spaces. Qwen's proposed course-wide substitution would erase this distinction. Their definitions remain in place.

**`048000`: `Sz.-Nagy`.** `Sz.-Nagy` is a conventional abbreviation for Szőkefalvi-Nagy's surname. Replacing it with `Nagy` solely to simplify pronunciation changes the attribution. Keep the original and assess the selected voice before adding a pronunciation alias.

**`099000`: `Hölder`.** The name and mathematical attribution are correct. Retain the diacritic; test the voice rather than replacing a named inequality without evidence of an actual failure.

**`084000` and other postfix-star cases:** Saying “X star” for \(X^*\) and “X adjoint” are both standard. Different usage is acceptable when locally clear. The proposed blanket conversion was not applied.

**Curly quotation marks:** Ordinary punctuation has no mathematical ambiguity and is not raw formula syntax. They remain.

## Additional problems identified in review

- **`111000`**: “the square root of three over two” admits two possible groupings in speech. Revised to “the square root of three divided by two,” consistent with the stated numerical value.
- **`130000`**: The chord formula needed grouping both inside the square root and at the half-angle. It now says “the square root of the difference between two and twice the cosine of theta” and “twice the sine of half theta.”
- **`134000`**: A second half-angle ambiguity was present in the trace-cost comparison at the end of the counterexample, beyond the instances listed in the audit.

The review kept mathematically meaningful spectral-gap qualifications and did not replace proper mathematical names with speculative phonetic spellings.

## Checks

- All 150 transcript files pass `extract_narration.py --check`.
- All 150 metadata sidecars validate: 49 historical claim anchors, 735 external-resource assignments, 69 catalog sources.
- All eight extractor and metadata regression tests pass.
- The mathematical/Lean appendices of all 150 lectures are unchanged.

## Remaining listening checks

Test a short sample of the selected TTS voice on the terms **adjoint**, **Ky Fan**, **Sz.-Nagy**, **Hölder**, **orthonormal**, and the letter **i** in a complex-number sentence. Add pronunciation aliases only for observed failures. These are recorded as `audio_check` or `retain_with_audio_check` in the disposition ledger.

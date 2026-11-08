# DKPS transcript citation sidecars — initial audit and implementation

**Date:** 2026-11-08  
**Baseline:** source archive `aiq-dkps-formalization-source-2026-11-08T135904-5-2deee28d14f6.tar.gz`, followed by the standalone, pedagogical-structure, and LLMism overlays distributed earlier on 2026-11-08.  
**Scope:** 150 numbered transcript drafts in `visualizations/draft-stages/tts-lectures/`. No mathematical theorem files, narrated text, spoken-region markers, Lean appendices, slides, images, or presentation artifacts were changed.

## Summary

| Measure | Result |
| --- | ---: |
| Numbered lecture sidecars | 150 |
| Lectures with historical/source-attribution anchors | 32 |
| Historical/source-attribution anchors | 49 |
| Lectures with optional reading references | 149 |
| Per-lecture optional source links | 300 |
| Unique bibliographic records | 18 |
| Historical claims verified against exact primary-source passages in this pass | 0 |
| Anchors and source IDs passing structural validation | 49 / 49 |
| Narrations passing the unmodified extractor | 150 / 150 |
| New regression tests passing | 5 / 5 |

The initial citation index contains 49 anchored claims and 18 bibliographic records. References come from `visualizations/lectures/**/resources.yaml`, the repository's external-literature registry, and publisher or institutional records. The 49 claims are queued for primary-passage comparison.

## What was indexed

The historical annotations target (1) attribution of methods to researchers, (2) claims that a specific result is stated in the 1970 Davis–Kahan paper, (3) statements about printed assumptions, theorem scope, examples, and the paper's numbered questions, and (4) original sources associated with such names as Halmos, Rosenblum, Eckart–Young, and Yu–Wang–Samworth.

The source-location hints include Theorems 5.1, 6.1–6.3 and 8.1–8.2, Lemmas 6.1–6.3, Propositions 4.1, 4.3, 4.4 and 6.1, the Section 9 beam model, and Questions 10.1–10.4. All 49 entries have status `pending_primary_passage_comparison`. The next audit will record the matching source passages and exact hypotheses.

The optional `related_resources` selections distinguish finite-matrix teaching material from Hilbert-space generalizations. Reused resources include Gilbert Strang's MIT OpenCourseWare lectures on projections, SVD, positive definite matrices and the matrix exponential; Nicholas Higham's explanations; alternative university notes on Rayleigh–Ritz and Davis–Kahan; the original Davis–Kahan, Halmos, Rosenblum, and Eckart–Young papers; and books by Kato and Bhatia.

Individual sidecars state the topic and scope of each optional resource. The 1970 historical-source audit uses `dev/external-literature-references.md`, `prose/distilled_literature/DavisKahan1970_part_III.tex`, and the printed paper's theorem and page locators.

## Representative examples

- **`045000`:** The phrase identifying Halmos's two-projection decomposition is anchored to Halmos (1969). The original statement is indexed for passage comparison.
- **`053000`:** The Eckart–Young optimality attribution is anchored to the 1936 paper; Strang's SVD recording is separately offered as an alternate explanation.
- **`068000`:** Both the attribution to Davis–Kahan Theorem 5.1 and the subsequent description of its scope have distinct anchors for comparison with the printed source.
- **`120000`:** Theorem 8.2, its self-adjoint completion method, and its crossed-defect qualification are separately marked; their exact statements and hypotheses are the review targets.
- **`134000`:** The printed universal minimization statement in Proposition 4.4 is indexed. The four-dimensional counterexample appears in the lecture appendix and project formalization.
- **`147000`:** The attribution of population-gap bounds to Yu, Wang, and Samworth is linked to the 2015 research article, with an open preprint supplied as optional reading.

## Why sidecars, not inline citation tags

The current `extract_narration.py` reads exclusively between the two spoken-region markers. No citation tokens were inserted in that region or elsewhere in the lecture Markdown. Sidecar references are keyed by lecture number and uniquely matched to an **exact excerpt** of extracted narration. Validation rejects anchors that are missing, duplicated, or no longer match the words being spoken.

`reference_metadata.py --json 053000` produces a combined record for a future learning system. The record includes the exact extractor output, source citations, source bibliographic entries, optional resources, and actual character offsets. This combined record is *not* a TTS input format; the unchanged extractor remains the TTS input producer.

## Validation commands

Run from the repository root:

```bash
python3 visualizations/draft-stages/tts-lectures/reference_metadata.py --check
python3 -m unittest discover \
  -s visualizations/draft-stages/tts-lectures \
  -p test_reference_metadata.py
python3 visualizations/draft-stages/tts-lectures/extract_narration.py --check \
  visualizations/draft-stages/tts-lectures/[0-9]*-*.md
```

The ZIP contains no numbered transcript Markdown files. All 150 transcripts and their appendices are unchanged.

## Next source-audit steps

1. Review the [49-row claim ledger](reference-claims-2026-11-08.tsv) against the actual primary text, with higher priority for historical claims about Proposition 4.4, Theorems 6.1–6.3 and 8.1–8.2, and source errata. Add page/formula locators and reviewer evidence before changing status to `primary_passage_confirmed`.
2. Check the named `Sz.-Nagy–Kato` attribution in `048000` against original sources rather than inferring priority from a later monograph. Keep it pending until the historical origin is established.
3. Perform a second human review for historical assertions not captured by this initial candidate inventory. Add entries only for externally verifiable attributions or claims about published texts; do not turn routine mathematical proofs into a bibliography exercise.
4. Review the per-lecture external-resource choices for topic and assumed background before the future server presents them to students.

The [150-row per-lecture ledger](reference-audit-by-lecture-2026-11-08.tsv) records which recordings currently have historical candidates and optional sources. The historical-anchor count and selected learning resources appear in separate columns.

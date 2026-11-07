# Transcript-first TTS drafts

These files are an **alternative, additive drafting branch**, following `../outline.md` rather than the existing `visualizations/lectures` Manim scene plan. They are not production video scripts or a second mathematical authority. The journal manuscript and formal proof sources remain the sources of mathematical scope; mathematical dependency determines lecture progression.

## Draft set

| File | Main learning result | Status |
| --- | --- | --- |
| `000000-course-introduction.md` | Course orientation; conceptual only, no mandatory Lean | Earlier staged overlay, not included in this ZIP |
| `001000-linear-maps-independent-of-coordinates.md` | Coordinate change is not change of operator | First spoken draft |
| `002000-norms-distances-and-convergence.md` | Norm axioms, induced distance, norm equivalence and its finite-dimensional limitation | First spoken draft |
| `003000-cauchy-sequences-and-banach-spaces.md` | Completeness; a Cauchy counterexample in polynomials; completeness of continuous functions | First spoken draft |

The IDs are the ones already reserved in `../outline.md`, spaced by 1,000 for insertions. No existing lecture sources or their names are modified.

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

## Transcript review standard

Check independently that:

1. The lesson works without animation and builds each new concept from previously taught mathematics.
2. Its theorems include a clear setting, their required hypotheses, and a reconstructible argument.
3. Its examples distinguish a particular computation from a general statement, and include a useful boundary or failure case when applicable.
4. Every symbol to Lean connection maps to a verified declaration or explicitly identified excerpt. Track TauCeti's current implementation separately from DKPS's donor/provenance history.
5. The spoken region contains no raw code or notation that makes synthetic speech hard to follow.
6. The listener can answer a new question using the ideas, not just repeat the conclusion.

The three new scripts are editorial drafts from the repository source snapshot dated 2026-11-07. The Lean blocks have been checked against that snapshot as text, not compiled in this environment. They do not constitute a new formalization.

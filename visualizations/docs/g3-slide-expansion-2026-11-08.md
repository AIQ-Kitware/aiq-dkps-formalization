# G3 companion-slide expansion — 8 November 2026

All 24 G3 lectures after the existing two-deck pilot now have independent
text-rich companion slide sources. These are attached by stable graph identities
`g3:002000` through `g3:025000` and appear in the existing audio reader.

## Source and visual approach

- Narration: the 24 revised G3 lecture manuscripts provide the mathematical
  explanations, proofs, examples, and hypotheses. Text is segmented at
  mathematical section and sentence boundaries so the slide pages are readable
  on their own. No audio timing or TTS endpoint is required.
- Equations: manually curated mathematical formulas are highlighted for the
  corresponding proof sections; the accompanying paragraph provides context.
- Figures: shared SVG redrawings of the geometry already implemented in
  G1 Manim scenes. The scene names appear in the SVG `<desc>` and in
  `companion-slides/figures/README.md`. This reuse is vector-source adaptation,
  not a video-frame export.
- Build: repository JSON sources become self-contained HTML with embedded SVG.
  The optional PptxGenJS exporter embeds the same SVG sources. The cache is
  ignored by Git and invalidates on source and figure changes.
- Graph: the single manifest registers exactly one companion deck for each of
  the 26 G3 lecture nodes. G2 sources are not duplicated.

## Where to inspect first

- `g3:003000`: trial-plane residual and Ritz compression
- `g3:004000`: principal-angle cosine and sine geometry
- `g3:008000`: entrywise Sylvester equation
- `g3:020000`: the sharp sine-theta proof
- `g3:024000`: four-dimensional Proposition 4.4 counterexample
- `g3:025000`: the real transport matching theorem

The former pilot slides were authored as concise summaries. The new deck set
leans toward *reading presentations*: it retains longer proof steps and worked
examples, so some lectures have more slides than their audio duration would
suggest. Editorial shortening and custom animation sequencing can be done
without changing the track's narration or graph links.

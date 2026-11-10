# Companion slides: Manim as the single composition engine

Companion-slide content is stored in readable JSON decks under
`visualizations/companion-slides/`, associated with G2/G3 lecture nodes through
`manifest.json`. This text content is independent of TTS speech extraction.

## Rendering architecture

The slide frame, heading, equations, diagram, argument text, and summary are
all composed into a fixed **16:9 Manim scene**:

- `dkvis.presentation.companion_manim` builds the slide composition, using
  `MathTex`, `Text`, and native Manim objects.
- `dkvis.presentation.companion_geometry` builds diagrams using native Manim
  primitives. Its explicit registry covers every diagram used in the deck
  inventory. New identifiers require an implementation, rather than a fallback
  picture from another topic.
- `dkvis.presentation.companion_slides` renders Manim frames and packages them
  in a self-contained HTML deck for the browser and offline sharing. It embeds
  each PNG as a data URI so no external assets are required to view slides.
- `dkvis.presentation.companion_export` supplies the **same cached PNG frames**
  to the PowerPoint exporter. The exporter no longer lays out a separate slide
  with PowerPoint text boxes and SVG illustrations.

Manim is required for generating new frames. Rendering does not fall back to
HTML or raw SVG drawing. Generated PNG, HTML, SVG, and PowerPoint outputs are
build artifacts and should remain outside Git. Content source files, Python
scene code, and manifest entries are committed.

## Browser workflow

Open an audio lecture in the local library, choose **Show slides**, and the
companion deck will render (or reuse cached frames). Slides remain separate
from audio timing. Arrow keys navigate the deck. The standalone HTML is fully
self-contained and can be printed to PDF.

An edit to deck JSON or the figure/scene source invalidates its cached deck.
The HTML and PowerPoint exporter share the same per-slide PNG cache.

## Build and export

From `visualizations/` in the project's Manim environment:

```bash
python -m dkvis.presentation.companion_slides dkps-fast-path
python -m dkvis.presentation.companion_export \
  companion-slides/dkps-fast-path.json /tmp/dkps-companion-frames --limit 2
node tools/build_companion_pptx.js \
  companion-slides/dkps-fast-path.json /tmp/dkps-fast-path.pptx
```

The `--limit 2` command is a small real-Manim smoke test. PowerPoint exports
are image-based so that their appearance exactly matches the Manim and HTML
slides. They are therefore not individually editable PowerPoint text/shape
objects; edit the JSON and Manim source to make changes.

For a fast QA check of the PowerPoint packaging independently of Manim,
`build_companion_pptx.js` also accepts `--frames-dir <directory>`, containing
`frame-001.png`, `frame-002.png`, and so on. This is intended for diagnostics;
normal builds always call Manim.

## Authoring policy

- A slide should explain a mathematical step or worked example without audio.
- Prefer meaningful geometry tied to the mathematical claim. No SVG source
  drawings and no generic fallback diagrams.
- Use exact `mathtex` for formulas; keep hypotheses and mathematical scope in
  accompanying prose.
- Do not introduce project/tool nomenclature in spoken narration.
- Preserve stable lecture IDs, existing graph relationships, and the shared
  manifest while extending the course.
- Source-level baseline status means that a deck exists but awaits a visual
  editorial review. It is not a final-quality certification.

## Previous migration and four new G2 lectures

The four added audio-first G2 mathematics lectures `091250`, `091500`,
`092250`, and `099500` have ten-slide baseline companions. These should receive
Manim visual QA and eventual editorial expansion in the same manner as the
existing G2 baseline decks.

The previous tracked figures under `companion-slides/figures/*.svg` are
obsolete. After applying the repair overlay, run:

```bash
python visualizations/tools/finish_companion_manim_migration.py --write
```

That removes only their Git index entries; SVG files remain on disk. It also
removes the old Python SVG drawing module if its contents match the reviewed
snapshot, so unknown local edits are preserved.

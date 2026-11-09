# Independent companion slides for the DKPS learning library

Companion slides are separate, source-controlled educational resources linked to course-graph lecture nodes. Their text is complete enough to read without listening to the recording. Showing, hiding, navigating, and rebuilding the slides has no effect on TTS generation or lecture playback.

## Pilot decks

- `dkps-fast-path`: G3 `000000`, *A fast path to Davis–Kahan*, 12 slides. Two-mode perturbation, gaps, principal angles, residual and Sylvester mechanism, angle theorem families, and transport.
- `finite-spectral-picture`: G3 `001000`, *The finite spectral picture*, 13 slides. Complete finite spectral theorem proof, real symmetric reduction, projection formulation, and worked 2-by-2 example.

The source directory is `visualizations/companion-slides/`. Each deck has its own JSON source file; `manifest.json` associates persistent deck identifiers with one or more course-graph lecture nodes. A deck may be linked to additional tracks later without copying its contents. Audio scripts, speech pages, and citation sidecars are unchanged.

## Browser workflow

1. Open `/audio?track=g3&lecture=000000` or `/audio?track=g3&lecture=001000`.
2. Select **Show slides** to build from source if necessary and display the deck at full content width above the complete transcript. The **Build / refresh** button can also rebuild the current source.
3. The full-width slide viewer appears above the transcript. Scroll down to read or select any transcript sentence; the audio player and its progress timeline remain independent of the slides. Navigate slides independently with the slide buttons or arrow keys. **Standalone view** opens them without the audio player. **Download HTML** saves the readable, self-contained deck; the standalone slide viewer also has Print / PDF.
4. The generated HTML is cached under `visualizations/companion-slide-cache/` and is ignored by Git. Edits to a source JSON automatically make its previous build stale; rebuild it from the UI.

Rendered HTML is self-contained: no CDN, remote font, network math service, or external asset URL. **Building** a deck with equations uses Manim `MathTex` when available; otherwise it needs a local TeX installation with `pdflatex`, `standalone`, `amsmath`, `amssymb`, `mathtools`, `bm`, and `mathrsfs`, plus Poppler `pdftocairo`. MathTex outputs are embedded as vector SVG paths in the HTML so viewing a built deck needs no LaTeX installation. Mathematical arguments remain intelligible without audio, and the figures supplement the text.

## Build and optional PowerPoint export

```bash
cd /home/joncrall/code/aiq-dkps-formalization/visualizations
python -m dkvis.presentation.companion_slides
```

Optional editable PowerPoint export of the same source (requires Node.js and `pptxgenjs`):

```bash
node tools/build_companion_pptx.js companion-slides/dkps-fast-path.json /tmp/g3-000000.pptx
node tools/build_companion_pptx.js companion-slides/finite-spectral-picture.json /tmp/g3-001000.pptx
```

The web server never executes Node or an arbitrary client-supplied command. Building a source-controlled mathematical deck **does invoke** Manim/TeX locally to produce SVG equations, and cached results are reused on subsequent requests. It validates deck IDs against the repository-owned manifest and publishes rendered HTML atomically. Use the unauthenticated build endpoint only on a trusted LAN, consistent with the speech-generation endpoints.

## Extension conventions

- Add a stable deck ID and a source JSON file; link it to one or more existing course-graph nodes in `manifest.json`.
- Each slide should have a substantive title, self-contained lead, explanatory paragraphs, and a mathematical conclusion or takeaway; figures supplement the text.
- Prefer complete worked examples and hypotheses over telegraphic bullet-only slides. Avoid lecture-number callbacks and authoring commentary.
- Cross-lecture reuse belongs in the manifest, not in duplicate slide files.
- Audio/slide timeline synchronization is deliberately deferred. Future explicit transcript anchors can live in non-spoken metadata.

## G3 expansion: lectures 002000–025000

All 26 G3 lecture nodes now have a companion deck. The 24 additional sources use
stable `g3-<number>-<slug>` identifiers and preserve the existing audio
transcripts. The original two handcrafted pilot decks are unchanged.

The new reading decks reorganize complete prose from the **current revised G3
transcript sections** into navigable, labeled slides. Where a proof needs
multiple steps, the explanation continues over multiple slides instead of
squeezing the argument into one formula-heavy graphic. Highlighted formulas
provide a quick visual index to the derivation. The sources are editable JSON;
the slide cache is derived at build time.

Sixteen shared SVG figures in `companion-slides/figures/` adapt construction
logic from G1 Manim scenes, including `PaError`, `TrialPlane`, `IbBlocks`,
`S07Theorem`, and `matching.study`. They are editable vector art, not frames
extracted from video. Both the HTML renderer and the optional PowerPoint
exporter use these same vector drawings. The figure README lists their
provenance. Figures are kept out of speech extraction.

Run `python -m dkvis.presentation.companion_slides` to prebuild all decks or
open any G3 audio lecture and select **Show slides** to build only its deck.
A deck source edit or a shared SVG edit changes its content digest and will
cause the cached HTML to refresh on the next build.

## Vector mathematics and visual composition (2026-11-08 revision)

- Equations use a source-level `mathtex` LaTeX field. The renderer converts the equation to vector glyphs via Manim MathTex, or locally through `pdflatex` and `pdftocairo` when Manim is unavailable. Manim installations must have their working TeX toolchain configured. The mathematical string is compiled only from repository-owned JSON, never from an HTTP request body.
- The 26 G3 decks now have 119 typeset equation panels, preserving the manuscript's full explanatory prose. Formula slides emphasize the equation and geometry; long conceptual pages use balanced reading columns and short argumentative paragraphs. The 16 existing SVG figures remain reusable across lectures.
- Edit `mathtex` directly when mathematical notation should be revised. Keep LaTeX mathematically exact and avoid substituting TTS-friendly prose for an equation. Add a `lead`, explanatory `body`, and `takeaway` where needed for standalone comprehension.
- The builder hashes both source and renderer version into the HTML cache key. Generated SVG, HTML, and PowerPoint assets remain untracked.
- For optional PowerPoint output, the exporter invokes the same Python `slide_math` module and embeds the vector math assets instead of Unicode fallbacks. The equations are vector assets, while prose remains editable text.

To use the explicit fallback renderer (when Manim is not installed):

```bash
DKVIS_SLIDE_MATH_RENDERER=latex python -m dkvis.presentation.companion_slides
```

To use Manim MathTex explicitly, set `DKVIS_SLIDE_MATH_RENDERER=manim`. The default `auto` uses Manim if importable and otherwise the TeX/Poppler fallback.

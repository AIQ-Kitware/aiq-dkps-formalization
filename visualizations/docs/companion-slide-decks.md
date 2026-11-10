# Independent companion slides for the DKPS learning library

Companion slides are separate, source-controlled educational resources linked to course-graph lecture nodes. Their text is complete enough to read without listening to the recording. Showing, hiding, navigating, and rebuilding the slides has no effect on TTS generation or lecture playback.

## Visual policy

Companion decks are now **Manim-rendered slide decks**, not HTML-composed pseudo-slides. The JSON files under `visualizations/companion-slides/` remain the editable content source, but a build renders every slide as a fresh Manim scene:

- prose is laid out in a fixed 16:9 slide frame,
- equations use the same MathTex / TeX toolchain as the main DKPS visual decks,
- reusable DKPS figures are imported from repository-owned Python/SVG sources, and
- the standalone deck viewer is only a thin HTML wrapper around the rendered slide images.

This keeps the authoring workflow lightweight while making the exported slides visually consistent with the rest of the Manim presentation stack.

## Pilot decks

- `dkps-fast-path`: G3 `000000`, *A fast path to Davis–Kahan*, 12 slides. Two-mode perturbation, gaps, principal angles, residual and Sylvester mechanism, angle theorem families, and transport.
- `finite-spectral-picture`: G3 `001000`, *The finite spectral picture*, 13 slides. Complete finite spectral theorem proof, real symmetric reduction, projection formulation, and worked 2-by-2 example.

The source directory is `visualizations/companion-slides/`. Each deck has its own JSON source file; `manifest.json` associates persistent deck identifiers with one or more course-graph lecture nodes. A deck may be linked to additional tracks later without copying its contents. Audio scripts, speech pages, and citation sidecars are unchanged.

## Browser workflow

1. Open `/audio?track=g3&lecture=000000` or any other G3 lecture with a linked deck.
2. Select **Show slides** to build from source if necessary and display the deck at full content width above the complete transcript. The **Build / refresh** button can also rebuild the current source.
3. The full-width slide viewer appears above the transcript. Scroll down to read or select any transcript sentence; the audio player and its progress timeline remain independent of the slides. Navigate slides independently with the slide buttons or arrow keys. **Standalone view** opens them without the audio player. **Download HTML** saves the standalone viewer; **Print / PDF** emits the rendered slide images page by page.
4. The generated HTML is cached under `visualizations/companion-slide-cache/` and is ignored by Git. Edits to a source JSON or a companion figure automatically make its previous build stale; rebuild it from the UI.

The served HTML is self-contained: no CDN, remote font, network math service, or external asset URL. Every slide image is embedded directly into the built HTML as a data URI, so the downloaded deck remains portable.

## Build command

```bash
cd /home/joncrall/code/aiq-dkps-formalization/visualizations
python -m dkvis.presentation.companion_slides
```

That command renders each slide through `dkvis.presentation.companion_manim` and writes a standalone HTML viewer to `visualizations/companion-slide-cache/`.

Companion-slide builds now require the local Manim environment used by the rest of the visualizations package. There is no longer a separate HTML-layout renderer or Node-based pseudo-slide export path.

## Extension conventions

- Add a stable deck ID and a source JSON file; link it to one or more existing course-graph nodes in `manifest.json`.
- Each slide should have a substantive title, self-contained lead, explanatory paragraphs, and a mathematical conclusion or takeaway; figures supplement the text.
- Prefer complete worked examples and hypotheses over telegraphic bullet-only slides. Avoid lecture-number callbacks and authoring commentary.
- Cross-lecture reuse belongs in the manifest, not in duplicate slide files.
- Audio/slide timeline synchronization is deliberately deferred. Future explicit transcript anchors can live in non-spoken metadata.

## G3 expansion: lectures 002000–025000

All 26 G3 lecture nodes now have a companion deck. The 24 additional sources use stable `g3-<number>-<slug>` identifiers and preserve the existing audio transcripts. The original two handcrafted pilot decks are unchanged.

The new reading decks reorganize complete prose from the **current revised G3 transcript sections** into navigable, labeled slides. Where a proof needs multiple steps, the explanation continues over multiple slides instead of squeezing the argument into one formula-heavy graphic. Highlighted formulas provide a quick visual index to the derivation.

Sixteen shared companion figures remain reusable across the lecture set, but the source of truth is `dkvis.presentation.companion_figures`, not tracked SVG files under `companion-slides/figures/`.

Run `python -m dkvis.presentation.companion_slides` to prebuild all decks or open any G3 audio lecture and select **Show slides** to build only its deck. A deck source edit or a figure-source edit changes its content digest and will cause the cached HTML to refresh on the next build.

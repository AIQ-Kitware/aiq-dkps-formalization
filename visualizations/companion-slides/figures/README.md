# Companion-slide figure policy

This directory is no longer the source of truth for companion-slide drawings.

Companion-slide figures should be authored as **source-owned Python renderers**
under `visualizations/dkvis/presentation/companion_figures.py`, then embedded
inline into the self-contained HTML decks or exported on demand for PPTX.
Exported SVG files are build products and should stay git-ignored.

Why this policy:

- slide sources should track authored structure, not disposable render outputs;
- companion-slide figures should be reproducible at build time, like MathTex;
- the repository should not accumulate hand-managed exported SVG assets.

Near-term transition note: a few figure definitions in
`companion_figures.py` still wrap legacy redrawings while we migrate toward
cleaner Manim-backed geometric builders. Even during that transition, the repo
tracks the Python figure source, not exported SVG files.

# Reusable slide components

This package owns reusable visual primitives. Topic scenes and numerical examples
live in `dkvis/learning/<topic>/`; transcripts live in numbered `lectures/` folders
indexed by `lectures/index.yaml`. See
`../learning/README.md`. Deck manifests compose those scenes and
`dkvis/presentation/` supplies the shared production pipeline.

`dkvis.slides_*` remains working reference material for topics not yet migrated,
so the old decks can be rendered while new compositions are built.

`common/` contains geometry, layout, and readout primitives. Keep reusable
mathematical explanations in the topic packages, with the numerical model
separate from its renderers. Existing sine-theta, angle-family, Proposition 4.4,
process, and 3D scenes can move by concept when that helps an actual lesson;
the module catalog records the existing material.

When migrating a scene, keep its class name stable until the deck manifests have
been deliberately updated.  Prefer extracting shared primitives first, then move
whole conceptual groups.  Do not create `v2`, `final2`, or similar scene names;
use descriptive alternatives when two explanations are worth comparing.

`lean_code.py` renders Lean 4 syntax using the bundled, licensed JuliaMono font
under `fonts/`; no system font installation or rendering-time download is needed.
`LessonLean` shows one checked example per slide, its symbolic formula and scope,
and a separate library-proof highlight. `DKVIS_LEAN_FONT` overrides the font.
The frozen reference decks keep their existing typography.

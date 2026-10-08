# Reusable slide components

This package is the destination for reusable visualization code.  The first
reorganization pass deliberately does **not** mechanically move every scene:
`dkvis.slides_*` remains the reference implementation so the old decks can be
rendered as a regression baseline while new compositions are built.

Migrate by concept, not by file size.  A useful target is:

- `common/`: geometry, layout, readouts and other presentation primitives;
- `sine_theta/`: motivation, angle, residual/gap, theorem, proof intuition, Lean;
- `family/`: tan-theta, sin-two-theta and tan-two-theta components;
- `prop44/`: claim, counterexample, explanation and repair;
- `process/`: workflow, confidence/evidence and claim-boundary components;
- `three_d/`: reusable 3D presentation components;
- `glossary/`: notation/reference components.

When migrating a scene, keep its class name stable until the deck manifests have
been deliberately updated.  Prefer extracting shared primitives first, then move
whole conceptual groups.  Do not create `v2`, `final2`, or similar scene names;
use descriptive alternatives when two explanations are worth comparing.

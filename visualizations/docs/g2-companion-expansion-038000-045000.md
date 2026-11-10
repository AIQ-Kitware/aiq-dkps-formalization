# G2 companion-slide expansion: 038000–045000

Eight source-controlled decks have been revised from first-pass outlines to
individually authored mathematical companions. Spoken lectures are unchanged.
The decks include proof arguments, explicit hypotheses, worked cases, and
editable vector figures (10 new SVG assets). Slides are self-contained for reading without audio.

| G2 ID | Specific additions |
| --- | --- |
| 038000 | Initial/final spaces, canonical polar-factor uniqueness, rank-deficient example, unitary completion |
| 039000 | Norm-convergent exponential series, nilpotent shear, flow law, noncommuting generators, planar rotation |
| 040000 | Squared-norm derivative, skew-adjoint converse, unitary flow, complex phase, noncommuting axes |
| 041000 | Spectral/series constructions, Pythagorean identity, inverse-angle branch, unitary block rotation |
| 042000 | Cross-Gram SVD, tilted-plane calculation, principal frames, rectangular-dimension convention |
| 043000 | Directed cosine/sine maps, Pythagorean identity, projection-difference square, 45° check |
| 044000 | Principal-plane construction, C–S matrices, endpoint blocks, doubled-angle identity |
| 045000 | Four Halmos intersections, six-dimensional construction, generic block, infinite-dimensional injectivity caution |

The G2 038000–045000 promotion is applied as a manifest update rather than a
manifest replacement. This preserves concurrent additions and the G3 curriculum
repair. The installer verifies that every target deck is present and already
authored at the expanded stage before modifying its manifest entry.

From the repository root:

```bash
python3 visualizations/tools/promote_g2_038000_045000.py --write
python3 visualizations/tools/promote_g2_038000_045000.py --check
cd visualizations
python3 -m pytest -q tests/test_g2_batch2_companions.py
python3 tools/audit_companion_coverage.py --check
```

The source-only promotion is separate from the HTML and PowerPoint export.
The edited source decks remain editable JSON; equations compile to vector SVG
via the existing Manim MathTex/TeX renderer, and drawings are source-controlled.
Future editorial work can continue in curriculum order without regenerating
narration or touching audio caches.

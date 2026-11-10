# G2 companion-slide expansion: Sylvester equations (062000–069000)

Eight baseline companion decks have been expanded into 10-slide mathematical
presentations. The source-controlled decks reuse the spoken lectures' examples,
but are intended to stand alone: each includes its own definitions, derivations,
and vector figures. No narration or G3 source has been modified.

| Lecture | Expanded mathematical development |
|---|---|
| `062000` | Scalar denominators, correctly typed two-sided operators, eigenvector pair coefficients, spectrum of the Sylvester map |
| `063000` | Two-by-two entrywise solution and multiplication check, repeated-eigenvalue compatibility, sharp Frobenius bound, projector formula |
| `064000` | Column vectorization, Kronecker representation, spectral difference criterion, invertibility versus conditioning |
| `065000` | Ordered gap, scalar Laplace identity, decaying operator integral, differentiation proof, constant-one sharpness |
| `066000` | Unitary Sylvester orbit, Fourier reciprocal multiplier, mixed-sign gap, π/2 operator-norm estimate |
| `067000` | Resolvent cancellation, separating contours, uniqueness, scalar residue, multi-loop versus circle hypotheses |
| `068000` | Theorem 5.1 inverse hypotheses, compatible Banach norms, affine fixed point, Neumann-series existence and constant-one bound |
| `069000` | Distinct norm classes, pairwise versus ordered constants, rank dependence, explicit two-by-two operator-norm obstruction |

Assets include 15 mathematical SVG figures, 72 rendered MathTex expressions,
and reproducible numerical checks. The figures are source-controlled, editable,
and do not depend on TTS or third-party illustration downloads.

## Apply

From the repository root, extract the overlay and run:

```bash
python3 visualizations/tools/promote_g2_062000_069000.py --write
cd visualizations
python3 tools/audit_companion_coverage.py --check
python3 -m pytest -q tests/test_g2_sylvester_companions.py tests/test_companion_slides.py
```

The promotion tool validates eight authored deck files, changes only their
`editorial_stage` fields in the **current** shared `manifest.json`, and writes the
result atomically. It does not replace the manifest from an older snapshot.

## Validation scope

All eight HTML companion decks were rendered using the actual TeX-to-SVG engine
and checked in a 1720×1100 browser viewport; 80/80 passed the content-overflow
check. Representative PowerPoint files were exported through the existing
PptxGenJS exporter and checked for out-of-bounds content. The covered mathematical
assertions were compared with the spoken lectures and display-only appendices.

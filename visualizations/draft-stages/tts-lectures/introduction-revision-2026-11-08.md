# Course introduction and audio-page revision — 8 November 2026

## Introduction

Revised `000000-course-introduction.md` using the full 150-lecture draft sequence and the 17-unit roadmap. The introduction now begins with a two-dimensional symmetric-matrix perturbation and uses that example to motivate spectral gaps, eigenvalue movement, and eigenspace angles.

The narrative follows the main mathematical route:

- Coordinate-free subspace geometry: orthogonal projections, principal angles, Gram maps, graph subspaces, and direct rotations.
- Normed and Hilbert spaces; spectral theory and functional calculus; infinite-dimensional operator domains.
- Residuals, complementary Sylvester equations, spectral separation, and singular-value/norm estimates.
- Sine, tangent, sine-of-twice-the-angle, and tangent-of-twice-the-angle theorems, including branch selection.
- Canonical rotation, the corrected whole-space optimality claim, the free-beam example, and later applications.

The opening calculation uses `A = diag(0, 4)` and `B = [[0, 1], [1, 4]]`: eigenvalues `2 ± √5`, eigenvalue displacement `√5 − 2 ≈ 0.2361`, and acute eigenspace angle `½ arctan(1/2) ≈ 13.2825°`.

Four historical assertions have matching non-spoken sidecar anchors in `metadata/000000.json`, with the claim and per-lecture ledgers updated accordingly. The spoken lecture contains no bibliographic tags or implementation commentary.

## Audio reader

The default speech page is now 1,200 characters, increased from 420. The configured range remains 250–1,500 through `DKVIS_AUDIO_PAGE_CHARS`; the default page splitter agrees with the server setting. Existing stored voice profiles and the selectable Kokoro/Crall providers remain unchanged.

Under the current paginator, the introduction changes from 36 pages to 12. Lecture `021000` changes from 33 to 10 pages. Pages remain sentence/paragraph-aware, and the full extracted narration is preserved.

## Checks

- All 150 lecture extractions pass.
- All 150 sidecars validate, with 51 historical claim anchors.
- 33 audio-library/media-server tests pass.
- 5 reference-metadata tests pass.
- The two-dimensional numerical example was checked against the exact eigenvalue and angle formulas.

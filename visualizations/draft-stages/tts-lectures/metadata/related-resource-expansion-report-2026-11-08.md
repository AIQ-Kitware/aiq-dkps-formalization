# DKPS related-resource expansion — 8 November 2026

This pass adds **25 external learning resources** to the shared reference catalog and **149 lecture-specific recommendations** across **94 of the 150 recordings**. There are now **43 catalog entries** and **449 related-resource links** across the course.

The source list includes 4 3Blue1Brown explanations, 15 Nick Higham articles, two MIT 18.102 functional-analysis collections, MIT matrix-calculus notes, Intel's principal-angle algorithm, Jordan Bell's projection-valued-measure notes, and Wisconsin uniform-convergence notes.

## Selection and placement

- **Foundations (001000–038000):** visual explanations of linear maps, duality, eigenvectors, matrix norms, invariant subspaces, positive operators, and SVD; the MIT 18.102 course adds Banach/Hilbert-space depth.
- **Angles and geometry (042000–051000):** the cosine–sine decomposition and Intel's QR/SVD calculation complement the two-projection geometry.
- **Norms and inequalities (052000–061000 and 097000–134000):** Higham's singular-value and unitarily invariant norm articles provide alternative derivations of the finite-matrix background.
- **Sylvester equations and matrix flows (064000, 039000–041000, 066000–070000, 092000):** the Kronecker product and matrix-exponential resources show concrete algebraic formulations.
- **Spectral theory (075000–088000):** Jordan Bell's notes present spectral measures and integration; Higham explains finite-matrix functional calculus.
- **Matrix perturbations and applications (107000–148000):** numerical principal-angle computation, matrix derivatives, pseudoinverses and uniform convergence provide additional examples.

Each sidecar names its sources and says what to study in them. All recommendations remain in `metadata/*.json`; the lecture Markdown and spoken extraction are unchanged.

## Inventory

- `related-resource-expansion-2026-11-08.tsv`: one row for every new recommendation, with a reason.
- `related-resource-coverage-2026-11-08.tsv`: totals and additions for every lecture.
- `sources.json`: reusable bibliographic entries, each with its HTTPS URL and origin.

## Checks

```bash
python3 visualizations/draft-stages/tts-lectures/reference_metadata.py --check
python3 -m unittest discover -s visualizations/draft-stages/tts-lectures -p test_reference_metadata.py
python3 visualizations/draft-stages/tts-lectures/extract_narration.py --check visualizations/draft-stages/tts-lectures/[0-9]*-*.md
```

All prior historical-claim anchors and statuses are preserved. No narrated text or mathematical appendix is modified.

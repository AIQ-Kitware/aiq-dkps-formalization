# Standalone TeX studies

These sources are independent of the current journal manuscript's input graph.
Build them from the **journal directory**, not from `studies/`, so the common
bibliography, symbol registry, snapshots, and `build/` output directory remain
available:

```bash
make matching-study
make literature
```

The build outputs remain `build/matching_proof_study.pdf` and
`build/literature_review.pdf`.

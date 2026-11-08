# DKPS free external learning resources — additional search (8 November 2026)

Added **26 freely accessible sources** and **286 lecture-specific links** in **132 lectures**. Catalog totals: **69 sources**, **735 related-resource associations**.

## Selection

All new entries have a public HTTPS landing page and an `access: free_no_login` field. The additions favor complete notes, full open books, university lecture recordings, worked examples, and publicly readable research papers. Existing historical claim citations are unchanged.

- **Open books:** Axler, Boyd–Vandenberghe, Hunter–Nachtergaele, Teschl, and Deisenroth–Faisal–Ong.
- **Recorded teaching:** MIT 18.065 lectures on the SVD, Eckart–Young, norms, Procrustes, and graph clustering; Stanford EE263 archived notes/slides/video links.
- **Alternative proofs:** Tao's Hermitian matrix inequalities; Bell's compact-SVD and operator-ideal notes; Bindel's symmetric eigenproblem, perturbation, and Rayleigh–Ritz notes.
- **Advanced subspace geometry:** Zhu–Knyazev on tangent angles, Kostrykin–Makarov–Motovilov on tan 2Θ, and Motovilov–Selin on sharp perturbation bounds.

## Design

- Catalog additions: `sources.json` (title, author, public URL, free access, format, content synopsis).
- Lecture mappings: `000000.json` through `149000.json` (only those with new links are modified).
- Addition ledger: `free-resource-expansion-round2-2026-11-08.tsv` (one row per new link with learning reason).
- Coverage: `free-resource-coverage-round2-2026-11-08.tsv` (all 150 lectures).

No changes to spoken lecture text, display appendices, extractor, historical-claim anchors, or audit status.

## Reproduce checks

```bash
python3 visualizations/draft-stages/tts-lectures/reference_metadata.py --check
python3 -m unittest discover -s visualizations/draft-stages/tts-lectures -p test_reference_metadata.py
python3 visualizations/draft-stages/tts-lectures/extract_narration.py --check visualizations/draft-stages/tts-lectures/[0-9]*-*.md
```

# G2 companion expansion 046000–053000

Eight G2 baseline companion decks are expanded into independently readable
mathematical presentations. The TTS source lectures and the G3 course track
are unchanged. All equations are source-controlled MathTex rendered to SVG;
11 new figures are source-controlled, editable SVG illustrations.

| Lecture | Material developed on the slides |
| --- | --- |
| 046000 | Ambient sine/cosine, commutation with both projections, endpoint cases and angle functional calculus |
| 047000 | Crossed defects versus uniform gap, graph parameterization, unbounded-angle counterexample |
| 048000 | Sz.-Nagy–Kato intertwiner, exact modulus, planar example, polar normalization and acute extension |
| 049000 | Direct rotation from polar factor, positivity characterization, reflection square and reverse transport |
| 050000 | Source/target right-angle defects, chosen isometry, quarter-turn, regular–defect splitting and shift obstruction |
| 051000 | Four endpoint invariants, compact cosine classification, diagonal and continuous-spectrum counterexamples |
| 052000 | Singular-value min–max games, intersection proofs, rectangular example and rank lower bound |
| 053000 | Truncated SVD, operator and Frobenius optimality, Ky Fan energy proof and tied-value cases |

After extraction, edit **only** these eight manifest statuses using the included
promotion tool. The JSON source files are replaced in place; the full shared
manifest is not supplied, protecting other agents' updates.

```bash
cd /home/joncrall/code/aiq-dkps-formalization
python3 visualizations/tools/promote_g2_046000_053000.py --write
python3 visualizations/tools/promote_g2_046000_053000.py --check
cd visualizations
python3 -m pytest -q tests/test_g2_batch3_companions.py tests/test_companion_slides.py
python3 tools/audit_companion_coverage.py --check
```

The decks can be opened from `/audio?track=g2&lecture=046000` onward and the
PptxGenJS exporter in `tools/build_companion_pptx.js`. Existing audio caches are
not touched. The editorial stage ``expanded`` indicates a substantial curated
mathematical pass; it is not a certification that every slide is final.

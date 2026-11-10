# G2 companion expansion 054000–061000

Eight G2 baseline companion decks are expanded into mathematical slide
presentations. The original spoken lectures, G3 track, and other companion decks
are unchanged. Each deck has 10 slides with explicit formulas, proof steps,
worked examples, and topic-specific SVG diagrams.

| Lecture | Expanded content |
| --- | --- |
| `054000` | Ky Fan frame variational formula; Bessel overlap bound; triangle inequality; pinching; counterexample to individual singular-value bounds |
| `055000` | Weak vs ordinary majorization; prefix inequalities; weighted summation by parts; mass transfer |
| `056000` | Two-coordinate T-transforms; convex descent; sign-symmetric shrinkage; failure for p below one |
| `057000` | Nuclear, Frobenius and operator norms; rectangular (4,3) example; Gram trace identity; rank bounds |
| `058000` | Symmetric gauges and invariant norms; SVD reduction; triangle proof; ideal versus fixed-shape norm |
| `059000` | Input/output isometric padding and exact Gram identities; shape-dependent norm counterexample; compression distinction |
| `060000` | Block reflection identity; pinching contraction; singular-value concatenation; Schatten direct-sum powers |
| `061000` | Loewner-order min–max; rectangular Gram comparison; explicit counterexample to operator squaring |

## Installation

Extract the accompanying ZIP into the repository root, then run:

```bash
python3 visualizations/tools/promote_g2_054000_061000.py --write
cd visualizations
python3 tools/audit_companion_coverage.py --check
python3 -m pytest -q tests/test_g2_batch4_companions.py tests/test_companion_slides.py
```

The promotion script reads the current manifest, validates the eight new deck
sources, and changes only those eight stage fields. It neither rewrites the
G3 ordering nor overwrites unrelated manifest edits.

## Mathematical and visual QA

All MathTex expressions must build with the real vector renderer; representative
HTML and PPTX decks must pass visual overflow checks before delivery. The
baseline/expanded status identifies a separate editorial development pass, not
an assertion that a finished deck is beyond revision.

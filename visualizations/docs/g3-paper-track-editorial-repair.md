# G3 paper-track editorial repair — 2026-11-09

The G3 audio path now contains 27 complete spoken lectures. Permanent lecture IDs
remain unchanged. The one new recording is `018500`, adapted from G2 `132000`,
which teaches Proposition 4.3's whole-space squared displacement theorem.

## Listening order

The source of the curated G3 listening order is `draft-stages/tts-paper/track.json`.
The audio reader and the course graph consume that order, not sorted filenames.
The Section 4 transport sequence appears at the end of G3:

- `017000` — Restricted direct rotation (Proposition 4.1)
- `018000` — Squared sine-angle bound (Proposition 4.2)
- `018500` — Whole-space squared displacement (Proposition 4.3)
- `019000` — Difference between squared and unsquared full displacement
- `024000` — Proposition 4.4 counterexample
- `025000` — Real transport matching theorem

The four angle theorems `020000`–`023000` form a contiguous block immediately
before Section 4. This is a deliberate teaching order; the 1970 paper orders
Section 4 before the Section 6 angle theorems. Navigation order is not a
mathematical dependency, and the course graph keeps those edges distinct.

## Mathematical contract for Proposition 4.3

Write `G_W = (I - W)^* (I - W)` for full positive squared displacement. In the
admissible direct-rotation setting, the direct rotation `D` obeys Ky Fan prefix
inequalities `K_k(G_D) <= K_k(G_W)` for every admissible competing transporter
`W`. The proof uses restricted singular-value comparison on both the source
subspace and its orthogonal complement, direct-sum Ky Fan dominance, and
pinching by the source reflection. The squared conclusion supplies full
unsquared optimality for Q-norms such as Schatten `p >= 2` with the appropriate
scope and ideal membership; it does not supply arbitrary unsquared UI-norm
optimality. In particular, the trace-norm statement asserted in printed
Proposition 4.4 is false in real dimension four.

The new companion deck includes 12 source-linked slides with a pinching
example using a **positive** matrix `[[3,2],[2,3]]`, whose eigenvalues change
from `(5,1)` to `(3,3)` on pinching. The G2 draft's example with off-diagonal
entries 4 was inappropriate as a positive displacement-square illustration.

## Narration repairs

- Remove dangling G2 defect-matching, Hilbert–Schmidt, and future spectral
  selection references; explain needed context locally.
- Repair the distinction between spectral repulsion and numerical smallness:
  off-diagonal structure selects the less-than-45-degree branch without a small
  perturbation-size assumption.
- Define Courant–Fischer locally at first named use in the G3 selection proof.
- Distinguish the exact subspace `U` from the polar isometry `W` in the
  sine-theta theorem's general-frame normalization.
- Delay the Section 4 counterexample's numerical conclusion until the actual
  construction and place that construction next to its setup in the listening
  order.
- Rename `018000` to match the sine-squared result it proves.

The new narrator source and slide files are source-controlled. Audio generation
remains on demand and already cached page keys are computed from the spoken
text; edited pages naturally produce new cache identities.

## Audits

From `visualizations/`:

```bash
python tools/audit_g3_presentation.py
python tools/audit_companion_coverage.py --check
python -m pytest -q tests/test_g3_presentation_repair.py \
  tests/test_audio_course_tracks.py tests/test_course_graph.py \
  tests/test_companion_slides.py
```

The audit checks the exact G3 track inventory, curated order, contiguous
sections, spoken-word metadata, known stale phrases, and companion coverage.
It cannot determine whether arbitrary new cross-lecture claims are pedagogically
sound; that still needs a content review when G3 is edited again.

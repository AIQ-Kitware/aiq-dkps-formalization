# G3 — Audio paper track

G3 is the shorter, paper-focused alternative to G2's 150-lecture comprehensive sequence.
The browser exposes three course entries:

- **G1 — Manim:** original animated presentations, served at `/`.
- **G2 — Audio comprehensive:** all 150 staged recordings, served at `/audio?track=g2`.
- **G3 — Audio paper:** 27 recordings, served at `/audio?track=g3`.

G3 assumes elementary linear algebra, singular values, Hilbert-space notation, and basic measure theory. Its goal is a tractable path through the original Davis–Kahan angle-theorem families, the failure of Proposition 4.4 for an unsquared displacement norm, and the positive real matching result.

## Sequence

| Position | Recordings | Purpose |
| --- | --- | --- |
| Orientation | `000000` | New high-level entry point and two-by-two perturbation example |
| Foundations and machinery | `001000`–`016000` | Spectral geometry, residuals, Sylvester bounds, domains, norms, reflection, repulsion, and selection |
| Four angle theorems | `020000`–`023000` | Sine θ, tangent θ, sine 2θ, tangent 2θ |
| Section 4 transport | `017000`, `018000`, `018500`, `019000`, `024000`, `025000` | Restricted displacement (4.1), squared sine-angle (4.2), whole-space squared displacement (4.3), scope of 4.4, four-dimensional counterexample, real matching |

`track.json` is the source of ordering, cross-track provenance, and section classification. The audio reader and course graph follow its **explicit list order**, not the six-digit numerical order. Existing IDs remain stable; `018500` is inserted between `018000` and `019000`. The 1970 paper presents Section 4 before the Section 6 angle theorems; G3 deliberately teaches the four angle theorems first and concludes with the repaired Section 4 transport story. It is **not** read as narration. Individual `.md` files use the existing `BEGIN SPOKEN LECTURE` and `END SPOKEN LECTURE` markers. The reader invokes the canonical G2 narration extractor for both tracks.

## Editorial state

The first draft contains one newly written G3 course introduction and 26 adapted, independently listenable G2 recordings. This gives G3 27 complete TTS inputs now; it also makes the provenance of every adapted lecture explicit through `source_g2` entries in `track.json`.

The next editorial pass should review the shortened sequence as a unit: remove repeated explanations across adjacent G3 recordings, strengthen transitions that matter for the 1970 paper, and decide where the assumptions can be shortened for the intended audience. Keep the six result recordings mathematically precise, especially the spectral-gap hypotheses, branch selection, ideal membership, Proposition 4.4's failed scope, and the real matching theorem's exponent and dimension restrictions.

The `metadata/` sidecars contain optional free learning resources and G2 source mappings. No metadata is narrated. Audio caching uses `visualizations/audio-cache/g3/`, separate from G2's existing cache; TTS profile and voice registration are shared.

## Checks

```bash
cd /home/joncrall/code/aiq-dkps-formalization
python3 visualizations/draft-stages/tts-lectures/extract_narration.py --check \
  visualizations/draft-stages/tts-paper/[0-9]*-*.md
cd visualizations
uv run --extra serve --extra test pytest tests/test_audio_course_tracks.py
```

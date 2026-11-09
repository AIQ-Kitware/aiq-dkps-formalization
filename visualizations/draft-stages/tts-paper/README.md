# G3 — Audio paper track

G3 is the shorter, paper-focused alternative to G2's 150-lecture comprehensive sequence.
The browser exposes three course entries:

- **G1 — Manim:** original animated presentations, served at `/`.
- **G2 — Audio comprehensive:** all 150 staged recordings, served at `/audio?track=g2`.
- **G3 — Audio paper:** 26 recordings, served at `/audio?track=g3`.

G3 assumes elementary linear algebra, singular values, Hilbert-space notation, and basic measure theory. Its goal is a tractable path through the original Davis–Kahan angle-theorem families, the failure of Proposition 4.4 for an unsquared displacement norm, and the positive real matching result.

## Sequence

| Position | Recordings | Purpose |
| --- | --- | --- |
| Orientation | `000000` | New high-level entry point and two-by-two perturbation example |
| Main development | `001000`–`019000` | Spectral geometry, residuals, Sylvester bounds, domain/norm distinctions, and direct rotation |
| Six results | `020000`–`025000` | Sine θ, tangent θ, sine 2θ, tangent 2θ, Proposition 4.4 counterexample, real transport matching |

`track.json` is the source of ordering, cross-track provenance, and section classification. It is **not** read as narration. Individual `.md` files use the existing `BEGIN SPOKEN LECTURE` and `END SPOKEN LECTURE` markers. The reader invokes the canonical G2 narration extractor for both tracks.

## Editorial state

The first draft contains one newly written G3 course introduction and 25 adapted, independently listenable G2 recordings. This gives G3 26 complete TTS inputs now; it also makes the provenance of every adapted lecture explicit through `source_g2` entries in `track.json`.

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

# Visualization development journal

## 2026-11-06 — Previous-phrase TTS conditioning drifts

Jon's listening review of the Rayleigh–Ritz continuity experiment found that
conditioning each passage on the preceding generated speech causes **massive
drift over time**. This makes the `previous` strategy unsuitable for lecture
narration in its tested form.

The experiment compared `original`, `previous`, and `anchored` conditioning
with Breeze TTS 2 and the approved `crall-math-dk-v2` reference. In `previous`
mode, each passage after the first uses a whole-phrase excerpt from the preceding
raw generation as its reference. Successive generations therefore inherit any
changes introduced by earlier generations. That feedback is a plausible
explanation for the observed drift, rather than an established diagnosis.

Retain this mode for explicit experiments; do not adopt it as the production
default. Successful generation, cached requests, and improved loudness at joins
do not establish a consistent voice across a lecture. This observation alone
does not settle whether `anchored` mode, which combines the original reference
with the preceding phrase, controls drift adequately.

Implementation: `dkvis/presentation/continuity.py`. Local comparison artifacts:
`renders/experiments/operators-rayleigh-ritz/0f2c468ffd47af47/` (generated and
untracked). Source commit: `e496e1187`.

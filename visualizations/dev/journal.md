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

## 2026-11-06 — An incomplete TTS response survived in the cache

A local Breeze TTS 2 render skipped most of a trial-space explanation near two
minutes. Its raw server response contained only 0.96 seconds for a 60-word
request; processing retained that duration. The short response was joined to
the next sentence and accepted into the video. Ordinary reruns reused it.
A duration scan found no other similarly extreme response in that render.

The speech client now applies a conservative lower-duration sanity check to
fresh and cached passages of at least 20 words. The normal video renderer retries
a rejected request once, preserving the failed audio for diagnosis, and stops
if the replacement is also implausibly short. This checks a concrete failure
mode, not pronunciation or completeness in general. Independent TTS chunks can
still differ in delivery even when their durations are plausible.

## 2026-11-06 — Speech spelling and display spelling are separate

Jon reported pronunciation problems with adjoint, nonnegative, orthonormal,
Frobenius, eigenvectors, Hermitian, Hilbert, Laplacian and matrix. The spellings
non-negative, ortho-normal and eigen-vectors improved at least those three.
They are now configurable speech-only defaults for Breeze TTS 2, while the
canonical transcript and captions retain their original spellings. Other words
remain pending listening tests; there are no guessed default pronunciations.

Standard phonemizers produce representations that a synthesis engine must
understand. Misaki supplies Kokoro-specific pronunciation annotations, whereas
the current local Breeze serving path exposes ordinary text. Use the small
respelling list for that path and prefer native pronunciation controls where
available. The speech cache records both canonical and synthesis text and
invalidates affected requests when a tested hint changes.

## 2026-11-06 — Pronunciation remedies need speaker-specific evidence

Jon clarified that the nine reported words fail for some Breeze speakers, not
all. Only non-negative, ortho-normal and eigen-vectors had reported listening
improvements. The ortho-normal spelling additionally causes an excessive
internal pause, so it is now tentative and excluded from the defaults.

The full list and remedy status live in `pronunciations/README.md`. Accepted
spelling aliases use W3C PLS rather than a new lexicon format. Breeze has a
limited alias adapter; this does not add native phoneme support or integrate
Misaki into its text-only inference path. Local per-speaker lexicons and direct
maps can augment the baseline when new remedies pass listening review. Other
reported words remain unresolved rather than receiving invented substitutions.

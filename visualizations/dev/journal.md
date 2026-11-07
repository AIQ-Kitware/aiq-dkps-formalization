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

## 2026-11-06 — Longer passages for the generic Breeze profile

The 420-character / 65-word defaults were a conservative response to an observed
60-second server cutoff, not benchmarked optimal passage sizes. The named
reference-voice Breeze profiles had already moved to 750 characters / 110 words,
but the generic `breeze` profile still inherited the older limits. Jon requested
a full Rayleigh–Ritz regeneration with longer passages.

The generic profile now uses 750 / 110 as well. Packing the unchanged 3,818-word
Rayleigh–Ritz transcript plans 57 speech requests instead of 88. Requests still
respect visual-build boundaries. Duration-cap splitting and the incomplete-audio
retry guard remain enabled. Deliberate build/slide pauses are unchanged for this
comparison; longer requests alone do not eliminate every narration boundary.

## 2026-11-06 — Visible notation, visual focus, and fewer rhetorical questions

The Rayleigh–Ritz review found spoken wording in a visible takeaway: “P = QQ
transpose” was authored slide text, not a pronunciation transformation. The
slide now displays the mathematical formula, and the compression box is labeled.
Motivating questions remain at investigative steps, while definitions,
observations and deductions use direct statements.

Slide 2 now highlights the original operator, trial space and coordinate frame
as they are introduced. Slide 7 links the moving trial direction to the quotient
curve, displays the substitution, overlays the compressed curve and identifies
the extrema. Normal video rendering now uses the existing forced-alignment and
phrase-cue machinery for decks with authored cues. Visual timing changes within
a coherent speech passage rather than requiring more independent TTS clips.

Hermitian and orthonormal were again reported as pronunciation problems. Neither
has a verified default remedy; ortho-normal remains tentative because of its
internal pause. No new pronunciation guesses were enabled by this revision.

## 2026-11-06 — State the destination before the details

Jon requested a compact opening view of the true statements a lecture will
explain, reinforced by the same statements at the end. Rayleigh–Ritz now opens
with three claims and a whole-construction picture before its notation setup.
The detailed exposition gives terms concrete roles before naming them, and
states the conclusion before longer derivations. The residual-vector quiz
explicitly distinguishes a zero trial-space projection from coordinate entries.

New and revised thinking intervals are five seconds, with no additional build
pause added to that authored interval. Viewers can pause for more time. The
entry lecture is renamed Before the Series: Foundations and owns the common
transpose/conjugate-transpose convention; later lectures state their setting
without repeatedly reteaching that distinction. Stable deck and folder IDs
are retained so existing commands and cached artifacts remain identifiable.

### Polar decomposition: geometry before the formula

The saved viewer comments asked for a usable mental picture of the modulus and
objected to project provenance in spoken mathematical instruction. The revision
starts from the same-input length identity, illustrates positive directional
stretch followed by rotation, and derives the square root from squared output
lengths. The remaining-factor rule is justified before naming its kernel
convention; a singular example distinguishes the canonical partial factor from
a unitary extension. Opening conclusions return in the recap. Project/API
provenance remains in source records and the formal companion, not the spoken
mathematical overview. Four explicit study questions use five-second pauses.

### Broader lecture clarity pass

Revised the fourteen remaining numbered mathematical and historical lectures,
leaving the sine-theta lecture, the recently revised Foundations/Rayleigh–Ritz/
polar lectures, and frozen reference compositions unchanged. Each now opens
with topic-specific conclusions and returns to them in its existing recap.
Transitions explain what the next calculation will establish; mathematical
narration no longer interrupts min–max or Sylvester reasoning with project
provenance. The shared opening component highlights claims during one spoken
passage. Four-question reviews use explicit objects, application questions,
and five-second pauses. Slides and transcript exports are rebuilt separately
from voice selection: existing narrated videos retain their generation records
until the corresponding voice is rebuilt.

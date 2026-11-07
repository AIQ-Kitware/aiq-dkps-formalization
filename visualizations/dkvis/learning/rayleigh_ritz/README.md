# Rayleigh–Ritz: trial spaces, compression, and residuals

Lecture **002749**, stable ID `rayleigh_ritz`, deck **`operators-rayleigh-ritz`**.
A standalone bridge from projections and Rayleigh quotients to the general
Davis–Kahan trial residual. The 28-scene lecture explains choosing a trial
space, its coordinates, compression versus restriction, lifted Ritz pairs,
residual geometry and block structure, fixed-space model fitting, and the
limits of residual information. It includes three accepted Tau Ceti examples,
a separate numerical bonus, and four study questions: two basic checks and two
application questions. The lecture assumes familiar matrix multiplication,
inner products, and eigenvectors, with local reminders for the new notation.

From `visualizations/`:

```bash
make slides DECK=operators-rayleigh-ritz
make text DECK=operators-rayleigh-ritz
make video DECK=operators-rayleigh-ritz TTS_PROFILE=crall-math-dk-v2-breeze-tts2
```

The lecture is indexed before the sine-theta lecture. Existing lecture numbers
are preserved. Restart an existing library server to discover the registration.
Public generated outputs begin `002749_operators-rayleigh-ritz`; source and
media caches retain stable deck/scene identities.

- [Transcript](../../../lectures/002749_rayleigh_ritz/lecture.md)
- [Sources and mathematical scope](../../../lectures/002749_rayleigh_ritz/sources.md)
- [Lean companion](../../../lectures/002749_rayleigh_ritz/facts.lean)

From the repository root, after building the pinned Tau Ceti RayleighRitz module:

```bash
lake env lean visualizations/lectures/002749_rayleigh_ritz/facts.lean
```

The companion applies existing accepted mathematics. `model.py` and its tests
supply evidence for the finite diagrams, distinct Ritz residuals, and changes
of trial coordinates. The matrix explanation does not waive the domain
conditions of the general unbounded residual theorem.

The 2026-11-06 revision connects the slide-to-slide argument in the spoken
narration and introduces the principal derivations in stages. The progress
strip names the lecture's own route. Rebuild slides and narration together;
old narrated videos retain their original speech and reveal timing.

The visual revision reuses one trial plane through coordinate embedding,
compression, Ritz vectors, residual columns, block structure, and the direct
orthogonality calculation. Amber identifies trial quantities, cyan the true
operator output, and green the residual. A rotating trial direction drives the
quotient graph; nested spaces drive the extremal-value marker. Numerical
models supply the data and are tested independently of their drawings.

The motivated revision uses questions at genuine points of investigation and
states definitions and deductions directly. It develops each new construction
from the problem that calls for it. Compression
begins with a trial input and the question of representable output; its formula
appears after the output leaves the plane. Residual columns appear as their
basis inputs are tested, and the block matrix follows the retained/escaping
output picture. Section endings identify the next unresolved question. The
recurring colors and the progress strip keep that exploration
connected to the larger approximation problem.

Phrase timing uses the completed narration for each visual build, so adding a
focus change does not create another TTS request. Normal `make video` now uses
the local `animation_cues.yaml` to align visual changes inside those passages. Slide 2 highlights A,
the candidate space and Q in turn. Slide 7 connects a rotating trial vector to
the quotient curve, shows the substitution steps, overlays the compressed curve,
and marks the two extrema. Displayed formulas use conventional mathematical
notation; speech-only pronunciation hints never change the slide source.
See the [production guide](../../presentation/README.md#phrase-timed-animations)
for dependencies and the timing override.

`make tts-experiment` separately compares long-passage conditioning strategies;
see the [experiment instructions](../../../README.md#long-passage-narration-experiments).
Rebuild narrated outputs to hear revised speech and see revised timing; earlier
generated videos and experiment comparisons preserve their original content.

The opening now states three true conclusions and previews the whole
approximation in one diagram before introducing the coordinate notation.
The closing summary returns to the identical claims with their equations.
Names such as lift, Ritz value and residual are attached to operations and
objects whose roles have already been explained. The block diagram labels
input columns and output rows; the transpose pairing is derived from A = A^T.
The error-vector question distinguishes zero trial projection from zero
original-coordinate entries. All four review pauses are five seconds.
The real/complex transpose convention belongs to Before the Series: Foundations,
whose stable deck ID remains `prereq-basics`.

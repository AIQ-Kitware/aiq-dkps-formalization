# Rayleigh–Ritz: trial spaces, compression, and residuals

Lecture **002749**, stable ID `rayleigh_ritz`, deck **`operators-rayleigh-ritz`**.
A standalone bridge from projections and Rayleigh quotients to the general
Davis–Kahan trial residual. The 26-scene lecture explains choosing a trial
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

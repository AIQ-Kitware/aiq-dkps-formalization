# Projection-valued measures

Lecture **002916**, stable ID `pvm`, deck **`operators-pvm`**.

A 22-scene standalone introduction: finite spectral windows and repeated
eigenvalues, the PVM laws, scalar energy measures, spectral integration,
continuous spectrum, strong convergence, and unbounded operator domains.
It closes with three symbolic/Lean pairs, an optional numerical bonus, and two
multiple-choice questions. The transcript provides local notation reminders;
projection and eigenvalue familiarity is useful. It does not prove the spectral
theorem.

From `visualizations/`:

```bash
make slides DECK=operators-pvm
make text DECK=operators-pvm
make video DECK=operators-pvm TTS_PROFILE=crall-math-dk-v2-breeze-tts2
```

The lecture is included in the indexed lecture batch. Restart an existing
library server to load the new Python deck registration. Generated artifacts
are ignored; their public basename begins `002916_operators-pvm`.

- [Transcript](../../../lectures/002916_pvm/lecture.md)
- [Sources and exact formal correspondence](../../../lectures/002916_pvm/sources.md)
- [Checked Lean examples](../../../lectures/002916_pvm/facts.lean)

From the repository root, after building the pinned Tau Ceti PVM module:

```bash
lake env lean visualizations/lectures/002916_pvm/facts.lean
```

`model.py` supplies the finite matrix illustration. Its numerical tests check
projection laws, repeated eigenvalue selection, and scalar energy masses.
Abstract PVM laws are accepted upstream; operator-to-PVM donor constructions
are identified separately in the source notes. Provenance records lecture
and transcript authorship independently of mathematical proof ancestry.

The 2026-11-06 revision connects the slide-to-slide argument in the spoken
narration and introduces the principal derivations in stages. The progress
strip names the lecture's own route. Rebuild slides and narration together;
old narrated videos retain their original speech and reveal timing.

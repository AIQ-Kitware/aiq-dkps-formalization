# Prerequisite lecture series

Six independent narrated lectures introduce the vocabulary for the matching
proof. Each has a motivating question, a little historical context, worked
explanations, a recap, and an answered self-check. Each introduces its own notation and includes a symbolic
facts card followed by one highlighted Lean statement per slide. A short numerical
bonus follows the core and Lean cards; the two study questions close the video. See the
[Lean companions](../../lectures/LEAN_FACTS.md). The prerequisite graph and
current teaching order are in [the lecture library](../../lectures/README.md),
generated from `lectures/index.yaml`.

| Lecture | Goal | Slides | Approximate speech |
| --- | --- | --- | --- |
| [Mathematics refresher](../../lectures/README.md#basics) | Identify which basic algebra, geometry, and calculus to revisit. | 20 | about 14 minutes |
| [Projections](../../lectures/README.md#projections) | Read projections, frames, blocks and transport. | 17 | about 12 minutes |
| [Thinking about I minus P](../../lectures/README.md#complementary_projection) | Distinguish complementary projection, geometric error, and motion displacement. | 16 | about 12 minutes |
| [Singular-value norms](../../lectures/README.md#singular_norms) | Compare movement costs and justify block additivity. | 18 | about 14 minutes |
| [Matrix exponential](../../lectures/README.md#matrix_exponential) | Build exact flows from matrix velocities. | 22 | about 17 minutes |
| [Variations](../../lectures/README.md#variations) | Construct legal motions and test stationarity. | 19 | about 16 minutes |

Times estimate speech at 140 words per minute, before slide pauses. The opening refresher reviews the vectors, inner products, matrix products, and
one-variable calculus assumed by the later lessons.
They introduce their specialized notation locally. The examples are finite and
real. They explain prerequisites and the first structural step of matching;
they do not replace the separate matching proof or extend its theorem scope.

## Build and narrate

From `visualizations/`:

```bash
make prerequisites             # all six, 1080p, HTML/PDF/handout and speech text
make prerequisites QUALITY=l   # draft all six
make slides DECK=prereq-projections
make text DECK=prereq-variations
```

Each deck exports a combined `presentation.txt`, individual slide text, build
text under `beats/`, and a manifest into `renders/<number>_<deck>-narration/`. Authored
scripts are linked above. Speech and animated builds use those same texts.

To make videos using the configured TTS service:

Select the `crall` profile for the cloned reference voice. The current model,
voice, delivery instruction, chunk limits, and postprocessing settings live in
[tts.toml](../../tts.toml); local endpoint overrides live in ignored `.env`.
The [production guide](../presentation/README.md) explains configuration and
caching. New Crall video variants are named `crall-breeze-tts2`.

```bash
make prerequisites-video TTS_PROFILE=crall SKIP_RENDER=1
make prerequisites-video TTS_PROFILE=kokoro SKIP_RENDER=1
```

Use `make lectures-video TTS_PROFILE=crall SKIP_RENDER=1` to include the
matching study and compact proof talk as well, following the complete YAML index.

This narrates all prerequisite lectures in YAML dependency order using existing
slides. Omit `SKIP_RENDER=1` to render the visuals first. Final videos are written
to `renders/<number>_<deck>.<narrator>.narrated.mp4`. To select another configured voice instead:

```bash
for deck in prereq-basics prereq-projections prereq-complementary-projection prereq-singular-norms prereq-matrix-exponential prereq-variations; do
    ./render_video.sh --deck "$deck" --skip-render --tts-profile kokoro || break
done
```

Change `--tts-profile` or the shared `tts.toml` settings to select another server
or voice. Private endpoints remain in the ignored `.env`. The six videos
are `renders/<number>_<deck>.<narrator>.narrated.mp4`; generation timings and cache behavior use
the existing shared pipeline. Building the lectures and their text does not
request speech.

Order numbers are folder keys, independent of deck IDs and code. Add an entry
with stable prerequisite IDs to the YAML, then preview and apply the organizer.
It preserves existing numbers when there is room. If dependencies change the
old order or a gap fills up, preview `--rebalance` to spread keys out again.

## Historical and mathematical sources

- Gale Young, [Matrix Approximations and Subspace Fitting (1937)](https://doi.org/10.1007/BF02287962): context for least-squares subspace fitting in lecture 1.
- Carl Eckart and Gale Young, [The Approximation of One Matrix by Another of Lower Rank (1936)](https://doi.org/10.1007/BF02288367): context for canonical matrix coordinates and approximation in lecture 2.
- Leonhard Euler, [Methodus inveniendi (1744), E65](https://scholarlycommons.pacific.edu/euler-works/65/): original work and archive for the calculus-of-variations context in the variations lecture.

- Arthur Cayley, [A Memoir on the Theory of Matrices (1858)](https://doi.org/10.1098/rstl.1858.0002), and Nicholas Higham, [The Scaling and Squaring Method for the Matrix Exponential Revisited (2005)](https://doi.org/10.1137/04061101X): matrix-algebra and computational context for the exponential lecture.

These are short contextual connections, not priority claims for all the modern
notions used in the lectures. The contemporary transport argument follows
`papers/dk_formalization_journal/formalization_enabled_extension.tex`.
The corresponding Lean stationarity and gradient results are in
`DavisKahan/FiniteDimensional/DirectRotation/SchattenRealStationarity.lean`;
the endpoint is in `RealNuclearMatching.lean` in that directory.

The projection and singular-value examples are in the respective `model.py`
files and checked by `tests/test_prerequisite_models.py`. Variations reuse
`learning/matching/model.py` and its existing matrix-identity and derivative
tests. These numerical checks support the pictures; Lean proofs remain the
source of formal certification.

After the series, start the [matching study](matching/README.md), especially
the transition from legal variations to invariant blocks. The complex-structure
and phase-projection block construction remains a natural next prerequisite
module; it is explained in the full matching study already.

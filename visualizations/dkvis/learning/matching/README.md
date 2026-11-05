# Real trace-norm matching

Two presentations of the same proof, with different audiences:

| Deck | Audience and purpose | Scenes | Transcript |
| --- | --- | --- | --- |
| `matching-proof` | A learner following the geometry, legal variations, and block construction in detail | [study.py](study.py), 40 proof scenes + local setup + numerical bonus + 2 review questions | [study.md](../../../lectures/README.md#matching_study) |
| `matching-proof-talk` | A mathematical audience following a compact proof | [talk.py](talk.py), 13 proof scenes + local setup + numerical bonus + 2 review questions | [proof-talk.md](../../../lectures/README.md#matching_proof) |

Both use [model.py](model.py) for the checked phase and matrix examples, and
`dkvis/novelty_math.py` for matching weights and the three-angle example.
Their presentation manifests remain in `dkvis/decks/`; this topic package owns
the content. The shared production code is in `dkvis/presentation/`.

## Learning goals and prerequisites

The learner should be able to explain why an unrestricted orthogonal minimizer
admits common small blocks, solve the one- and two-angle costs, recover both
matching inequalities, and pass the minimum values to the trace norm. A matching
then provides the exact value and an attaining transporter.

The study develops proof-specific projection, variation, gradient, and block
ideas. It assumes finite-dimensional linear algebra and basic calculus. The
proof talk additionally assumes principal angles, singular-value norms,
orthogonal spectral decompositions, the two-projection decomposition, and
compact variational arguments. See [the module catalog](../README.md) for
prerequisite material that can become smaller lessons.

## Mathematical sources

The exposition follows the matching theorem and its proof in
`papers/dk_formalization_journal/formalization_enabled_extension.tex`.
The Lean endpoint is `exists_minimizing_real_nuclear_transport_matching` in
`DavisKahan/FiniteDimensional/DirectRotation/RealNuclearMatching.lean`.
The supporting stationarity, gradient-spectrum, real decomposition, phase
rectangle, local optimization, and attainment files are in the same directory.

The theorem is finite dimensional and real, includes both determinant
components, repeated and right angles, and common directions. It gives an
unrestricted minimum and an attainer, not a classification of every minimizer.

## Build

From `visualizations/`:

```bash
make slides DECK=matching-proof-talk
make text DECK=matching-proof-talk
./render_video.sh --deck matching-proof-talk --skip-render --tts-profile kokoro
```

Substitute `matching-proof` for the detailed study. Public outputs now carry
`004000_` (study) or `005000_` (talk). Scene and speech caches stay stable;
the older `make matching`, `make matching-talk`, and
`render_matching_video.sh` commands are preserved. Speech settings stay in
`tts.toml` and private endpoints in the ignored `.env`.

The local setup cards restate the admissible maps, full displacement norm,
principal-angle labels, and meaning of a matching. The graph reduction itself
remains part of the proof; the blossom-based numerical implementation and
floating-point issues are a separate bonus after the proof. That bonus follows
[NetworkX's documented conventions](https://networkx.org/documentation/stable/reference/algorithms/generated/networkx.algorithms.matching.max_weight_matching.html).

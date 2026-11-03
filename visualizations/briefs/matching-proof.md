# Theorem 5: the finite real matching proof

This is a standalone study presentation, rather than an addition to the frozen
Kitware talk. The three matching scenes in `novelty-tour` and `comprehensive`
remain the short overview. This deck expands the proof so the reader can
reconstruct each inference and explain why it follows.

The mathematical source is Theorem 5 and its six-step proof in
[`paper.tex`](../../papers/dk_formalization_journal/paper.tex), with the longer
calculations in
[`matching_proof_study.tex`](../../papers/dk_formalization_journal/matching_proof_study.tex).
The Lean endpoint is
`exists_minimizing_real_nuclear_transport_matching` in
[`RealNuclearMatching.lean`](../../DavisKahan/FiniteDimensional/DirectRotation/RealNuclearMatching.lean).
The strict-exponent theorem used before taking the limit is in
[`RealMatchingAttainment.lean`](../../DavisKahan/FiniteDimensional/DirectRotation/RealMatchingAttainment.lean).

## Teaching structure

Every slide has an inference, a mathematical diagram or calculation, and a
short justification. The presenter notes carry the longer explanation, including
what has not yet been established. The narration follows the inference and
justification style of the study note. It is written to be understood as speech,
with formulas read out in words.

| Scenes | Purpose |
| --- | --- |
| M00–M05 | State the ambient optimization; construct singletons and pairs; explain graph weights and the two inequality directions. |
| M06–M07 | Step 1: use a differentiable power cost and choose a global minimizer by compactness. |
| M08–M13 | Step 2: construct feasible curves; derive the general trace pairing, including mixing directions; deduce zero diagonal source blocks of the gradient. |
| M14–M19 | Step 3: square the gradient; introduce complex coordinates on a positive level; split the phase projection; count real block dimensions; handle the zero level separately. |
| M20–M23 | Step 4: parametrize all four-dimensional competitors; compare the phase rectangle with an attainable edge; include both determinant classes. |
| M24–M26 | Step 5: use block replacement to recover a matching of the same minimum cost; remove zero-angle partners. |
| M27–M28 | Step 6: pass minimum values through a uniform limit; calculate the trace-norm pair weight. |
| M29–M31 | Recover an attaining transporter; solve the three-angle example; rehearse the proof without notes. |

The block diagrams for four real dimensions describe grouping and invariant
subspaces; they do not purport to draw four-dimensional geometry on a plane.
The phase-rectangle animation compares phase values; it does not assert a
monotone path of feasible matrices. Rotation-plane coordinates of the minimizer
are distinguished from source/complement coordinates throughout.

The numerical examples live in `dkvis/matching_math.py` and use the existing
three-angle graph in `dkvis/novelty_math.py`. Tests check the actual orthogonal
attainers, their displacement spectra, mixed-direction derivatives, and the
scalar comparison. They illustrate the Lean mathematics rather than replace it.

## Rendering and narration

Run `make matching` from `visualizations/` for the 35-scene deck, portable HTML,
PDF handout, and plain-text narration exports. `make matching-text` exports text
without rendering or requesting audio.

[`narration/matching-proof.md`](../narration/matching-proof.md) is the single
authored source of titles and presenter/speech text. The scene identifiers in
its headings must match the deck manifest in order. Each exported `.txt` file
contains one complete slide script. The exported manifest connects those texts
to the Manim slide JSON files.

[`render_matching_video.sh`](../render_matching_video.sh) renders the deck,
requests one MP3 per slide from the user's local Qwen speech API, holds the
final slide frame for the remaining speech, and assembles a chaptered H.264/AAC
video. `--skip-render` reuses current Manim outputs. Requests use whole slide
scripts because the user's model works better with longer inputs. Cached audio
is keyed by the script and speech settings, so a failed run can resume. See the
README for the exact defaults and output paths.

## Mathematical scope

The claim is the unrestricted finite-dimensional **real** minimum for
equal-rank source and target subspaces. The proof passes from `1<p<2` power
costs to the trace-norm endpoint. It supplies an exact matching reduction and
an attaining transporter. It does not classify every trace-norm minimizer,
assert infinite-dimensional matching, or infer the reduction from the
sine-theta theorem. The auxiliary complex coordinates are coordinates on the
original real space, rather than a change to a different optimization problem.

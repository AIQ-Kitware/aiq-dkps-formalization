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

The learner can follow algebra and a two-inequality proof but needs the concepts
behind the block argument explained. More examples do not repair unexplained
jargon. Introduce an operation in ordinary language, say why it is useful, then
name it and introduce its symbol. Keep a local definition visible when that
symbol is used. Do not make the learner memorize a glossary before watching.

Each slide has a motivating question, a takeaway, a diagram or calculation, and
an explanation of what the step buys us. The footer keeps the original question
and the current stage visible. Narration connects each new object to earlier
ones: E keeps a component just as P did, complex multiplication describes an
already constructed quarter-turn, and the local factorization reuses the
source-preserving pre-change construction.

The structural sequence explicitly explains “block,” “feasible,” “commute,”
“stationary,” “invariant,” “skew-symmetric,” and “phase.” The derivative shorthand
is written as rate(B), with its definition beside it. G is introduced as a
matrix collecting cost responses before being used to constrain a minimizer.

Four conceptual moves receive a consistent **Key idea** callout:

1. Construct legal directions first; their commutation with P follows.
2. Independent pieces must be preserved by W, P, and Q together.
3. Starting with an X-eigenvector, following Y to its partner and back closes
   the coordinate plane.
4. Pass minimum values through the limit; convergence of minimizers is not
   required.

| Scenes | Purpose |
| --- | --- |
| M00–M05 | State the problem; explain the meaning of a block; construct candidates; isolate the remaining question about many-way mixing. |
| M06–M07 | Step 1: use a differentiable power cost and choose a global minimizer by compactness. |
| M08–M13 | Step 2: construct source-preserving changes before introducing BP=PB; define P and stationarity; calculate cost-change rates; deduce zero diagonal response blocks; explain what common invariant pieces must do. |
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

Run `make matching` from `visualizations/` for the 40-scene deck, portable HTML,
PDF handout, and plain-text narration exports. `make matching-text` exports text
without rendering or requesting audio.

[`narration/matching-proof.md`](../narration/matching-proof.md) is the single
authored source of titles, motivating questions, local definitions, and
presenter/speech text. The scene identifiers must match the deck manifest in
order. A `<!-- beat -->` marker starts a new narrated build. `Why:` and `Recall:`
metadata appear on screen and are excluded from speech. Exports include complete
slide scripts and a `beats/` directory with one script per narrated build.

[`render_matching_video.sh`](../render_matching_video.sh) uses named server
profiles in `tts.toml`. The default remains the cloned `crall-math-dk` voice;
Kokoro, stock Breeze, and Qwen are alternatives. Private endpoint addresses and
this machine's profile selection belong in the ignored `.env` file. CLI flags
can override profiles and individual settings.

Each animation build retains its full spoken explanation. Speech is synthesized
in bounded sentence-aware pieces to avoid the observed 60-second server cutoff.
Capped responses are rejected and retried with shorter text, then the complete
pieces are joined losslessly. Audio caches distinguish request settings and
retain results across profile changes. `--refresh-audio` measures fresh synthesis.
`--scenes` produces a short preview for a model/voice comparison.

The final video has a chapter per complete slide. Each build starts with its
matching explanation and holds until speech ends. `--skip-render` checks exact
clip/note correspondence before synthesis. Measured TTS, cache, audio-join,
Manim, export, encoding, and concatenation timings are appended to
`renders/logs/render-timings.jsonl`; each video run also writes a settings/totals
summary. See the README for configuration, benchmarking, and output paths.

## Mathematical scope

The claim is the unrestricted finite-dimensional **real** minimum for
equal-rank source and target subspaces. The proof passes from `1<p<2` power
costs to the trace-norm endpoint. It supplies an exact matching reduction and
an attaining transporter. It does not classify every trace-norm minimizer,
assert infinite-dimensional matching, or infer the reduction from the
sine-theta theorem. The auxiliary complex coordinates are coordinates on the
original real space, rather than a change to a different optimization problem.

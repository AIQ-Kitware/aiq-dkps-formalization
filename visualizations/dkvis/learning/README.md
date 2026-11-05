# Learning modules

The goal is a library of explanations from which someone can learn the
mathematics, follow the proofs, and explain them independently. A module has
an explicit learning goal and prerequisites. Its scenes and spoken transcript
are maintained together. Mathematical claims point back to the manuscript
and Lean sources; pictures and numerical examples remain explanatory evidence.

## Current modules and source material

The [six-lecture prerequisite series](PREREQUISITES.md), the matching
topic, and [three accepted operator-foundation lectures](operators/README.md)
have complete, synchronized transcripts. Other rows identify existing
material to draw from when authoring more modules; those rows are not already
finished narrated lessons.

| Topic | A learner should be able to… | Prerequisites | Existing material |
| --- | --- | --- | --- |
| Mathematics refresher | Recognize the basic linear algebra, geometry, and calculus assumed later. | School algebra; review of previously encountered ideas | [Lecture 000010](basics/README.md) |
| Subspaces and projections | Translate between a subspace, its orthogonal projection, and adapted coordinates. | Inner products, linear maps | [Lecture 1](projections/README.md): complete narrated module |
| Complementary projection and error | Read I minus P, its restriction to trial vectors, and its relation to displacement. | Basic vectors; projections introduced locally | [Thinking about I minus P](complementary_projection/README.md): complete narrated module |
| Principal angles | Interpret the angle list, principal planes, and the directed sine operator. | Subspaces and projections; SVD | `slides_sine_theta.py`, `slides_sine_theta_3d.py`; matching study `M01PrincipalPlanes` |
| Singular-value norms | Compare full displacement costs in operator, trace, and Schatten norms. | Basic matrix algebra; the SVD is introduced | [Lecture 2](singular_norms/README.md): complete narrated module |
| Matrix exponential | Turn a constant matrix velocity into a flow; derive exact orthogonal and source-preserving motions. | Matrices, series, differentiation | [Matrix exponential](matrix_exponential/README.md): complete narrated module |
| Min-max and eigenvalue stability | Prove the variational characterization and derive Weyl stability. | Projections; operator norms | [Accepted operator foundations](operators/README.md) |
| Operator modulus and polar decomposition | Construct the canonical factor and distinguish its kernel convention. | Projections; singular values | [Accepted operator foundations](operators/README.md) |
| Residuals and spectral separation | Explain why residual size divided by certified separation bounds the subspace error. | Principal angles; spectra | `slides_sine_theta.py`, `sine_theta_story.py` |
| Sylvester equations and angle bounds | Follow the residual-to-Sylvester reduction and distinguish the four angle theorems. | Residuals and separation; operator norms | [Accepted operator foundations](operators/README.md); `slides_family.py`, `S09Sylvester` |
| Feasible variations and stationarity | Construct legal variations and derive the gradient compression equations. | Projections, norms, exponential, differentiation and trace | [Variations](variations/README.md): complete narrated module |
| Real and complex invariant blocks | Follow the complex-structure and phase-projection construction on a real space. | Spectral theorem; projections; stationarity | Matching study `M13TwoDecompositions`–`M19ZeroGradient` |
| The two-angle minimum | Reduce an unrestricted four-dimensional fiber to an attainable phase edge. | Principal coordinates; orthogonal spectra | Matching study `M20PairCoordinates`–`M23Determinants` |
| Real trace-norm matching | Recover both matching inequalities, the trace endpoint, and an attaining map. | The preceding three proof modules; singular-value norms | [Matching study and proof talk](matching/README.md): complete transcripts and Manim scenes |
| A printed claim and its repair | Verify the Proposition 4.4 counterexample and explain the norm-class repair. | Principal angles; singular-value norms | `slides_prop44.py`, `prop44.py` |
| Reading formal evidence | Distinguish a checked proposition, source correspondence, and a numerical illustration. | Familiarity with a theorem and its proof | `slides_process.py`, `slides_glossary.py` |

The catalog is a guide for authoring, not a new census or completion gate.
Start with the prerequisite series; it supplies much of the vocabulary needed
by the matching study. A dedicated common-invariant-blocks module is a natural
next topic; its proof is already explained in the matching study.
Unbounded operators, spectral measures, and operator ideals will need dedicated
modules before this library covers the full formalization's prerequisites.

## Authoring a module

Read [LECTURE_STYLE_RULES.md](../../LECTURE_STYLE_RULES.md) first. It is the
canonical record of the user's lecture preferences; this guide documents the
source layout, transcript format, and existing component APIs.

Each indexed lesson has a local setting and notation refresher, so viewers can
start there without decoding symbols in another video. Numerical considerations
are optional bonus slides after the core and Lean facts, before the study
questions. Lean facts appear one per card, with a repeated symbolic formula,
plain-language assumptions, JuliaMono syntax colors and a green library proof.

Keep importable code in a topic directory such as `dkvis/learning/matching/`:

```text
README.md          audience, learning goals, prerequisites, source references
model.py           numerical examples, with no Manim or TTS imports
study.py           scenes for a learner, if needed
talk.py            a distinct proof presentation, if needed
```

Names are descriptive, not compulsory. Use the smallest set of files the topic
needs. Reuse visual primitives from `dkvis/components/` and symbol roles from
`dkvis/notation.py`. A scene can appear in several decks. A study presentation
and a specialist talk may explain the same result differently.

Add a stable lecture ID and prerequisites to `lectures/index.yaml`. Run
`uv run python -m dkvis.lectures --apply` to allocate its numbered folder, and
author `lecture.md` there. The [lecture library](../../lectures/README.md)
documents previewing changes and explicitly rebalancing cramped order keys.
Numbers start at 001000 and normally advance by 1000; intermediate keys allow
insertions without renaming other lectures. YAML order breaks topological ties.

Register a `DeckSpec` in `dkvis/decks/`, supplying ordered scenes and
`narration=lecture_path(ID)` from `dkvis.lectures`. Register it in `decks/__init__.py`.
The shared pipeline discovers narrated decks from this field; adding a lesson
does not require editing the parser, video renderer, or Makefile.

A transcript section uses the actual scene class name:

```markdown
## ProjectionExample: What the projection preserves

Why: Connect the nearest-point picture to the projection identity.
Recall: $P$ is the orthogonal projection onto $K$.

Speak the explanation in ordinary language, spelling out mathematics for TTS.

<!-- beat -->

Explain the next meaningful animation here.
```

Section order must match the deck. `Why:` and `Recall:` are metadata, excluded
from speech. Each beat must be passed verbatim to `DeckSlide.say()` before its
animation. Load it with `read_deck_narration(deck_name)` from
`dkvis.presentation.narration`; see the matching scenes for working examples.
The video renderer checks every clip's embedded notes against the transcript
before it sends a speech request. Presenter notes on an older deck do not by
themselves make it a synchronized narrated module.

Build and review with the common commands documented in
[the visualization README](../../README.md). Inspect the animated explanation,
the complete final-frame handout, and the spoken text together. A learner should
know why each construction is introduced and what inference it permits; a
specialist talk can assume its declared prerequisites without teaching them.
Do not put authoring instructions or prerequisite checklists on the slides
unless they serve the audience's understanding.

## End-of-lecture study questions

Every indexed lecture has two questions in its source folder's `quiz.yaml`.
Author the question, three or four choices, a zero-based correct index, an
explanation, and ordinary-language `speak_question` / `speak_answer` text.
`think_seconds` controls the silent interval after the spoken choices (eight
seconds by default); viewers can also pause. The shared review scenes show the
question first, then highlight and explain the correct answer. The transcript
export includes these two scenes automatically. Keep their sections out of
`lecture.md`; append `quiz_uses()` to the deck's scene list.

## Model attribution

Each numbered lecture folder has `provenance.yaml`. Its `slides` and `transcript`
components record source-model attribution separately. The initial records cite
the first tracked source commit found with `git log --follow`, preserving that
commit's model name and any explicit uncertainty. They do not establish who
originated every imported line or make a mathematical-priority claim. Shared
rendering components retain their own Git history.

For subsequent content changes, append a `revisions` entry under the affected
component with `models`, `date`, `sources`, and `scope`. Use the actual model
identity, not an identity copied from an earlier agent. Preserve unknown model
variants as unknown. A rendering-only or library-server change does not make its
author the author of the existing slide or transcript content.

Exports snapshot these records with their generation timestamp and source Git
revision. Existing videos without a snapshot remain explicitly unrecorded;
the library displays current source attribution separately.

If the user later supplies an exact model identity for existing work, correct
the source attribution and record the confirmation, scope, and previous label.
The numbered lectures' correction is documented in
[AUTHORSHIP_CORRECTIONS.md](../../AUTHORSHIP_CORRECTIONS.md).
Never backfill an older video's generation record with today's source attribution.
If attribution changes, include the title scene when partially rendering a deck
so the visible robot/model credit is updated as well as the edited content.
For example, use `UPDATE_SCENES="CpTitle CpSplit"`. Partial rendering explicitly
selects scenes; it does not infer Python source dependencies.

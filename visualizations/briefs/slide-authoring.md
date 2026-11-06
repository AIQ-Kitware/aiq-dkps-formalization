# Slide implementation notes

For the user's teaching and narration requirements, read
[LECTURE_STYLE_RULES.md](../LECTURE_STYLE_RULES.md). This file covers the
repository's implementation conventions, not additional user style rules.

## Architectural rule

Reusable scene/component code and presentation composition are different
layers.

- `dkvis/components/` is for reusable visual primitives.
- `dkvis/learning/<topic>/` groups scenes and checked numerical examples.
- `lectures/` contains numbered folders with authored transcripts;
  `lectures/index.yaml` records stable IDs, prerequisites, and course membership.
  Resolve paths with `lecture_path(ID)`. Use the organizer for numbering;
  normal insertions use gaps, while `--rebalance` restores 1000-step spacing.
- `dkvis/decks/` chooses and orders components for a particular purpose.
- `DeckSpec.narration` selects the transcript; `dkvis/presentation/` owns the
  shared rendering, speech, video, and timing pipeline.
- checked numerical models have no rendering or TTS dependencies.
- render/demo code remains separate from both models and deck composition.

Do not put Friday-specific ordering, optionality or backup status on a reusable
scene class.  `SlideUse.depth` in a deck manifest owns that metadata.  Existing
scene-level `depth` values are compatibility fallbacks for renders that do not
come through a manifest.

## Migration strategy

1. Keep the reference decks rendering while reorganizing.
2. Extract cross-module primitives before moving large groups of scenes.
3. Move scenes by concept, preserving scene class names during the migration.
4. Render after each conceptual move; do not infer visual correctness from
   Python source.
5. When two explanations are worth testing, keep descriptively named
   alternatives and choose between them in deck manifests.

Avoid generic framework work that does not make composition, explanation or
render reliability better.

Use the module layout and transcript format in `dkvis/learning/README.md`.
New topics must use the common pipeline rather than clone the matching video
or narration tools. Existing decks without synchronized transcripts remain
slide presentations until a transcript is authored and reviewed.

## Animation rule

Animation should encode information.  Useful cases include perturbation,
rotation, gap closure, decomposition, correspondence and before/after
comparison.  If the audience is only waiting for already-known static content
to fade in, show the content immediately.

## Evidence-bearing content

Do not alter checked numerical models merely to improve a picture.  Add a new
specialization to the model layer and test it if a component needs new numbers.
Keep claims tied to the Lean/source evidence already recorded in the repository.


## Components used by indexed lectures

- Covers use `LessonTitle`; `llm_credit.py` reads the robot/model disclosure
  from the lecture's `provenance.yaml`. Source attribution is maintained as
  described in `dkvis/learning/README.md`; the frozen reference talk is separate.
- `LessonSlide.example = True` supplies the **Example:** title and **General
  tool:** takeaway marker. Keep the symbolic rule in the existing content region.
- `LessonLean.symbolic_facts` supplies paired labels and formulas; `fact_index`
  selects the checked example from `facts.lean`. Keep the full Lean imports and
  context in that companion file. The shared JuliaMono/Lean-4 renderer supplies
  syntax colors and the library-proof highlight.
- Computation bonus scenes use `bonus=True` and manifest `SlideUse.depth="*"`.
  Current decks place them after the mathematical/Lean facts and before the quiz.
- Flow illustrations use amber for the first coordinate or scalar output, blue
  for the second coordinate, and violet for time, as implemented in the current
  matrix-exponential scenes and shared palette.

The transcript section/beat contract and quiz format are documented in the
[authoring guide](../dkvis/learning/README.md). Keep that guide as the single
technical reference for new modules.

## Editing and rendering one scene

Keep the scene and its narration synchronized and use
`make video DECK=... UPDATE_SCENES="SceneName" TTS_PROFILE=...`. This renders the
selected scene and assembles every chapter, reusing other encoded segments by
input content. `--scenes` retains its selected-chapter preview meaning.
Shared-style or scene-order changes require a full visual render. If model
attribution changes, include the cover in the selected scenes so its visible
credit stays current. See the [production guide](../dkvis/presentation/README.md)
for cache behavior and generation records.

## Spoken continuity and staged results

`Why:` and `Recall:` are metadata; they are excluded from synthesized speech.
Put the reasoning needed to cross a slide boundary in the authored speech.
Use additional transcript beats when a key derivation needs a setup, a result,
and an interpretation; reveal the corresponding scene content after each
`beat()`. Keep earlier parts visible so the final build still works as a
complete handout. `LessonSlide.stage_labels` can name a lecture's own route;
the default labels remain available for existing compositions.

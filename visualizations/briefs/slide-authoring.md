# Slide authoring and component rules

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

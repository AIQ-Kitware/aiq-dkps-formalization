# Slide authoring and component rules

## Architectural rule

Reusable scene/component code and presentation composition are different
layers.

- `dkvis/components/` is for reusable visual primitives and, incrementally,
  conceptual scene groups.
- `dkvis/decks/` chooses and orders components for a particular purpose.
- checked numerical models remain outside the presentation layer.
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

## Animation rule

Animation should encode information.  Useful cases include perturbation,
rotation, gap closure, decomposition, correspondence and before/after
comparison.  If the audience is only waiting for already-known static content
to fade in, show the content immediately.

## Evidence-bearing content

Do not alter checked numerical models merely to improve a picture.  Add a new
specialization to the model layer and test it if a component needs new numbers.
Keep claims tied to the Lean/source evidence already recorded in the repository.

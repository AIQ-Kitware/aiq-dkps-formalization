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


## Examples and the reusable tool

Label worked cases visibly as examples. In prerequisite lessons, set
`LessonSlide.example = True` to prefix the title with **Example:** and mark the
colored takeaway as **General tool:**. Use that takeaway to state the rule the
case illustrates, with any essential hypothesis. Distinguish particular numbers
or matrices from the general statement. Where the body has room, box the
symbolic rule in the existing content column; otherwise emphasize the rule
without adding another panel. Keep the example values and animation visible.


On a Lean companion slide, repeat the symbolic statement beside the code that
proves it. Match the order of the preceding mathematical facts card. Keep common
assumptions visible, make the notation correspondence explicit, and wrap code
lines in the checked companion file rather than shrinking long lines until they
are unreadable. `LessonLean.symbolic_facts` supplies the paired labels/formulas;
the code is read from the actual examples in `facts.lean`.


## Mathematical meaning and numerical computation

Give both the mathematical object and its motivating interpretation. For the
matrix exponential, distinguish the series-defined family `exp(t A)` from a
trajectory obtained by applying that map to an initial vector. In prerequisite
flow illustrations, reuse amber for the first coordinate (or scalar output),
blue for the second coordinate, and violet for time. Label the quantities as well
as coloring them. Use the same coordinate colors on later plane diagrams.

When a topic has a non-obvious numerical side, include one short computation
coda near the end, before the mathematical-facts/Lean closing pair. Explain the
choice of algorithm and desired output, cite primary papers or official library
documentation, and distinguish a teaching calculation from production numerical
practice. Avoid claims that one algorithm is universally best.

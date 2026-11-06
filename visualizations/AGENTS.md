# Agent instructions for `visualizations/`

The visualizations are reusable Manim/VTK scenes composed into several decks.
Shared slide/transcript/TTS/video production lives in `dkvis/presentation/`.
Learning scenes and models belong in `dkvis/learning/<topic>/`; authored lecture
text lives in numbered `lectures/` folders. `lectures/index.yaml` owns stable
lecture IDs, prerequisites and course membership; `python -m dkvis.lectures`
previews NetworkX topological ordering, and `--apply` organizes folders.
Use `lecture_path(ID)` in deck manifests rather than hard-coding numbered paths.
Ordering keys must not become Python package names or deck identities. Read
`dkvis/learning/README.md` for the module contract and current catalog.
`DeckSpec.narration` selects an authored transcript. Do not add topic names,
scene-name prefixes, or transcript paths to the shared production tools.
Keep legacy scene files where they are until a conceptual migration is useful.
Preserve presentation content and ordering during organization-only work.

The completed presentation is now named `kitware-talk`; **do not change its
scene order or change a scene just to improve the new `comprehensive` deck**.
The `comprehensive` deck is the editable long presentation and should include
every distinct source-grounded mathematical visualization in a coherent order.
The older reference decks and `study` continue as regression/learning surfaces.

For substantial slide work, also read `briefs/slide-authoring.md` and
`dkvis/components/README.md`. Read the relevant deck brief when editing that
deck; the frozen Kitware, comprehensive, and deep-study briefs have distinct
scopes.

The old `sine-theta-short`, part decks and `sine-theta-full` are reference
compositions. Preserve their behavior. Use `dkvis/decks/comprehensive.py` to
reorganize the long presentation, rather than modifying the frozen Kitware talk.

Render and inspect slides before claiming a visual improvement. Use draft
quality while iterating. Every scene's final build must contain the complete
intended static content because the handout generator captures final builds.

Presentation-specific `*` / `**` depth belongs in the deck manifest.  Existing
class-level `depth` attributes are compatibility fallbacks and should disappear
as scenes are migrated.

The checked numerical models and their tests are evidence-bearing code.  Do not
change them to make a picture prettier.  If a new visualization needs a new
specialization, implement and test it in the model layer first.

Prefer small conceptual migrations over a mechanical rename of the whole tree.
For future visual work, use short incremental passes:

1. list and render the affected scenes at draft quality;
2. inspect them for clipping, unreadable math, duplicated material and color drift;
3. improve reusable scenes outside `kitware-talk` (or create alternatives);
4. render again before claiming a visual improvement;
5. rebuild `comprehensive` and its standalone HTML when the sequence is ready.

Do not write brittle tests asserting text labels, slide captions, or paragraphs.
Tests should cover numerical model behavior, deck integrity, and actual helper
behavior. Inspect rendered outputs for visual correctness.

## Novelty tour

Before editing `novelty-tour`, read [its brief](briefs/novelty-tour.md) for the
source/target color crosswalk and exact verified scope. Preserve the distinction
between this deck's transport notation and the older sine-theta notation.

## Canonical sine-theta notation

Do not reintroduce `U`/`V` as aliases for the ranges of the sine-theta frames.
The core exposition names the objects the theorem operates on directly:

- `Ahat`: operator under study in the general theorem; Lean/source names this `A`;
- `E0, A0`: trial frame and trial-coordinate operator;
- `F0`: exact wanted frame; `F1, Lambda1`: exact unwanted frame/block;
- `R = Ahat E0 - E0 A0`;
- `Theta0(E0,F0)` / `sinTheta0(E0,F0)`: angles/error between their ranges;
- `delta`: certified spectral separation, not a generic eigengap.

In perturbation slides only, keep `A` permanently equal to the original operator
and write `Ahat = A + H`.  Choose the trial pair from original `A`, so
`A E0 = E0 A0`, `R = H E0`, and `||R|| <= ||H||`.  Use `g` for an original
eigengap of `A`; never silently identify it with `delta`.  `U,V` may still be
used when they are genuinely the notation of another statement, such as
Proposition 4.4.

## Lecture authoring

Read the [project vision and history plan](docs/planning/lecture-project-vision-and-history.md)
when planning lecture coverage. The north star is understanding the full
Davis–Kahan paper, the repository's extensions, and their prerequisites. Use
Lean to progressively validate the learning map; do not block obvious useful
lecture drafts on a complete formal dependency tree. Keep teaching prerequisites,
proof dependencies, and historical influence distinct.

Before writing or revising a lecture, read
[LECTURE_STYLE_RULES.md](LECTURE_STYLE_RULES.md). It records the user's directly
expressed teaching and narration preferences. Keep those rules there rather than
copying or extending them in multiple instruction files. Technical mechanics
belong in [the authoring guide](dkvis/learning/README.md) and
[the implementation notes](briefs/slide-authoring.md).

## Lecture model provenance

Maintain the lecture's `provenance.yaml` when changing content, following the
[model attribution instructions](dkvis/learning/README.md#model-attribution).
They specify the separate slide/transcript revision records, runtime model
identity, and generation-time snapshots. Include the cover when attribution
changes so its visible model credit is refreshed; see the
[partial-update instructions](README.md#updating-one-scene).

## External illustrations

Use images with on-slide attribution. Commit selection/access logic and source
records, not downloaded images. Keep images and their license/provenance
snapshots in the portable ignored asset store, as described in
[the asset guide](docs/EXTERNAL_ASSETS.md). Reuse the attributed-image component
for portraits. Retain original creator credit separately from lecture/model
authorship; do not silently substitute another image if access fails.

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

Read these before substantial slide work:

- `briefs/kitware-talk.md`
- `briefs/comprehensive.md`
- `briefs/deep-study.md`
- `briefs/slide-authoring.md`
- `dkvis/components/README.md`

The old `sine-theta-short`, part decks and `sine-theta-full` are reference
compositions. Preserve their behavior. Use `dkvis/decks/comprehensive.py` to
reorganize the long presentation, rather than modifying the frozen Kitware talk.

Render and inspect slides before claiming a visual improvement.  Use draft
quality while iterating.  Static scenes should appear complete without
purposeless fade-in sequences.  Animation should communicate a mathematical or
conceptual transition.  Every scene's final build must contain the complete
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
## New spectral transport deck: semantic color crosswalk

`novelty-tour` is a separate presentation using the manuscript's transport
notation: `U` is the **source**, colored amber (`TRIAL`), and `V` is the
**target**, colored blue (`WANTED`). Its LaTeX uses `\sym{Usource}` and
`\sym{Vtarget}`, and its projection symbols use `ProjSource`/`ProjTarget`.
Do not replace these with historical `\sym{U}`/`\sym{V}`: in the older
sine-theta slides those keys deliberately mean exact wanted `U` (blue) and
trial `V` (amber). Keep both semantic namespaces and the global palette.
Principal angles and optimal phases are magenta (`SINE`), thresholds violet
(`GAP`), and the smoothed objective/optimal cost steel (`CURRENT`).

`novelty-tour` is anchored to the Lean-completed exact finite complex
Charbonnier optimizer, closed uniqueness cutoff, mixed-angle quartic growth,
critical-planar failure of quadratic growth, and commuting-unitary correction.
The scalar worked examples come from `dkvis/novelty_math.py` and have
numeric regression tests. The higher-rank finite complex Schatten `1<p<2`
minimum, complete all-angle optimizer classification, exact simple-angle
counts and no-nonglobal-local-minima theorem **are now Lean-verified** at
source snapshot `427169ce`; include them as certified mathematical results.
Its optimizer Grassmannian decomposition is an algebraic set equivalence,
not a verified topological or smooth parametrization. The unrestricted finite-dimensional real matching theorem for
`1 <= p < 2` is now verified, including the nuclear endpoint. The complex
nuclear minimum, real/complex even-multiplicity equality criterion, real
canonical-value criterion, and exact nearest nuclear correction are also
proved. They are visualized in `N08NuclearMatching`, `N08NuclearParity`,
`N08NuclearCanonical`, and `N08NuclearCorrection`. Do not infer a full
`p=1` optimizer classification, endpoint local-to-global theorem, the
strict-exponent real/complex parity conjecture, or infinite-dimensional
ideal theory from these claims. Unproved sorted-sum formulas, uniform
field-gap estimates and historical-priority claims must remain qualified.

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

## Standalone, evergreen narration

Transcripts are lectures for a new viewer, never replies to the author or to a
prompt. Do not include conversational carryover such as “your displacement
intuition is useful”, “as you asked”, or “we fixed the missing explanation”.
State the mathematical idea directly. Addressing the audience with an actual
study question is fine; assuming they participated in an earlier conversation
is not.

Motivate each topic through the mathematical question it answers. Define local
notation and explain the reasoning within the lecture's stated prerequisites.
Do not assume the viewer is reading this manuscript or watching a particular
proof. Keep reusable concepts and summaries useful beyond this project.
Matching and Davis–Kahan are welcome as explicitly introduced applications;
avoid unexplained references to “the proof”, “the paper”, or an earlier request.
Review spoken text, slide motivations, recaps, and study questions for these
issues when editing. Preserve mathematical hypotheses and source attribution.

## Lecture model provenance

Each indexed lecture has `provenance.yaml` beside its transcript. Maintain slide
and transcript attribution separately. When changing their content, append a
revision with the exact runtime model identification (and variant/config when
known), date, affected source paths, and a short scope description. Preserve the
initial Git-backed attribution; do not replace it with the latest editor. Use
`revisions` entries with a `models` list under the affected component. Shared
rendering infrastructure edits are not authorship of the lecture content.
Unknown models or variants must stay explicitly unknown. Generation metadata
snapshots source attribution for future exports; never backfill a historical
video with today's attribution as if it were recorded when that video was made.

Lecture covers display the model credits from this metadata. If attribution
changes, include the cover scene in a partial render as well as the edited
content scene (for example `UPDATE_SCENES="CpTitle CpSplit"`), so the visible
badge does not retain the previous attribution. Partial rendering selects
scenes explicitly; it is not an automatic Python/source dependency analyzer.

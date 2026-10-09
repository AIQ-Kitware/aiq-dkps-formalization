# Agent instructions for `visualizations/`

The visualizations are reusable Manim/VTK scenes composed into several decks.
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

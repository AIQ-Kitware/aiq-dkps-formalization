# Agent instructions for `visualizations/`

The immediate goal is not generic cleanup.  It is to make the visualizations a
reusable component library from which multiple explanations can be composed,
then improve two presentations: `friday` and `study`.

Read these before substantial slide work:

- `briefs/friday-talk.md`
- `briefs/deep-study.md`
- `briefs/slide-authoring.md`
- `dkvis/components/README.md`

The old `sine-theta-short`, part decks and `sine-theta-full` are reference
compositions.  Preserve their behavior while migrating scene implementations.
Do not improve them in place when the goal is to test a different narrative;
create/change a manifest in `dkvis/decks/` instead.

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
A good next sequence is:

1. render the reference, `friday` and `study` manifests at draft quality;
2. inspect the resulting decks and record narrative/visual problems;
3. move one conceptual group (for example sine-theta geometry) behind
   `dkvis/components/`, keeping class names stable;
4. render again and compare;
5. then begin creating alternative explanatory components where the current
   material is weak.

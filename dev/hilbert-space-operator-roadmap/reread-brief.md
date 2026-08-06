# Reread brief — HilbertSpaceOperatorTheory READMEs

Working note. Not part of the PR (main repo, not the submodule).

**The reread happened, and round 4 landed as `c47ecd7`.** What remains useful here is the
settled-decisions record below — chiefly *Deliberately KEPT* and *Facts established* — which
exists so a fifth round does not re-find them. Everything in *Open* still needs a decision.

## Why this exists

Each round of prose cutting *introduced* the thing the next round found:

| round | cut | introduced |
|---|---|---|
| 1 | reviewer asides, tone words | the "bar for done" paragraph, ×6 |
| 2 | "bar for done" | `not only X`, ×4 |
| 3 | `not only` | `Each object should … its basic API`, ×5 → 6 |
| 4 | that template, and the prose about the prose | — checked; see below |

The cause is method, not judgment: editing against grep hits and diff hunks cannot show six
file openings at once, so the same sentence gets written six times unnoticed. **A cutting
pass must end with a sequential whole-file read.** That is the one thing greps cannot do.

Round 4 also proved the *other* half of the failure: three of the four defects it repaired
were grammar breaks left by rounds 1–3, where the cut word was carrying the sentence's verb
or its meaning. `genuine` → `holds` inverted a claim; `worth` and one relative clause each
took a subject and verb with them.

## What round 4 did

- Repaired four shipped defects (the three above plus an orphaned bold).
- Deleted the fourth-generation template: `Each object should … basic API` (6/6 → 1) and
  `Not in Mathlib:` (6/6 → 0; it restated the heading two lines above it).
- Cut prose whose subject is the document: the `says so` family, `Why this is a milestone`,
  `This debt is incurred knowingly`, `A specification omitting this would hide …`,
  `Structuring the proof that way is part of the milestone`, and four standalone
  `This is what lets/needs` justifications.
- Cut one duplicated dependency list, one restated pair of missing lemmas, three
  non-duplication assertions where one suffices, and the `most consequential absence`
  superlative.
- Rewrapped the ragged lines rounds 1–3 left at their edit sites.

Verification that ran after, and should run after any future pass:

- no sentence over 45 chars in more than one file (except the house Acknowledgements line
  and a shared reference entry);
- the six file openings printed side by side and read as distinct;
- no broken relative link; no line over 100 cols except those carrying long URLs;
- `git status` shows READMEs only — no `Suggested.lean` touched.

## Settled — do not reopen

### Absolute (user directives)

- **`sorry` in `Suggested.lean` is the intended state.** Never report one as a finding, never
  fill one. The roadmap is an API sketch: theorem signatures, not proofs.
- **No self-justifying notes.** Never add "we deliberately scoped X out" or similar after a
  cut. Quote: *"I hate it. Reviewers hate it. It is bloat."*
- **No reviewer-directed prose** ("a reviewer should check…", "if a reviewer wants it…").
  State the claim or delete it; do not state the null claim.
- **No "before implementing, search the Zulip" instructions.** Due diligence is done and does
  not belong in the document.
- **No scope-boundary / "coordinate with the author" sections.**
- **Provenance and credit are wanted** — in Acknowledgements, not as process disclaimers.
- **Em-dashes are fine.** The user likes them. Do not remove them and do not reintroduce ones
  already cut.
- **Links are wanted** where they make sense. DKPS → `https://github.com/AIQ-Kitware/aiq-dkps-formalization`
- Work happens in `submodules/TauCetiRoadmap`. `ForTauCetiRoadmap` is a staging ground and is
  not the deliverable.

### Measured against the 27 accepted roadmaps (don't re-measure)

- House section order: Standing conventions → What Mathlib already has (consume) → What is
  missing (build here) → The build, in layers → Worked examples (acceptance criteria) →
  Ordering → References → Acknowledgements.
- "bar for done": **0/27**. Ours, not house style. Deleted.
- Submission mechanics / PR sizing: **0/27**. Deleted. Do not re-add.
- Acknowledgements: 11/27 have one; house form is short — name the source, link it, license,
  stop. Ours now reads: *"An Apache-2.0 implementation … exists in [AIQ DKPS formalization]
  (Kitware, Inc.) … The public API and proof structure may change during integration."*
- The word "provenance": 0/27 use it in prose.

### Phrases cut to zero — do not reintroduce

`honest` · `genuine`/`genuinely` · `load-bearing` · `not only`/`not just` · `worth` ·
`actually` · `precisely` · `cleanly` · `said out loud` · `nobody` · `hides` ·
`the substance`/`the hinge`/`the headline`/`the payoff` · `buys`/`is not paying`/`that costs` ·
"not to race to a handful of named theorems" · "Discharge these alongside the layers" ·
"None of the following is in Mathlib; this roadmap builds it" · "Used rather than rebuilt" ·
"Three gaps this roadmap fills" · "Consume these and connect to them" ·
"establishes feasibility … specifies the desired mathematics intrinsically"

### Deliberately KEPT — do not "find" these

These were examined and kept on purpose. Flagging them again is churn.

- **`and nothing else` (×4)** — states exact dependency closure (`Part D consumes Part C and
  nothing else`). A specification, not emphasis.
- **`not merely of gauges` / `not merely weak` / `not merely asserted`** — dropping the
  qualifier inverts the claim ("an equality of families, not of gauges" is false).
- **`silently strengthened` / `silently dropped`** — names the failure mode being guarded
  against.
- **`the engine` in `MajorizationAndAngles`** — a term that file defines in Standing
  conventions and uses throughout.
- **Real mathematical contrasts** — square vs rectangular; finite vs infinite dimension;
  one-sided vs two-sided gaps; statement ownership vs proof dependency; the targeted vs
  excluded halves of Calkin. The cut targets narration *around* a distinction, never the
  distinction.
- **`rather than`** (~48 total) — mostly legitimate. Not a target.
- **`MatrixSpectralStatistics` intro, the four-Part arc** — reviewed and kept; each sentence
  states actual mathematics (a rank-≤`d` PSD matrix *is* a Gram matrix of `n` points in `𝕜^d`).
- **The one-parameter-semigroups ownership paragraph in the index** — long, but carries five
  distinct items including the resolvent-set reason and the Stone/`C₀`-group coordination.

### Facts established — do not re-derive

- The TauCeti pin was 683 commits stale; all "already ships" checks were re-run against
  current `main`. Nothing this family proposes has landed upstream.
- The `OneParameterUnitaryGroup` ↔ `StronglyContinuousSemigroup` bridge **exists**:
  `toSemigroup` / `generator_toSemigroup` in `SemigroupBridge.lean`. (An earlier claim that it
  did not was wrong and is corrected in the roadmap.)
- `ContinuousLinearMap.modulus` is the **rectangular** construction (`E →L[ℂ] F`);
  `LinearMap.operatorAbs` is the **square** one. The name is an open review question.
- `UnboundedSinThetaProblem` was cut from the roadmap — not general reusable mathematics.
- TauCeti never extends root Mathlib namespaces (Mathlib will not take AI-authored code); it
  mirrors them under `namespace TauCeti`. Migration TODO for `ForTauCeti` (~39 files / ~390
  declarations) is recorded in `ForTauCeti/README.md`.

## Open

1. **`deliberately`** — 9 in the READMEs after round 5 (12 before round 4), plus 5 in
   `Suggested.lean` files. Awaiting the user's call. (An earlier count of 43 was wrong.)
   Do not act unilaterally.
2. Open items in `considerations.md`: the `→L`/`→ₗ` bridge for `IsPartialIsometry`; the
   `operatorAbs`/`modulus` naming; `OperatorIdealFamily`'s ℂ-only scalars and universe pin.
3. Examined and left alone through round 5 — flag, do not cut unilaterally:
   - `The reason is not brevity:` (Foundations, the Moore–Penrose predicate) — negation
     then assertion, but the assertion is real;
   - `The arbitrary basis is the point:` (Majorization, Hoffman–Wielandt);
   - `is specified here intrinsically` (Perturbation, Part A) — residue of a cut phrase;
   - `The approximants are public and named because … not about a limit appearing from
     nowhere` (SelfAdjoint, Part E);
   - `**Why "Hilbert-space" and not "finite-dimensional"**` (Foundations) — reads as
     title-justification, but its content is a real generality decision;
   - `differing on three axes` (Foundations, Part B) above a four-row table.
4. **The shared Acknowledgements sentence**, *"The public API and proof structure may change
   during integration"*, is in all six children plus the index — noted in review, no
   instruction given. It is the deliberate house form (11/27 accepted roadmaps carry an
   Acknowledgements; the form is short — name the source, link it, license, stop). Left in
   place. If it should be cut or varied, that is a decision, not an oversight.

## Settled by round 4 — do not reopen

- **The criterion sentence.** Deleted in `MajorizationAndAngles`, `SelfAdjointSpectralTheory`
  and `MatrixSpectralStatistics`; reduced to its content (no `Each object should` opener) in
  `OperatorIdeals`; kept in `HilbertSpaceOperatorFoundations` (names specific API, and
  "defined once at its natural generality" is that file's thesis) and in
  `SpectralSubspacePerturbation` (a different sentence, naming real generalities).
- **`Not in Mathlib:`** — gone from all six. The heading `## What is missing (build here)`
  carries it. Do not re-add.
- The `OperatorIdeals` Acknowledgements design-history paragraph ("Two design decisions …")
  was deleted rather than repaired. If provenance value is wanted there, that is a decision
  to revisit deliberately, not an oversight.

## Method rules, learned the hard way

- **Never bulk-regex prose.** Boundary patterns cannot distinguish a clause-final contrast
  from one inside parentheses or between paired commas. This destroyed sentences once
  (`(\`unitaryGroup\`, not the invertibles) because…` → `(\`unitaryGroup\`.`) and was reverted.
  Exact full-line strings with a `count == 1` assertion are safe; anything else is not.
- **After deleting a single word, read the whole sentence.** `states cleanly with` →
  `states with` was a grammar break caught only on the diff read.
- **After deleting a paragraph, grep for terms it introduced** and check they are still
  defined before first use.
- **Before committing, put the six files' corresponding sentences side by side** and check
  for a regenerated template. This is the check that would have caught all three rounds.

## Verify before every push

```
# from submodules/TauCetiRoadmap
git status --porcelain | grep -v 'README.md$'     # expect empty — READMEs only
# 0 broken relative links; no added line >100 cols (URLs exempt)
```

Push: submodule → `Erotemic hilbert-space-operator-theory`; then bump the pointer in the
parent and push → `origin main`. Always commit and push; do not end by asking.

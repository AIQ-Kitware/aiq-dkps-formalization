# Reread brief — HilbertSpaceOperatorTheory READMEs

Working note for the post-compaction full read. Not part of the PR (main repo, not the
submodule). Delete when the reread is done.

## Why this exists

Three rounds of prose cutting have each *introduced* the thing the next round found:

| round | cut | introduced |
|---|---|---|
| 1 | reviewer asides, tone words | the "bar for done" paragraph, ×6 |
| 2 | "bar for done" | `not only X`, ×4 |
| 3 | `not only` | `Each object should … its basic API`, ×5 |

The cause is method, not judgment: editing against grep hits and diff hunks cannot show six
file openings at once, so the same sentence gets written six times unnoticed. **The reread
must be sequential and whole-file.** Its purpose is to catch document-level problems, which
is the one thing the greps cannot do.

## Scope of the reread

Read all six child READMEs and the family index end to end. Produce **findings, not edits**,
unless told otherwise. Look for:

1. Regenerated templates — near-identical sentences across files (see the open question below).
2. Broken antecedents — a term defined in a paragraph that was deleted. This happened once:
   removing Majorization's intro orphaned "Suggested home: … for the engine".
3. Sections that no longer read correctly after their lead-in line was removed, especially
   *Worked examples (acceptance criteria)*.
4. Sentence fragments and grammar breaks from single-word deletions.
5. Content that is now a truism — a sentence left saying nothing after its substance was cut.

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

## Open — decide during the reread

1. **`deliberately`, 12 occurrences.** Awaiting the user's call. (An earlier count of 43 was
   wrong.) Do not act unilaterally.
2. **The six criterion sentences.** The question is *whether they should exist*, not what they
   should say — that has been answered wrong three times. Current recommendation:
   - **delete** in `SelfAdjointSpectralTheory` and `MatrixSpectralStatistics` — both have
     decayed to truisms, and each file's *What is missing* already lists the deliverables;
   - **keep** in `HilbertSpaceOperatorFoundations`, `MajorizationAndAngles`, `OperatorIdeals`
     — these name specific API (closure/composition laws; invariances and variational
     characterizations; unconditional interface laws);
   - `SpectralSubspacePerturbation`'s is a different sentence naming real generalities — keep.
3. Open items in `considerations.md`: the `→L`/`→ₗ` bridge for `IsPartialIsometry`; the
   `operatorAbs`/`modulus` naming; `OperatorIdealFamily`'s ℂ-only scalars and universe pin.

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

# Honesty census, 2026-08-31

A name is dishonest when a competent reader who trusts it draws a false
conclusion about scope, status, or content.  This census surveys the repository
for that, at HEAD `d92dd95e`, and separates what was measured from what is a
judgement call.

Method: every declaration name in `DavisKahan/**` and `ForTauCeti/**` (10 741),
every module path, every `dev/` and `docs/` document (142 Markdown files with
their reference counts and last-touch dates), and the gate suite with the data
files each gate reads.

## Summary

| # | finding | count | disposition |
| --- | --- | --- | --- |
| 1 | `Experimental/` is an empty shell with two gates guarding it | 7 artifacts | remove |
| 2 | Module paths carrying `Headline`, `WholeSpace`, `Legacy` | 8 modules | renamed |
| 2b | Module paths claiming completeness: `Full*` | 4 modules | renamed |
| 3 | Staging roots that outlived their staging | 2 modules | removed |
| 4 | Historical documents kept as forwarding tombstones | 9 documents | remove |
| 5 | Finished-campaign plans still named as plans | 14 documents | remove |
| 6 | Superseded audit sweeps under `dev/audit/` | 18 documents | remove |
| 7 | Unqualified names bound to the complex statement | 66 of 113 candidates | renamed `_complex` |
| 8 | `hidden-foundations` reports 0 findings over a deleted tree | 3 artifacts | retired |
| 9 | The audit corpus is a July 2026 review sweep nothing reads | 21 documents | removed |

Not a finding: declaration names containing `generic`, `complete`, `final`,
`full` or `exact` are overwhelmingly *domain vocabulary*, not vagueness.
`genericCosineBlock` is the generic part of a subspace pair (Halmos);
`completeSpace_*` is `CompleteSpace`; `polarPartial_final_surjective` is the
final space of a partial isometry; `fullDisplacement` and `ExactSinTheta` are
Davis--Kahan's own words for the full displacement and the exact subspace.  The
scan flagged 176 of these and every one that was checked was honest.  Only the
Section 2 uses of `headline`/`wholeSpace`/bare `exact` were route-not-content,
and those were renamed on 2026-08-30.

Also not a finding: Lean prose contains no completion claims.  Every one of the
25 matches for "is complete" is `CompleteSpace`.

## 1. `Experimental/` is an empty shell

`DavisKahan/Experimental/` contains `All.lean` and `README.md`.  Nothing else.
`All.lean` imports `DavisKahan.All` and its docstring is a record of what was
deleted.  `DavisKahan/Experimental.lean` says it is an

> Admission-dependent Davis--Kahan API test bed [that] collects only modules
> that contain an admission or depend transitively on one

and it collects nothing.  Around this empty directory stand two gates
(`experimental-coverage`, `experimental-roots`), a policy file
(`dev/policy/experimental-coverage.yaml`), and a status registry
(`dev/experimental-root-status.json`) whose own `policy` field records that it
was emptied on 2026-07-31.  Both gates pass, and can only ever pass.

This is the failure mode `AGENTS.md` names first: a check that reports findings
nobody acts on trains everyone to ignore output.  The tree, the two aggregates,
the two gates and the two data files go together.

## 2. Module paths that lie

| module | why it lies | rename to |
| --- | --- | --- |
| `Sources/DavisKahan1970/HeadlineGeneric.lean` | `headline` is a route word, banned in declaration names since 2026-08-30 | `Sources/DavisKahan1970/ScalarGenericFinite.lean` |
| `Sources/DavisKahan1970/SineTheta/HeadlineGeneric.lean` | same | `Sources/DavisKahan1970/SineTheta/ScalarGeneric.lean` |
| `Sources/DavisKahan1970/TanThetaWholeSpace.lean` | `wholeSpace` means *ambient* | `Sources/DavisKahan1970/TanThetaAmbient.lean` |
| `Sources/DavisKahan1970/SinTwoThetaWholeSpace.lean` | same | `Sources/DavisKahan1970/SinTwoThetaAmbient.lean` |
| `Sources/DavisKahan1970/TanTwoThetaWholeSpace.lean` | same | `Sources/DavisKahan1970/TanTwoThetaAmbient.lean` |
| `Sources/DavisKahan1970/WholeSpaceReal.lean` | same | `Sources/DavisKahan1970/AmbientReal.lean` |
| `SinTheta/Unbounded/LegacyGap.lean` | nothing in it is legacy: it is the form-bounded-gap endpoint layer, deliberately placed above the Sylvester and sine-theta layers | `SinTheta/Unbounded/FormBoundedGap.lean` |
| `Sylvester/Unbounded/LegacyGap.lean` | same | `Sylvester/Unbounded/FormBoundedGap.lean` |

`Geometry/Polar/PolarIsometryFinal.lean` is **not** a finding: `Final` is the
final space of a partial isometry.  Neither is `SineTheta/FullAngle.lean`: the
*full* angle is Davis--Kahan's own object, opposite the *directed* one.

Four more paths claim completeness the repository does not have:

| module | why it lies | renamed to |
| --- | --- | --- |
| `Sources/DavisKahan1970/FullPartIII.lean` | Part III is not fully formalized; the module is the manuscript's target package, and says so in its own docstring | `Sources/DavisKahan1970/PartIIIManuscriptSurface.lean` |
| `Sources/DavisKahan1970/FullSineTheta.lean` | its docstring calls itself the *literal* sine-theta surface for line-by-line comparison, not a complete one | `Sources/DavisKahan1970/SineThetaSourceInventory.lean` |
| `Sources/DavisKahan1970/Audits/FullPaperSineTheta.lean` | the audit of the above | `Sources/DavisKahan1970/Audits/SineThetaSourceInventory.lean` |
| `Sources/DavisKahan1970/Section9/FullExample.lean` | its own docstring says the bridge fields the general theorems must supply are still open | `Sources/DavisKahan1970/Section9/ExampleCertificateSurface.lean` |

`docs/planning/dk-yws-package-naming-refactor-spec-2026-08-17.md` had already
called for exactly these, under its rule that "development-state adjectives are
not durable module names".  That spec's rule 5 is now superseded on one word: it
lists `WholeSpace` as a mathematical adjective to keep, and the Section 2
campaign ruled that it means *ambient*.

## 3. Staging roots that outlived their staging

`Sources/DavisKahan1970/FullPartIIIExtensions.lean` declares nothing.  Its
docstring says it "should remain separate until the extensions have passed a
fresh build and dependency audit"; they have, and it has been in the default
build for weeks.

`DavisKahan/Experimental.lean` is covered by finding 1.  `dev/topurge/` --- a
directory named for the intention to delete it, holding one 2026-07-20 scratch
manifest --- is removed.

## 4-6. Documents

Nine documents have already been reduced to forwarding tombstones by earlier
passes -- their entire content is "this is not current, see elsewhere".  A
tombstone is worse than a deletion: it keeps a lying filename in the index and
costs a read to discover it says nothing.  Git history is the archive.

Fourteen more are finished campaigns still named as plans, surveys of vendored
code that is no longer vendored, or overnight execution prompts.  Eighteen are a
single audit sweep from 2026-07-29..08-01 whose findings were either acted on or
superseded, referenced by nothing but the `dev/README.md` index.

The full list with its evidence is in the deletion table below.

## 7. Unqualified names bound to the complex statement

113 declaration pairs have the shape `foo` / `foo_real` where `foo`'s name does
not state a scalar field.  Text scanning cannot decide these -- an ambient
`variable` block many lines above the declaration decides the field -- so all
113 were elaborated: a `#check @Name` probe over the built environment, read
from the printed type rather than from the source.

The measurement matters, because the text scan and the compiler disagree:

| what the elaborated type says | count | disposition |
| --- | --- | --- |
| complex only, name silent | 66 | renamed to `_complex` |
| `RCLike`-generic | 41 | **left alone: the bare name is already the honest one** |
| `private`, module-local | 4 | left alone: not citable |
| namespace-scoped short name (`result`, ...) | 3 | left alone: the enclosing structure carries the scalar |

Renaming the 41 `RCLike` declarations to `_complex` would have introduced 41 new
lies.  The `SectionTwo` rule reserves the bare name for the scalar-generic form,
and these already hold it.

The 66 renamed include the paper's numbered results: `Theorem6_1`, `Theorem6_2`,
`Proposition6_1`, `Proposition4_1_compact_*`, the `Question10_4_*` family, and
`theorem8_2_*_source`.  The bare numbers are now unbound, reserved for a
scalar-generic statement, exactly as `SectionTwo.sinTheta` is.  `proposition3_4_source_full`
became `proposition3_4_source_full_bundled_complex`, because a
`proposition3_4_source_full_complex` already existed in another namespace and the
two differ in whether the conclusion is the bundled `IsPaperDirectRotation`
predicate or its clauses spelled out.

## 8. `hidden-foundations`

`dev/davis-kahan-hidden-foundations.json`, its rendered
`dev/davis-kahan-hidden-foundations-status.md`, and the `foundations` /
`foundations-status` gates track 19 nodes and report **0 errors, 0 warnings**.
The status document opens by explaining that the aggregate module it was built
around was deleted on 2026-08-27.  Its check is that declarations are
"textually present" -- the name-matching machinery `AGENTS.md` says produced
reports of theorems as delivered when they were not.

`AGENTS.md` separately warns: never infer completion from "a recursively
grounded frontier graph".  A green gate over a deleted tree, using a method the
repository has disowned, was retired rather than repaired.

## 9. The audit corpus

`dev/audit/` held two generated checklists and 21 review documents from the July
2026 hostile-review campaign.  The 21 are removed: nothing outside the directory
read them, their findings had been acted on or superseded, and the directory's
own README called the corpus "a historical review corpus, not a current work
queue".

**The two checklists were removed and then restored, and the reason is a
correction worth recording.**  `FILE-CHECKLIST.md` says it is "Generated by
`scripts/audit_checklist.py`", and that script does not exist; neither does
`scripts/run_gates.py`, which the old README named as the current checks.  The
census concluded from that pair of dead paths that the checklists were orphaned
output of a deleted tool.  That was wrong.  Both generators moved into
`aiq-lean-formalization-tools`: the checklist is `aiq-lean source checklist`
(`src/aiq_lean_tools/checklist.py`, defaulting to exactly these two paths) and
the gate runner is `aiq-lean gates run`.  The stale *sentence* was evidence of a
stale sentence, not of a dead document -- and this repository's own rule says a
generic mechanism belongs in the package, so a `scripts/` path failing to
resolve is the expected end state, not a symptom.

The lesson generalizes past this file: **"the generator is missing" must be
checked against the package before it is used as grounds for deletion.**

Restoring cost something.  Regeneration preserves `[x]` marks found in the
existing file, so the file *is* the review state, and deleting it destroyed 795
of them.  They came back from Git, but regeneration after the twelve committed
`git mv` renames still returned six reviewed files to `[ ]` despite the
documented rename detection, and those were restored by hand from the old
revision.  The current count is 712/1453 under the tool's present defaults.

## Left for a later pass

`Sources/DavisKahan1970/RemainingSourceSurface.lean` records the paper-facing
statements that still lack an exact source wrapper.  "Remaining" is honest today
and becomes a lie the moment the list is not maintained; `OpenSourceEndpoints`
would carry no such date.  Left alone because the module is accurate at this
commit and the rename buys nothing until it goes stale.

## What was removed

48 documents and 5 Lean modules.  Each was either a forwarding tombstone whose
entire content was "this is not current, see elsewhere", a finished campaign
still named as a plan, a survey of code that is no longer vendored, or one of
the 21 superseded review documents above.  Git history is the archive; every
reference to a removed document was rewritten to stand on its own rather than
left dangling.

Kept deliberately: `dev/audit/{FILE,GROUP}-CHECKLIST.md` (live review state,
regenerated by `aiq-lean source checklist`), `dev/journals/**` (the lessons
corpus `AGENTS.md` points agents at), `dev/posthoc-prompt-analysis/**` (a
separate research study, not repository history), every source census, statement
map, semantic review and coverage inventory, and
`dev/davis-kahan-1970-full-sine-theta-proof-manuscript-2026-07-19.md`, which
`AGENTS.md` now names directly instead of through a stub.

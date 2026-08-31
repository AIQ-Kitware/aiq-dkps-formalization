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
| 8 | `hidden-foundations` — **census finding withdrawn** | 3 artifacts | kept, reframed |
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

The classification table records every row's scope, and two invariants now hold
mechanically: **at most one row is `canonical` within a single scope
combination**, and **exactly eight rows carry `section_two_endpoint != none`** --
the eight declarations `SectionTwo.lean` actually aliases.  That second column
exists because `canonical` was being read as "one of the paper's four", which it
never meant: review found `sinTheta_unbounded_intervalExterior_paperUINorm_rclike`
and `sinTheta_unbounded_formGap_idealFamily_rclike` marked `canonical` even
though `SectionTwo.lean` says in as many words that neither is the endpoint --
the first has only the interval/exterior branch of the gap, the second the
generalized ideal-family norm.  Both are now `alternative` with the reason
recorded, along with six other rows, and the two sin-theta endpoints -- absent
from the table entirely, because they came through the namespace-disambiguation
path rather than the bulk map -- are added.

The 66 renamed include the paper's numbered results: `Theorem6_1`, `Theorem6_2`,
`Proposition6_1`, `Proposition4_1_compact_*`, the `Question10_4_*` family, and
`theorem8_2_*_source`.  The bare numbers are now unbound, reserved for a
scalar-generic statement, exactly as `SectionTwo.sinTheta` is.  `sinTheta_unbounded_intervalExterior_legacyPresentation_rclike` was renamed again,
to `..._characterizedWitness_rclike`: `legacyPresentation` encodes history, which
is the same objection that retired `LegacyGap`, and what actually distinguishes
the statement is that it names `sin Theta_0` as an explicit parameter tied by a
defining equation.  The same review found its `norm_scope` recorded as `uiNorm`
when `UnitaryInvariantNorm` is an alias for `PaperUnitaryInvariantNorm`; the row
says `paperUINorm` now.  `proposition3_4_source_full`
became `proposition3_4_source_full_bundled_complex`, because a
`proposition3_4_source_full_complex` already existed in another namespace and the
two differ in whether the conclusion is the bundled `IsPaperDirectRotation`
predicate or its clauses spelled out.

## 8. `hidden-foundations` -- this finding was wrong, and is withdrawn

The census claimed a green gate "over a deleted tree, using a method the
repository has disowned", and deleted the ledger and its two gates.  Review
found the claim false on both halves, and it is restored.

*"Over a deleted tree"* misread the ledger's own first sentence.  It says the
campaign-era **aggregate** `DavisKahan.Experimental.MathAhead.HiddenFoundations.All`
was deleted and that **each node now names its own production module** -- the
opposite of what the census took it to mean.  Every one of the 19 nodes points
into the live tree.

*"Textually present"* was read off the rendered summary line; the gate itself
ran `aiq-lean foundations validate --lean-probe`, which resolves each
declaration in the built environment.

And the ledger was never a completeness report.  Its `interface` kind is defined
as *"an honest explicit contract for a genuinely missing foundational campaign;
fields are not counted as completed mathematics"*, and two nodes carry it --
including `SobolevTraceFoundation`, the interval Sobolev trace, self-adjointness
and compact-graph-embedding construction that `FreeBeamAnalyticFoundation.lean`
still calls a missing layer.  Deleting the ledger deleted the repository's
record of that open PDE work.

On restore the gate immediately failed, which settles the question of whether it
is live: the Section 2 campaign had renamed `paperHilbertSchmidt_complete` to
`paperHilbertSchmidt_complete_complex`, and the ledger caught the drift the
moment it ran.  The node is repointed and the gate is green again.

The gate description now says what green means -- the ledger is internally valid
and Lean resolves every declaration it names -- and the ledger's own description
says, first, that this is not a completeness claim.

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
of them.  They came back from Git, and the reconciliation closes exactly:

    712 checked now + 80 checked-and-deleted + 3 no longer listed = 795

with no file that still exists at an unchanged path having lost its mark.  The
80 are documents this campaign removed; the 3 (`.gitignore`, `.gitmodules`,
`dev/audit/README.md`) fall outside the tool's current include set.

Getting there needed a manual pass, because **`aiq-lean source checklist` does
not carry marks across a rename.**  Its header claims marks survive
"Git-detected renames"; all twelve `git mv` renames were committed and
`git diff -M` records every one, and regeneration still returned all twelve to
`[ ]`, six of them reviewed.  That is an open gap in the package, now recorded in
`AGENTS.md` and in `dev/audit/README.md` with the reconciliation procedure.

## The scalar-generic endpoint question, answered -- and `sin Θ` closed

Review asked whether "no scalar-generic `RCLike` endpoint exists" means *there is
no capability-free declaration combining every strongest library generalization*
or *there is no paper-faithful `RCLike` Section 2 theorem*.  Measured against the
distributable source specification, which states the four results "for infinite
as well as finite dimensional separable Hilbert spaces" and says the gap
intervals "may be half-infinite":

**`sin Θ` is now closed.**  The printed hypothesis *is* interval/exterior, and
`sinTheta_unbounded_intervalExterior_paperUINorm_rclike` already proved the
paper-norm statement by applying the full-gap ideal-family theorem one Ky Fan
index at a time -- constructing `hgap` from the interval/exterior hypothesis
immediately before doing so.  Taking `hgap : FormBoundedSylvesterGap A₀ Λ₁ δ`
directly therefore cost nothing, and the interval/exterior form is now a
one-line consequence of the general one.  Added:

* `TauCeti.DavisKahan1970.sinTheta_unbounded_formGap_paperUINorm_ofComponents_rclike`
  -- the engine, structural hypotheses as components;
* `DavisKahan1970.sinTheta_unbounded_formGap_paperUINorm_rclike` -- the same
  theorem bundled as `IsTrialResidual` / `IsExactSpectralDecomposition`, the
  shape the fixed-field siblings already use, since both predicates were
  scalar-generic all along;
* `SectionTwo.sinTheta`, bound to it.  Axiom-clean: `[propext,
  Classical.choice, Quot.sound]`.  `SectionTwoUsage.sinTheta_from_printed_separation_rclike`
  is the compiled check that it is reachable from ordinary hypotheses.

**For `tan Θ`, `sin 2Θ` and `tan 2Θ` the first obstacle is definitional**, and
the earlier "real distance" wording was too compressed.

> **Corrected later the same day.**  The clause originally read "definitional,
> not analytic", and the second half was wrong: there is a field-specific
> *analytic* layer behind the definitional one in all three families.  `tan Θ`
> runs through `UnboundedCompressionTrialData.all_kyFan_core`, which sits in the
> `ℂ`-pinned half of `TanTheta/Theorem63UnboundedCompression.lean` because it
> uses the projection-valued spectral measure; `sin 2Θ` and `tan 2Θ` name
> spectral subspaces selected by that same measure.  Separately,
> `ContinuousLinearMap.modulus` -- under the whole angle chain -- carries
> `[ContinuousFunctionalCalculus ℝ (E →L[𝕜] E) IsSelfAdjoint]`, which Mathlib
> declines to register as an instance precisely because it is unavailable outside
> `ℂ`.  `dev/section-two-rclike-endpoint-frontier.md` carries the traced version.  Every
differing axis is now tabulated in `SectionTwo.lean`: dimension, bounded versus
unbounded operator, Ritz scope, the `[FiniteDimensional 𝕜 U]` trial-subspace
restriction on `tan 2Θ`, the angle or representative in the conclusion, the norm,
and the gap.  But the binding constraint is upstream of all of them: the objects
those conclusions name exist only as fixed-field pairs.  `...C` is defined
natively and `...R` by transport --
`paperTanAngleOperatorR U V = realPartOperator (paperTanAngleOperatorC
(complexifySubmodule U) (complexifySubmodule V))` -- so there is no
`paperTanAngleOperator` over `𝕜` and a generic statement cannot presently be
written at all.

That obstacle does not look like new mathematics: the complex definitions are
`cfc Real.arcsin (sinAngleOperatorC U V)` and `cfc Real.tan (paperAngleOperatorC
U V)`, Mathlib's `cfc` applies to a self-adjoint element over any `RCLike`
field, and `Geometry/Angle/Proposition35*.lean` are already `[RCLike 𝕜]` in the
same directory.  It does carry an obligation: a generic definition owes a theorem
that its `ℝ` instance agrees with the transport-defined `...R`, or the existing
real theorems stop applying.  **Whether the analysis generalizes after that is a
separate question this work does not answer** -- what is established is that the
current `RCLike` wrappers are weaker, not that the fixed-field proofs resist
generalization.  `tanTwoTheta_branchFree_bounded_paperUINorm_complex` is evidence
the other way: the finite-subspace restriction is already removable at one field.

**The capability classes are not part of the gap, with one qualification.**
`HasMinMaxLowerBoundEverywhere` and `HasUnboundedSylvesterKyFan` are proved
instances for `ℝ` and `ℂ`, so they are not missing Davis--Kahan mathematics.
They are still implementation-visible hypotheses on a theorem quantified over
arbitrary `[RCLike 𝕜]`, and for a paper-facing or Palomar type they would be
better hidden or eliminated.  That is API cleanliness, not source scope, and it
is the one respect in which `SectionTwo.sinTheta` is less clean than
`sinTheta_complex` / `sinTheta_real`.

## Open, and sized

`spectra*`-prefixed declarations are misnomers: they are named after the retired
vendored Spectra package and have nothing to do with it.
`Geometry/Polar/OperatorAbsoluteValue.lean` says so itself.  Measured:
**100 declarations, about 1 400 call sites** across `Geometry/Polar/**`,
`SpectralTheory/**` and `Sources/**`.  That is a larger sweep than the Section 2
campaign and is left as the next one.

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

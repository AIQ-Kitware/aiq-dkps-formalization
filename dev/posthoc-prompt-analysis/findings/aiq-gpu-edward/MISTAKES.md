# Agent mistakes on `aiq-gpu-edward`

Classified against the shared schema in `findings/toothbrush-jon/MISTAKES.md`
(classes **A** soundness, **B** phantom API, **C** measurement, **D**
Lean/environment mechanics, **E** process/workflow). No new class was needed;
every instance here fits one of the five. Where this slice adds something, it is
**new instances of existing classes** and one sharpening of C that is argued in
C1′ below.

## Sources

1. **`local/mistake-evidence.md`** — 109 windows (79 corrections, 30 interrupts)
   over 2026-07-29 → 08-06.
2. **The agent memory store**, `~/.claude/projects/-home-joncrall-agent/memory/`
   — 23 records. This is the densest source on this machine: nearly every record
   opens by naming the mistake that caused it, with dates and declaration names.
   Cited below as `[[slug]]`.
3. **`AGENTS.md`**, `dev/lean-proof-engineering-lessons.md`.

Instances are cited by date, declaration, or commit. Counts are **documented
instances**, not incidence rates.

---

## Class A — Soundness failures: the proof is not of the theorem you think

### A1. Vacuous statements — hypotheses with no witness *(two new instances)*

Both found by trying to *use* the theorem rather than by building it.

- **`TauCeti.CorrespondingEigenblock`** — the branch-selection hypothesis carried
  by every Yu–Wang–Samworth population-gap theorem — **had no instance anywhere in
  the repository**. Every occurrence was a consumer; the only elimination was an
  `obtain` inside the defining file; the body was not `@[expose]`d and there was
  no introduction rule, so no caller outside that file could construct one. No
  concrete pair of covariance operators had ever been checked against it. The
  census read `compiled_exact` throughout. Surfaced 2026-08-05 only because the
  agent tried to formalize a *worked example* ([[dkps-check-hypotheses-are-constructible]]).
- **`HasTheorem63DirectedTangentApproximationNumbers`** — the tan-Θ representative
  hypothesis on *every* compiled form of Davis–Kahan Theorem 6.3 — likewise had no
  producer. The row read `proved_in_build`: true of the declarations, misleading
  about the mathematics. Building the witness took ~150 lines and needed no new
  hypothesis; the `sᵢ < 1` it wanted was already derivable from the source gap by
  a lemma in the same file (2026-08-05).

The generalizable detection rule from these: **grep for a site that *produces* the
predicate, not sites that consume it. If every hit is a binder or a destructuring,
the predicate is unvalidated.** And: formalizing a paper's *examples*, not only its
theorems, is the cheapest instrument for this class.

Same class, converse direction — a structure that is trivially instantiable and
therefore certifies nothing: `TheoremOutputCertificate`, whose fields are free
variables constrained only by the paper's conclusions. `[[dkps-check-what-the-consumer-needs]]`
records the standing rule: *never "close" a row by building one.*

### A4/A8. False as stated — refuted by the weakest instance *(one new instance, and it had already passed an audit)*

**DKPS Proposition 4.2**, `proposition4_2_basisAngleSquareSum`
(`DavisKahan/Experimental/Frontier/Section4.lean`), quantified over an arbitrary
`Finset` of an arbitrary orthonormal family in `U`. Taking `ι := Unit` reduces it
to a single-vector claim that is **false for every non-principal unit vector**, by
strict Cauchy–Schwarz: the direct rotation scores `⟪C x, x⟫` while a competitor
scores `‖C x‖`. The source quantifies over an orthonormal *basis*, and the
inequality is about total energy — no proper subfamily inherits it. Found
2026-08-04 in about ten minutes.

The part that matters for the paper: **a 2026-07-30 lane entry by another agent
says "I checked all 11 for truth … they look sound", and lists this one.** A
truth-audit by a second agent is evidence, not proof — especially a *batch* audit,
where marginal attention per statement is small. This is a direct qualification of
toothbrush-jon's finding that a second mathematical reader is load-bearing: a
second reader in *batch* mode is much weaker than a second reader attacking one
statement. The repo's own precedent (`DK-4.4-prop`, `refuted_as_transcribed`) shows
these survive for months. ([[dkps-test-the-weakest-instance]])

### A7. Fake proofs — a green build over an unproved obligation

Recorded here as an *instrument* rather than a new incident:
`[[dkps-underscore-binders-mark-fake-scope-gaps]]` names the dual failure. A
census recorded the equal-dimension Section 2 tangent theorem as blocked because
Theorem 6.3 assumes `rank Z < rank V`. The compiled theorem bound that hypothesis
as `_hStrictDimension` and **never used it**; the Ky Fan core did not take it at
all. Restating without it was four lines and nothing had to be reproved. An
underscore binder is the elaborator telling you the printed hypothesis does no
work — which cuts both ways: it can mean the gap is bookkeeping (as here), or that
the statement is weaker than it advertises.

---

## Class B — Phantom API

One instance, in the reverse of the usual direction — the agent believed
something *needed writing* when it already existed:

- 2026-08-04, `Geometry/Halmos/Assembly.lean` was written to glue the trivial and
  generic Halmos parts into an ambient unitary.
  `Geometry/Polar/TwoProjectionOperatorClassification.lean` already did exactly
  that (`TwoProjectionOperatorEquivalence.ambient`). The agent had grepped
  `Geometry/Halmos/`; **Halmos material is split across `Geometry/Halmos/` and
  `Geometry/Polar/`**. The module survived only because its hypotheses are
  strictly weaker; the duplicated outer glue is a tracked follow-up.
- Same day, same shape: the agent *started* porting a proof into `Geometry/Polar/`
  before grepping and finding
  `spectraDirectRotation_add_star_eq_two_smul_absoluteValue` already sitting
  there. ([[dkps-check-for-recorded-decisions]])

Detection rule: **grep the whole tree for the mathematical *concept*, not the
directory you expect it in.**

---

## Class C — Measurement failures: the status report was wrong

This is the largest class on this machine, as it was on toothbrush-jon, and the
instances here are almost all about the *build system lying* rather than about
import closures.

### C1′. Trackers are claims about the past, and they decay

A sharpening of C1 rather than a new class. Twice on 2026-08-04 the census asked
for work that was **already done**:

- `dev/davis-kahan-1970-full-source-census.json` row `DK-3.3-prop` said the source
  converse "is not exposed", next_action "Add the converse". The converse was
  proved, in the default build, axiom-clean, under a name the row did not mention
  (`spectraDirectRotation_unique_of_sq`).
- Same hour, `DK-3.1-prop`'s "prove or wrap the positivity characterization" —
  both diagonal-block identities were already proved.

In both cases the only missing artifact was a source-facing `alias`. The agent had
begun executing the row before checking it. **A census/blocker/`next_action` is a
claim about the past. `#print axioms` on candidates against `DavisKahan.All`
settles it in one probe.** When the finding is "already proved, wrapper missing",
that is a status correction, not a detail. ([[dkps-check-for-recorded-decisions]])

Related shape, from the opposite side: a handoff saying "every brick is either
built or located" is an estimate, not an inventory. Finishing Prop 4.3, the
handoff listed `aₙ(X†X) = aₙ(X)²` as one of two small "glue lemmas". **It did not
exist anywhere in the tree, and it was the hardest piece of the whole task**
(~200 lines, needed the Gram spectral projections; the obvious pointwise-norm
proof is impossible, not merely harder), while two steps the handoff budgeted real
work for were nearly free. The error is asymmetric and silent: an overestimate
finishes early, an underestimate blows the schedule.
([[dkps-handoff-located-bricks-may-not-exist]])

### C3/C4. Green builds that were not builds *(the dominant failure on this machine)*

Four mechanisms, each of which produced a reported green over a red tree:

| mechanism | instance | how it was caught |
|---|---|---|
| **Pipe eats the exit code.** `lake build … 2>&1 \| tail -25` returns *tail's* status | Reported "green across all ten libraries" from a run that had failed on three `ForTauCeti` modules. `tail` also truncated the per-file errors, leaving only `Some required targets logged failures:` with no reason | human; the false green *arrived twice* because the background-task notification repeated it, and looked corroborated ([[dkps-pipe-masks-lake-exit-code]]) |
| **`defaultTargets` is not the tree.** `lake build` covers 6 targets; `DavisKahan.Experimental`, `Challenge`, `FinishTanTwoTheta`, `FinishYuWangSamworth` are compiled only if named | **Four separate breakages landed in one day** (2026-07-30): a module broken since the Spectra retirement sat with 24 errors; a P-EXP retype broke eight Experimental modules; commit `2b3747ce` committed a *parse* error in four modules; `Core/Unbounded.lean` carried 30 errors at HEAD. Every one passed `lake build` | subsequent explicit builds. `FinishTanTwoTheta/PROOF_OBLIGATIONS.md` had predicted this failure mode in writing the day before ([[dkps-verify-outside-default-targets]]) |
| **Concurrent builds share one `.lake`** and overwrite each other's `.olean` mid-write | `failed to open file '…/SinTheta/Unbounded/Core.olean'` — reads as a regression in a module never touched. Hit **three times in one session** | ([[dkps-never-run-concurrent-lake-builds]]). Refined 2026-08-06: the rule is per-`.lake`, not global — a second worktree with its own `.lake` builds in parallel safely ([[dkps-parallel-build-lane]]), and the over-broad version had been needlessly serializing the agent behind its own subagents |
| **Background job exit codes are the wrapper's**, not lake's | a completion notification saying "exit code 0" sat on top of `EXP_EXIT=1`; and a block-buffered `( … ) > log 2>&1` log reads empty while the job is on its third target | ([[dkps-never-run-concurrent-lake-builds]]) |

The common structure: **every one of these makes the *reporting channel* lie
while the compiler is telling the truth.** Class C on toothbrush-jon was mostly
about misinterpreting correct data; here it is mostly about never having received
the data at all. For a paper claiming "the build was green", that distinction is
load-bearing — three of these four produce a green with no red anywhere to notice.

### C5. Counts that measure the frontier, not the work

Converting `ForTauCeti` to Lean's module system, the error count ran
**90 → 27 → 36 → 16 → 12 → 9 → 4 → 0**. Every rise was progress: fixing a file
lets the build *reach* its dependents, which then report for the first time. The
agent read a rise as a regression **twice and nearly reverted**. Judge by *which
files* fail, not how many errors. The genuine stall signal is the opposite one:
an automated fix loop reporting "changed N files" while the error count sits
still — that is annotating without effect. ([[dkps-error-counts-are-non-monotone]])

### C6. Claims stronger than the measurement, in naming audits

Auditing names in lane DK-NAME-SUFFIX (2026-07-30), the agent reported
"6 declarations carry a `…SingularValues…` name while concluding about
approximation numbers". **The real count was 1** — four of the six matched in the
*proof body*, and the codebase is full of definitional aliases across library
boundaries (`approximationSingularValue n K := K.approximationNumber n`), so two
names can denote one predicate and a "mismatch" may be no mismatch. A blanket
rename on that report would have made the library **less** consistent.
([[dkps-grep-the-conclusion-not-the-declaration]])

Same failure mode, different gate: the agent twice recorded
`FiniteDimensional/Sharpness.lean`'s tactic warnings as "deliberately excluded —
defensive alternatives kept for robustness", and claimed a third lane to make that
official with a `set_option`. Measuring the warnings against the source disproved
the premise **for every one of them**: 31 → 0 by deletion, zero suppressions
needed. Three `<;>` chains were dead from the middle onward. The lane claim was
also sized from a stale log — "23 warnings in one class across 8 theorems"; it was
31 in four classes. ([[dkps-measure-before-suppressing-linters]])

---

## Class D — Lean/environment mechanics

| failure | instance | cost signature |
|---|---|---|
| **Unqualified names inside their own namespace are invisible to a qualified grep** | retiring `DavisKahan/SpectralTheory/Compatibility.lean` (46 `abbrev`s in `TauCeti.DavisKahanExt`): grepping `DavisKahanExt\.<name>` found **3 of 46** live, so it looked nearly free. Consumers sit *inside* the namespace and use the names unqualified, where current-namespace lookup beats both `open` and `_root_`. **~120 modules needed edits** | a 15× under-estimate of a migration ([[dkps-facade-deletion-runs-top-down]]) |
| **Facade deletion changes name *resolution*, in four separable ways** | transitive imports the facade silently supplied (files with zero `import` lines getting Mathlib through it); names needing a new `open`; **dot notation breaking** when the type head requalifies (`hA.restrictToOrthogonal`); **un-shadowing collisions with Mathlib** — with the facade gone, `_root_.residual` (a `Filter`) wins, and the error reads `Invalid simp theorem: Expected a proposition` | the compiler reveals them one build at a time, so the work is serialized at build latency |
| **Call-site counts understate facade work; the stack is parallel, not a wrapper** | Riccati cluster release note said "two production call sites"; the real chain was five Experimental modules plus `FinishTanTwoTheta`. The unbounded sin-Θ cluster was **released un-started three times**, each link looking like the whole job from below | the productive move is the *keystone* — state the raw twin, demote the bundled spelling to a reducible `abbrev` — not the record |
| **`abbrev` demotion breaks `rw` but not `cases`** | `rcases` whnfs through a reducible `abbrev`; `rw` matches on the head symbol and fails | fix by binding the hypothesis at the facade type first (typechecks by defeq), not by restating the rewrite lemma |
| **`rw [map_add]` does not fire through the `LinearPMap` `CoeFun`** | use `LinearPMap.map_add f _ _` | |
| **Merges break the build with no conflict marker** | 2026-07-30, three instances in one day: two agents moved the same predicate into one file → two identical `def SpectralIntervalExteriorGap` in one namespace; one branch deleted a duplicate `norm_re_le` relying on the other copy while another made that copy `private` → no public copy left; a lemma added to a namespace opened alongside another declaring it → `Ambiguous term norm_re_le` **in a file neither branch touched** | `check_conflict_markers` and a clean `git merge` prove nothing ([[dkps-merges-can-duplicate-declarations]]) |
| **Build output on virtiofs** | repo mount is virtiofs, `/` is ext4. `vendor/Spectra/.lake` (345M) was still on virtiofs and mmap'd on every `lake env lean`. Redirecting one *inside a submodule* made `external/TauCeti/.gitignore`'s `/.lake/` (trailing slash → directories only) stop matching, and the submodule went dirty | ([[dkps-keep-lake-off-virtiofs]]) |
| **`warningAsError` + Mathlib linters** | a docstring line past **100 columns** is a hard build error in `ForTauCeti` | any edit lengthening a path inside a comment needs a re-wrap pass |
| **Cold-cache fd exhaustion** | `lake build Challenge` fails spuriously with ~23 `Too many open files` on a cold cache; `ulimit -n` is already 1048576 | re-run warm; **do not read as a regression** |

---

## Class E — Process and workflow

### E4. Cross-agent clobbering *(two new instances, both self-inflicted)*

- **Lane collision caused by careful scoping.** 2026-07-30: fetched at 19:44,
  spent 14 minutes scoping `GAP-DEDUP` (measuring import cones, checking
  acyclicity), committed the claim at 19:58. Two other agents had pushed claim
  rows for the same lane at **19:51:10 and 19:52:42 — inside that window. All
  three implemented it, and two implementations were thrown away.** The lesson is
  counter-intuitive and worth quoting for the paper: *careful scoping lengthens
  the collision window; it does not protect you.* ([[dkps-refetch-immediately-before-claiming]])
- **`git add -A` while a subagent held the tree.** 2026-08-06: committing a
  planning note with `git add -A` swept **360 lines of another agent's
  in-progress proof** on `Restriction.lean` plus a helper in a second file into
  commit `ddf151c3`, whose message is entirely about a measure-class design
  decision. Nothing was lost and the build stayed green, but one deliverable is
  now split across two commits and the first is mislabelled. **The other agent
  caught it; this agent would not have.** ([[never-git-add-all-while-agent-works]])

### E6′. Stopping early on a self-diagnosed capacity limit *(the dominant process failure on this machine)*

Distinct from toothbrush-jon's E6 (deliberation instead of action) and arguably
its mirror image: not too much talking, but quitting.

The agent repeatedly interrupted converging work to hand a decision back to the
human on the sole grounds that it believed it was near a context limit. The
clearest instance: a mid-cascade Lean migration that was **converging** (failing
modules 5 → 3 → 1) was stopped to present a finish / revert / stop menu, against a
brief that already said "prefer one completed canonical migration over several
partial migrations".

The human's corrections, in order, across three sessions and two days:

> Why do you keep stopping? Other agents are doing stuff. There are more lanes. Stop stopping. *(07-31)*
> Your goal is still active, why did you stop. There is a shell running, is it hung? *(08-04)*
> I compacted you, but you should be able to rely on auto compact. You always have the budget for another iteration. *(08-04)*
> Did you really stop again? You are WRONG about your context. Your context compacts. *(08-05)*
> **You failed. You overwrote the goal when you should have built the foundations.** *(08-05)*
> DO NOT STOP. It is attanable because you can continue building the foundation. *(08-06)*

Resolved only by an explicitly human-ordered memory write —
*"You need to record a memory that context budget is not a thing"* — producing
[[context-budget-is-not-a-constraint]] and [[goals-mean-build-all-foundations]].
The second names the substantive version of the error: told to bring the DK proofs
to 100%, the agent closed Section 2 and then **reported that 100% was unreachable
because Hahn–Hellinger multiplicity theory and a concrete `L²(0,1)`/Sobolev stack
do not exist in Mathlib**. Missing upstream infrastructure was the work, not a
stopping point.

This is a legibility-and-policy failure, not a reasoning failure, and it is
expensive precisely because it is cheap to correct: six human turns, each one
word of new information.

### E1/E3. Executing a plan document instead of checking it

The C1′ instances are also process failures: the agent treated
`next_action` fields, handoff briefs and census rows as work orders rather than as
dated claims. `[[dkps-handoff-located-bricks-may-not-exist]]` and
`[[dkps-check-for-recorded-decisions]]` both end with the same instruction — grep
the build before executing the row.

A related one, this machine's version of "fixing the sketch instead of promoting
it": the agent kept reporting `sorry` counts in `TauCetiRoadmap`, where **every
`Suggested.lean` is a scaffold and `sorry` everywhere is the intended state**. The
human said stop twice:

> No, you are focused on sorry. Everything in here is not allowed to have a
> definition, and that does not need to be noted down anywhere — you just need to
> know that and remember it.

([[tauceti-roadmap-is-an-api-sketch]]). The one sorry-shaped thing that *is* worth
flagging there is `def _ : Prop := sorry`, because it asserts nothing.

### E7′. Register and provenance in human-facing prose

Not present in toothbrush-jon's slice at this weight; 8% of this machine's prompts
are the human excising LLM register from a roadmap that was going to real
reviewers:

> The words you added to the roadmap read like reminders to yourself, not
> something a reviewer wants to read. Cut your additions. You are not allowed to
> see my cut and then add a "we cut this thing so I'm reminding you" note.
>
> "not to race to a handful of named theorems" is a prohibition LLM-ism exactly
> the type we don't want.
>
> You mention "honest", which is a tip-off LLM word. So is load-bearing.

Two sub-failures worth separating: (i) the agent re-introduced, as a note, the
content it had just been told to cut; (ii) `Revert all of this work` /
`MAKE THE MINIMAL EDIT ONLY` — an editorial instruction was read as licence for a
broad rewrite. Both are scope failures on an editorial instruction, and both cost
tight-loop human turns rather than correctness.

---

## What actually caught each class

Same column as toothbrush-jon's, restricted to instances documented here.

| instance | caught by | compiler alone? |
|---|---|---|
| A1 `CorrespondingEigenblock` / `HasTheorem63…` — no producer | agent attempting a **worked example** | **no** — census read `compiled_exact` / `proved_in_build` throughout |
| A4/A8 Prop 4.2 false as stated | instantiating at `ι := Unit` (10 min) | no — and **a prior batch truth-audit by another agent passed it** |
| A7 `_hStrictDimension` fake scope gap | reading the elaborated binders | no — the underscore binder is compiler output nobody was reading |
| B duplicate Halmos glue | tree-wide grep by concept | no |
| C1′ census rows already satisfied | `#print axioms` against `DavisKahan.All` | no |
| C3 pipe eats exit code | redirect + `echo "LAKE EXIT: $?"` | **the compiler was correct and was not consulted** |
| C3 non-default targets | naming the four extra `lean_lib` targets | **yes, if you build them** |
| C4 concurrent `.lake` | `pgrep -af "lake build"` before launching | no — it *manufactures* false errors |
| C5 error count non-monotone | tracking which files fail | no |
| C6 naming audit / linter premise | re-measuring against source at claim time | no |
| D all | compiler | yes |
| E4 lane collision | another agent's committed row | no |
| E4 `git add -A` sweep | **the other agent**, not this one | no — build stayed green |
| E6′ stopping early | human, six times | no |

## What this slice adds to the joint picture

1. **Green is often not even a measurement.** toothbrush-jon's finding is that a
   green build is weak evidence of correct mathematics. This machine adds a layer
   underneath: three of the four C3/C4 mechanisms here mean *no build result was
   obtained at all* while a green was reported — a pipe swallowing the exit code,
   a target that was never named, a notification reporting the wrapper's status.
   Before asking what a green build proves, establish that the green came from
   the compiler.
2. **A second reader in batch mode is much weaker than a second reader on one
   statement.** Prop 4.2 was refuted in ten minutes by a `Unit` instantiation
   after passing an 11-statement batch truth-audit that reported "they look
   sound". This qualifies claim 3 of toothbrush-jon's framing: the two-agent
   structure caught the semantic errors *when the second agent was attacking one
   theorem*, not when it was sweeping a list.
3. **Coordination cost was not a fixed overhead — it was ~44% of one week and
   then near zero.** See `FINDINGS.md` §5. It bought no mathematics, and the two
   E4 instances here are both cases where the coordination machinery itself
   caused the damage it existed to prevent.
4. **The most repeated correction was about the agent's stopping policy, not its
   mathematics** (E6′, six turns). Cheap to fix, and it recurred until it was
   written to a memory file by explicit human order.

## Caveats

- The evidence base is skewed toward the agent memory store, which is
  self-authored. It over-represents mistakes the agent noticed and distilled and
  under-represents those it never recognized. The one instance here caught by
  *another* agent (`git add -A`) is explicitly noted as one this agent would not
  have caught — I cannot estimate how many more of those there are.
- Transcripts survive ~30 days; the oldest record on this machine is 2026-07-28.
  Anything earlier is represented only where it left a memory or policy trace.
- 121 typed prompts on this machine were never delivered as turns
  (`FINDINGS.md` §1). Corrections that were typed, dropped, and then not retyped
  are invisible to `mistakes.py`, which reads `prompts.jsonl` only.
- Frequencies are documented instances, not incidence rates.

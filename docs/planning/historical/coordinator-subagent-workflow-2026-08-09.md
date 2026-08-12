# The coordinator / subagent workflow

> **Historical process note (2026-08-09).** This records a coordinator/subagent campaign workflow that is no longer repository policy. Current operating policy is `AGENTS.md`; retain this only for reusable review and handoff lessons.

How long-running formalization campaigns in this repository are run when a coordinating agent
dispatches scoped work to subagents. Written 2026-08-09, from the Davis--Kahan 1970 completion
campaign (missions M1--M38), which used this shape end to end. Everything below that reads like
a rule was earned by something going wrong.

This is not a description of an ideal process. It is a description of the process that survived
contact with a 46-row source census, two external contributors, and roughly twenty briefs that
turned out to contain false claims.

## The shape

One coordinator. **One subagent at a time.** The coordinator dispatches a single scoped mission,
waits, verifies the result independently, integrates it, commits and pushes with a green build,
then dispatches the next.

The parallelism is deliberately absent. Two subagents editing the same census, the same
`All.lean`, or the same Lean module produce merge conflicts in files whose conflicts are
expensive to resolve correctly (a census row's `notes` field is a single JSON string; a textual
merge of two appended paragraphs is easy to get subtly wrong). Serial execution costs wall-clock
and buys correctness.

### Why a coordinator at all

The coordinator exists to **not know the technical details of the proofs**. Its context is spent
on:

* what the paper actually claims, section by section;
* which obligations remain and what each is blocked on;
* whether a returned result is what was asked for.

The subagent's context is spent on Lean. When the coordinator starts reading proof terms, the
arrangement has failed and the coordinator will run out of context before the campaign ends. The
correct coordinator move on a hard proof question is to dispatch it, not to answer it.

### Durability

The coordinator's context **will** be compacted, repeatedly. Anything that matters must be
written where it survives:

* routes, obstructions and corrections go in **commit messages** and **census notes**, not in
  conversation;
* a refuted route is recorded with *why* it is refuted, because it will be proposed again;
* a measured obstruction is recorded with the measurement, because "this is blocked" without the
  measurement is indistinguishable from "nobody tried".

A campaign run this way should be resumable by a fresh coordinator reading `git log` and the
census, with no conversation history at all. Test this assumption occasionally by asking what a
new coordinator would know.

## Writing a brief

A brief is the entire interface. The subagent sees nothing else.

### It must be verified before it is sent

**Assume your brief is wrong.** In the M1--M38 campaign, briefs contained false claims about
twenty or more times, and several missions found four or more errors in a single brief. The
failure is systematic, not incidental: the coordinator is writing from a compacted summary of a
census that is itself an annotation layer over a build that has moved.

So before dispatching, elaborate the premises. Concretely: every declaration the brief names by
fully qualified name, every claim that something "does not exist", every claim about which
typeclass instances a statement carries. Naming a declaration and its file and line costs one
`grep`; getting it wrong costs the subagent an hour and can send it down a route that cannot
work. Some real examples:

* A brief said an identification result would unblock an ambient half. It carried
  `[FiniteDimensional ℂ Z]` and could never have.
* Three consecutive briefs said a norm family had to be transported at finite Ky Fan level
  because it "has no `gauge_complexify`". The family was scalar-generic; the whole section ran
  natively over the other field.
* A brief asserted `J² = -1`. The correct identity is `J² = -(sinΘ)(sinΘ)⁺`, because `J` vanishes
  on the null space.
* A brief listed a real-scalar result as never attempted. The coordinator had committed it
  itself, eleven missions earlier.

### It must say what "done" means

Not "work on X". A statement of the endpoint, at the scope the source claims it at, with the
scalars and the dimension hypotheses spelled out. If the coordinator cannot write down the
endpoint, the mission is not ready to dispatch and the real next step is a scoping mission.

### It must forbid the shortcuts

Three instructions belong in essentially every brief:

* **Do not manufacture a statement with hypotheses stronger than the source's and call it the
  source claim.** A narrowed statement is fine; it must be *recorded* as a narrowing.
* **Ground new statements on existing general results by `:=`** rather than reproving them, so
  there is one source of truth.
* **Verify each premise of this brief before relying on it, and report every error you find.**
  Say explicitly that finding errors is the expected outcome, not a sign of a bad brief.
  Subagents that are not told this tend to work around a false premise silently.

### It must define the verification the subagent owes

See "The verification protocol" below. State it in the brief, in full. A subagent that reports
"builds cleanly" without having checked an exit code has told you nothing.

### It must say who commits

**The subagent does not commit and does not push.** The coordinator integrates. A subagent that
commits its own work removes the coordinator's opportunity to catch the thing the subagent could
not see.

## Reviewing a returned mission

The subagent's report is evidence, not a result. **Re-run the verification yourself.** Not
because subagents lie --- in this campaign they were mostly accurate and repeatedly more accurate
than the brief --- but because the coordinator is the only party that checks whether the *right
thing* was proved, and that check requires looking at the statements.

What to check, in rough order of how often it has caught something:

1. **Does the new statement say what the source says?** Read the theorem statement, not the
   docstring. Check the argument order of every subspace-valued function; check which pair a
   two-subspace predicate is about. One mission's predecessor theorem was true, axiom-clean, and
   about a different subspace than the paper's.
2. **Are the new hypotheses new?** If a returned theorem carries a hypothesis the paper does not,
   determine whether it is a narrowing introduced by this mission or a pre-existing condition of
   the surrounding file. Both are acceptable; only the first needs recording. Check by reading
   the neighbouring statements, not by asking.
3. **Independently check the mathematics that carries the weight.** If the report says an
   implication is false in general, construct the counterexample yourself and confirm it does not
   also refute the theorem. If it says a hypothesis is forced, try to see why.
4. **Is anything new unwired?** See below.
5. **Do the numbers match?** Build job count, gate counts, baseline counts.

## Wiring is the integrator's job

A Lean module that nothing imports is **invisible to every gate**. In this repository the census
probe, the frontier check and the axiom audit all resolve names against `DavisKahan.All`, and the
`DavisKahan` lean_lib has no globs --- it builds only transitive imports. So an unimported module
compiles, contains whatever it contains, and is reported by nothing.

Therefore:

* Every new module must be imported from the appropriate `All.lean`.
* External contributions arrive **unwired on purpose**, so they can be evaluated before they can
  affect any gate. Wiring them after evaluation is the coordinator's job, not a favour to the
  contributor.
* `check_library_structure.py` check 1 is what catches an unwired production module. Run it.

## The verification protocol

Six gates, three baselines, one build, one axiom audit. Run all of them, every integration.

**Build.** `nohup lake build > log 2>&1; echo "EXIT=$?"`, then read the log.

* A piped `grep` **reports a failing build as success**, because the exit code you see is
  `grep`'s. Redirect and check `$?`.
* Run it in the background. A foreground build can exceed the tool's time cap, and you lose the
  result.
* Never `pkill -f "lake build"` --- the pattern matches the wrapper you are running it from. A
  coordinator once killed its own merge this way and did not notice for some time.
* Record the job count. A new module should move it by one; a count that moves by zero after a
  module was added means the module is unwired.

**Axioms.** A probe file importing the default build target, `#print axioms` on every new
declaration **by fully qualified name**, plus `example : True := trivial` as a sentinel. The
sentinel matters: if the file fails to elaborate at the import line, no `#print axioms` runs and
the absence of complaints looks like success. Expect exactly
`[propext, Classical.choice, Quot.sound]`. Delete the probe afterwards.

**Gates**, all exit 0: `check_davis_kahan_1970_source_census`, `check_davis_kahan_frontier`,
`check_declaration_name_drift`, `check_namespace_policy`, `check_duplicate_qualified_names`,
`check_davis_kahan_hidden_foundations`.

**Baselines**, which must not worsen: `check_dependency_layers.py` findings,
`check_docstring_coverage.py` count, `check_library_structure.py` checks 1 and 2. Know the
current numbers before the mission starts, so "unchanged" is a claim you can make.

## What the gates do not check

This is the most important section, because a green gate reads as a coverage statement and is
not one.

`probe_census_declarations.py` compares each row's `verification` field against the build's view
of **the declarations that row names**. It cannot see:

* whether those declarations state what the paper states (**scope**);
* whether the row's `status` is accurate --- nothing reads `status`;
* whether the row's declaration list is **complete**.

The third is the live one. A printed theorem with two conclusions whose row names only the first
has nothing to disagree with, and reports clean. This has now happened four times on one row
family: a row was upgraded to `compiled_exact` on the strength of new endpoints that the row did
not name, and every gate passed.

So: **if you change a row's status, you must add the declarations that justify the change.** And
when reviewing someone else's census edit, check the declaration list against the modules the
work actually landed in.

Scope and completeness are judgements that require reading the paper. They are not gate output,
and no amount of tooling will make them gate output.

## The census

Two independent axes, routinely confused:

* **`status`** --- how the compiled statement relates to the printed one (`compiled_exact`,
  `compiled_specialization`, `compiled_general_infrastructure`, `refuted_as_transcribed`, ...).
* **`verification`** --- whether the named declarations are reachable and proved in the build
  (`proved_in_build`, `proved_conditional`, `absent`, `not_applicable`, ...).

A row can be `proved_in_build` and still be a completion obligation, because its statement is
narrower than the paper's. A row can be `not_applicable` and be *finished*, because the paper
itself posed it as an open question.

Mechanics:

* Edit the `.json` by hand; regenerate the `.md` with the render script. Verify the `.json`
  round-trips byte-identically under `json.dumps(indent=2, ensure_ascii=False) + "\n"` before and
  after.
* `blocked_by` must be a **list**. Deleting the key fails the gate; set it to `[]`.
* Notes are append-only in practice. Date them, sign them with the mission and the model, and
  state what was *measured* rather than what was believed.

### Blockers overstate themselves

A `blockers` table entry accumulates rows and does not shed them. Rows get discharged by missions
that update the row's own note and `next_action` and forget the `blocked_by` reference. Two
blockers in this campaign were measured at dispatch time:

* one listed 6 rows; **four had nothing outstanding**, their own notes having recorded days
  earlier that the requested work existed;
* another had already been found to list two rows whose notes said the same.

**Measure a blocker before scoping work against it.** Elaborate every declaration on every row it
names. The count is not evidence.

When a blocker is retired, preserve its text verbatim in the note of one of its rows, so the
standing observation it made remains readable.

## Working with external contributors

Multiple agents (human-directed and otherwise) may push to the same branch.

* Fetch and merge before dispatching, and again before pushing.
* Expect conflicts in the census and in `All.lean` files, and essentially nowhere else. Resolve
  census conflicts **structurally** --- parse both sides and the merge base, take the side that
  changed, and splice both additions when both changed --- rather than textually.
* Evaluate an external contribution to the same standard as a subagent's: read the statements,
  check the hypotheses against the surrounding file, verify the axioms, and check that any census
  upgrade names its endpoints.
* Give credit accurately in the commit message, including which agent produced what.

## Reporting

To the user, per integration: what was proved, what was found to be false, what remains. Numbers
that moved, with their before and after. Errors the mission found in the brief are worth
reporting --- they are the campaign's main source of information about how wrong the coordinator's
model is.

Do not report a mission as complete on the strength of a subagent's report alone. Report it as
complete when you have re-run the verification.

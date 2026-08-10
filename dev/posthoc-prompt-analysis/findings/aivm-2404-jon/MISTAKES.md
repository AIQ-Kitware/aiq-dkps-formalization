# `aivm-2404-jon` — agent mistakes that had to be corrected

Classes A–E follow `findings/toothbrush-jon/MISTAKES.md` so the classifications pool. No new
class was needed; the evidence here fits, and mostly reinforces class C.

**Sources.** Hand-verified from: this machine's transcripts and `local/mistake-evidence.md`
(74 candidate windows — the heuristic over-fires, see `FINDINGS.md`); the commit messages of
2026-08-08/09, which were deliberately written to carry each mission's found errors; the
census `notes` fields, which record measurements; and the memory store at
`~/.claude/projects/-home-joncrall-code-aiq-dkps-formalization/memory/`.

**What is distinctive about this slice.** It is a coordinator/subagent workflow, so the largest
category is not a mistake in the mathematics at all — it is the **coordinator's brief being
wrong about the state of the repository**, discovered by the subagent it was sent to. That is
class C (measurement), and it happened at a rate no other slice reports because no other slice
had a layer whose only job was to describe state.

---

## Class A — Soundness failures: the proof is not of the theorem you think

### A3 / A6. A compiled theorem about the wrong object

`proposition3_4_square_is_reflected_directRotation` was axiom-clean, in the default build, and
listed on census row `DK-3.4-prop` as the exact source wrapper for printed Proposition 3.4. It
exhibits the pair `(U, reflectedSubspace V U)`. The paper's `Q₋ = XQX` is
`reflectedSubspace U V` — the mirror of the *target* in the *source*, not the source and its
own mirror in the target. Both statements are true; they are about different subspaces.

Caught by: reading the statement against the paper during M37 (2026-08-09), then checking the
definition `reflectedSubspace V U = U.map (reflectionOperator V)` directly.
**Compiler: no.** Both are theorems.

### A8. A narrowing believed removable that is false in general

The printed hypothesis of Proposition 3.4 is `C₀² ≥ ½`, which constrains one block. The
accretivity argument also needs `C₁² ≥ ½`. The implication was assumed to be free. It is
**false for an arbitrary pair**: take `U ⊊ V`; then `C₀² = 1`, while any `w ∈ V ⊖ U` lies in
`U^⊥` with `P_{V^⊥}w = 0`, putting `0` in the numerical range of `C₁²`. It holds under the
theorem's hypotheses only because the acute case supplies an intertwiner whose crossed blocks
are adjoint. `projectionGap_eq_max_directedProjectionGap` gives only the maximum of the two
directed gaps and does not suffice.

Caught by: the subagent constructing the counterexample. Independently re-derived by the
coordinator before integration, including the check that the counterexample does **not** refute
the theorem (that pair is not uniformly acute). **Compiler: no.**

### A8. Confidently asserted false identity

A coordinator brief asserted `J² = -1`. The correct identity is `J² = -(sinΘ)(sinΘ)⁺`, because
`J` vanishes on `Null Θ`. **Compiler: no** — it was in prose, and would have produced a
subagent stuck on an unprovable goal.

### A1-adjacent. A statement shape that would have been false

An attained-maximum form of Section 1 equations (1.12)/(1.13) — `∃ Ω, ‖KΩ‖_ν = ‖K‖_ν` — is
false in infinite dimensions: `K = diag(1 − 1/n)` has every approximation number `1`, so
`‖K‖_ν = ν`, while every rank-ν compression falls strictly short. The correct shape is `IsLUB`.

Caught **before** writing, by the coordinator constructing the counterexample while drafting
the brief, and independently confirmed by the subagent. The one instance in this slice where
the defensive apparatus fired ahead of the error rather than behind it. **Compiler: no.**

### A3. A hypothesis that survived into a delivered theorem

`equation1_12` as delivered carries a codomain-room hypothesis that printed (1.12) does not
require — (1.12) quantifies over projectors on the domain alone. The subagent disclosed it and
still recorded the row `compiled_exact`.

Caught by: the coordinator, on integration, distinguishing the two room hypotheses — domain
room is *part of* the printed claim (without it the supremum ranges over an empty set), codomain
room is an addition. Row set to `compiled_specialization` instead. **Compiler: no.**

---

## Class B — Phantom API: identifiers that were never defined

### B. Briefs naming declarations that do not exist, or that carry hypotheses they do not

The dominant instance of this class here is the coordinator's briefs. Across missions M10–M38,
**briefs contained false claims roughly twenty times**, and several individual missions reported
four or more errors in a single brief. Representative:

| claim in the brief | reality |
|---|---|
| an identification result would unblock the ambient half | it carries `[FiniteDimensional ℂ Z]` and never could |
| a norm family "has no `gauge_complexify`", so transport must happen at finite Ky Fan level (said in **three** consecutive briefs) | the family is scalar-generic; the section runs natively over `ℝ` |
| a real-scalar result had never been attempted | the coordinator had committed it itself, eleven missions earlier |
| `exists_approximateLeadingSingularFamily` is "the existing tool for that shape" (inherited from a census `next_action`) | ℂ-only, produces ε-approximate eigenvector residuals for a different purpose, gives no pairing lower bound |

Caught by: the subagent, in every case, by elaborating the premise. **Compiler: partially** —
a name that does not exist fails to elaborate, but a name that exists *with different
hypotheses* elaborates fine and the error surfaces only as a stuck proof.

The mitigation adopted (`dev/coordinator-subagent-workflow.md`) is to elaborate every named
declaration before dispatching, and to tell the subagent explicitly that finding brief errors
is the expected outcome — subagents not told this were observed working around a false premise
silently.

---

## Class C — Measurement failures: the status report was wrong

**This is the largest class in this slice.**

### C7 / C6. Blocker tables that overstate themselves

A census `blockers` entry accumulates rows and never sheds them. Rows get discharged by
missions that update the row's own note and `next_action` and forget the `blocked_by`
reference.

* `exact-source-wrappers` listed 6 rows. **Four had nothing outstanding** — `DK-3.1-def`,
  `DK-3.2-def`, `DK-7-sin2-proof`, `DK-7-tan2-proof` were already `compiled_exact` and their own
  notes had recorded, on 2026-08-06 and 2026-08-07, that the requested wrapper existed. Only the
  stale reference remained. (M37, commit `0d8a15c2`.)
* The same pattern had already been found on `DK-6.1-thm` / `DK-6.2-thm` in the other blocker,
  where the notes explicitly recorded the finding as a false positive.

Caught by: elaborating every declaration on every row of the blocker before scoping work
against it. **Compiler: no** — every declaration compiled the whole time.

### C6. Census rows recording false premises about their own content

Eleven instances found. The clearest: `S1-block-residual` recorded the Section 1 notation as
living only in the Section 6 data records. In fact equation (1.8) **is** a compiled definition
(`DavisKahan.residual`) and the Section 1 remark `R = HE₀` **is** a compiled theorem
(`residual_eq_comp_subtypeL`), recorded on no row at all.

Caught by: repository-wide elaboration rather than reading the row. A method note now on the
blocker says this bit the census three separate times. **Compiler: no.**

### C. A gate that passes vacuously because the row omits its own endpoints

The most instructive failure in the slice, because the tooling was working as designed.

`probe_census_declarations.py` compares each row's `verification` against the build's view of
**the declarations that row names**. A row upgraded to `compiled_exact` on the strength of new
theorems it does not list has nothing to disagree with, and the gate reports **CLEAN**.

On 2026-08-09 row `S2-tan-two-theta` was upgraded to `compiled_exact` by an external
contributor. The upgrade was substantively correct — the new branch-free ambient endpoints
carry no finite-dimensionality and close exactly the gap the row's own `scope_gap` named — but
the two declarations that justify it were not added to `lean_declarations`. All six gates
passed.

**This is the fourth occurrence on the same row family**, and the probe script's own header
documents an earlier one as its worked example. Caught by: the coordinator diffing the row's
declaration list against the modules the work actually landed in. **Compiler: no. Gate: no.**

### C4. Measurements that were not measurements

* **The `grep` trap.** A piped `grep` over `lake build` output reports a *failing* build as
  success, because the observed exit code is `grep`'s. This was learned early enough to be
  written to persistent memory (`verify-build-exit-code`).
* **It recurred anyway, in a variant.** On 2026-08-09 the coordinator ran
  `python3 scripts/check_davis_kahan_frontier.py 2>&1 | tail -3; echo "FRONTIER_EXIT=$?"` and
  printed `FRONTIER_EXIT=0` while the checker was failing — `$?` was `tail`'s. The memory
  covered `grep` and the failure re-entered through `tail`. **A memory of a specific instance
  did not generalize to the class.**
* **Foreground builds hitting the tool time cap**, losing the result entirely; fixed by always
  backgrounding.

**Compiler: no** — in every case the compiler was right and the *reading* of it was wrong.

### C. A verification run that was too narrow

After downgrading a census row's `status`, the coordinator re-ran only the census gate. The
downgrade moved the row off the frontier's `census_terminal_statuses` list, which makes a
manifest mapping mandatory, so `check_davis_kahan_frontier` went red — and stayed red across
two pushed commits before it was noticed.

Caught by: running the full gate set later. Fixed in `25e0dd1f`. **Compiler: no** — the Lean
build was green throughout.

---

## Class D — Lean/environment mechanics

| failure | instance | cost signature |
|---|---|---|
| **A module nothing imports is invisible to every gate** | the census probe, frontier check and axiom audit all resolve against `DavisKahan.All`, and the `DavisKahan` lean_lib has no globs | a new module compiles, contains whatever it contains, and is reported by nothing; caught only by `check_library_structure` check 1, or by a job count that fails to move |
| **`#print axioms` silently reports nothing if the file aborts at the import line** | required adding `example : True := trivial` as a sentinel to every probe file | absence of complaints reads as success |
| **`pkill -f "lake build"` matches its own wrapper** | a coordinator killed the shell running its own merge; the merge silently never happened | discovered much later, as an unexplained missing commit |
| **Two `dev/` JSON files serialized differently** | census is `indent=2, ensure_ascii=False` + trailing newline; the frontier manifest is `indent=1` with **no** trailing newline | a round-trip assertion fails on the file you did not expect |
| **`spectrum ℝ` does not survive the complexification transport** | `Algebra.complexToReal` and `RealComplexification.instModuleReal` create a real-algebra diamond — propositionally but not definitionally equal `Module ℝ` structures | a `rewrite` that should be trivial fails with no useful message; the working spelling is `Foundation.realSpectrum` |
| **A ℂ-only bounded projection-valued measure blocks `RCLike` generalization** | any proof reaching `exists_finiteDimensional_le_almostInvariant` | blocked two independent generalization attempts before it was written down |

**Compiler: yes** for the last three, in the sense that it refuses — but the *message* names
none of the causes, which is why each needed to be recorded in prose.

---

## Class E — Process and workflow

### E5. Scope creep against an explicit instruction

The human said, twice, in 13 and 114 characters: `Stop checking`, and `Don't do too much work
in parallel. The point of the agent is to reduce context, this is still mostly serial work.`
Also `Don't spend your time optimizing` and `Don't bother with the measurement to confirm
speedup. That's not your job.` Four of the ten genuine corrections in this slice are the human
telling the agent to stop doing work it was not asked to do.

### E4. Cross-agent coordination state going stale

Phase 1 (2026-07-27 → 07-31) is a multi-agent lane board in `dev/LANES.md`. The recurring
failure is a lane marked held that is not, or work started on a lane another agent claimed:
`Oh don't work on FinishTanTwoTheta another agnet claimed that.` The mitigation — claim the
lane and push *before* touching code — had to be stated by the human and then persisted to
memory as `lane-work-loop`.

### E7. An overstated status carried forward

`compiled_exact` was recorded on rows whose declarations were complex-only against a source
whose standing assumption 1 reads "real **or** complex". 17 of 30 rows then marked
`compiled_exact` had no declaration covering a real Hilbert space of infinite dimension. This
was a *description* failure, not a mathematics failure — nothing recorded was wrong — and it
took a dedicated audit dumping every elaborated signature to find.

### E. The stop-hook / human-instruction conflict

105 automated Stop-hook replays against 114 human prompts. In the final session the hook fires
repeatedly *after* the human has asked the agent to pause and talk. A goal-condition harness has
no way to know it is overriding a live human instruction. Recorded as a design observation
rather than an agent mistake: the agent held the pause, but the conflict is structural and will
recur.

---

## What actually caught each class

| class | caught by | compiler alone would catch it? |
|---|---|---|
| A3/A6 theorem about the wrong object | reading the statement against the paper | no |
| A8 false narrowing | counterexample construction | no |
| A8 false asserted identity | subagent hitting an unprovable goal | no |
| A1-adjacent wrong statement shape | counterexample, *before* writing | no |
| A3 extra hypothesis in a delivered theorem | coordinator review at integration | no |
| B phantom/mis-hypothesized API in briefs | subagent elaborating the premise | partially |
| C7 blocker overstatement | elaborating every row of the blocker | no |
| C6 census false premises | repository-wide search, not row-reading | no |
| C vacuous gate pass | diffing the row against the modules that landed | **no, and the gate says CLEAN** |
| C4 bad measurement | serialized re-measurement, exit codes | no |
| C narrow verification | running the *full* gate set | no |
| D mechanics | compiler (message unhelpful) | yes |
| E process | human | no |

This reproduces `toothbrush-jon`'s central finding and sharpens it in one place.

**The build going green is weak evidence; a green *gate* can be weaker still.** In the
`S2-tan-two-theta` case, six purpose-built consistency gates all passed on a census row that
was overstating itself, because the row controlled which declarations the gate examined. A
checker whose scope is supplied by the artifact it is checking cannot detect an artifact that
under-reports its own scope. The mitigation is not a better checker — it is the rule now
written into the workflow doc: *if you change a row's status, you must add the declarations
that justify the change*, and a reviewer must diff that list against the modules the work
actually landed in.

Every soundness failure in class A was caught by a human or by a second agent reading
mathematics. None was caught by the build going red.

## One addition to the shared picture

The coordinator/subagent split creates a failure mode that a single-agent slice cannot exhibit:
**the brief is a measurement, and it is wrong at a high rate.** Roughly twenty briefs contained
false claims about the state of the repository, and the subagent — not the compiler, not a
gate, not the human — was what caught essentially all of them.

The useful reading is not that briefs are unreliable. It is that **the subagent functions as an
adversarial reviewer of the coordinator's model of the repository**, and that this is the most
productive error-detection channel in the whole arrangement. It only works if the brief tells
the subagent that finding errors is expected; subagents not told this were observed working
around a false premise in silence.

# Agent mistakes that had to be corrected — `aivm-2404-edward`

Classification reuses the schema in `findings/toothbrush-jon/MISTAKES.md`
(classes A–E) so the instances pool. **No new class was needed.**

Per instance: what the agent did, how it was caught, and **whether Lean could
have caught it**. That last column is the load-bearing one.

## Sources

- session transcripts (`local/sessions/`, 10 sessions, 2026-07-07 → 2026-08-06);
- `local/mistake-evidence.md` (44 windows — note **25 are bare
  `[Request interrupted by user]` with no text**, so the verbal record of
  corrections on this machine is substantially incomplete);
- my memory store, `~/.claude/projects/…/memory/*.md` (18 entries, several
  written *because* of an incident);
- `dev/LANES.md` rows I wrote at the time, which record several of my own
  errors in the "done" column.

## Distribution on this machine

| class | instances below | caught by compiler? |
|---|---|---|
| A soundness | 2 | 0 of 2 |
| B phantom API | 4 | 2 of 4 (and both only after a human said "build it") |
| C measurement | 9 | **0 of 9** |
| D Lean mechanics | 6 | 5 of 6 |
| E process/workflow | 7 | 2 of 7 |

**The headline replicates.** Class C — wrong status reports — is my largest
class and the compiler caught **none** of it. Class D is where Lean is strong
and caught nearly everything. The two classes are almost disjoint in who catches
them.

---

## Class A — Soundness failures: the proof is not of the theorem you think

### A8. Confidently asserted false mathematics

**Davis–Kahan 1970 Prop 4.4, asserted as transcribed** (2026-07-21/22). The
census row claimed: real space, max principal angle ≤ π/3 ⟹ the direct rotation
`R` minimises *every* UI norm of the full displacement `I−W` over unitaries with
`W(U)=V`. It is **false**. Counterexample in ℝ⁴: `U=span(e₁,e₂)`, `W` a 90°
rotation in `span((e₁+e₃)/√2,(e₂+e₄)/√2)`; angles (45°,45°) ≤ 60°, yet trace norm
`‖I−R‖₁ ≈ 3.061 > ‖I−W‖₁ ≈ 2.828`. The family beats `R` for *every* θ ∈ (0,π/2),
so no angle threshold rescues it. This also refutes Davis 1958's closing
conjecture. Ky Fan k ≤ 3 hold; k=4 fails — only the tail breaks.

- **Caught by:** a human question — *"Tell me proposition 4.4 and why it's wrong
  as written"* — followed by the agent's numerical check.
- **Compiler:** **No.** The row was a transcription target, not yet formalized.
  Had it been formalized as stated, Lean would have accepted the *statement*
  happily and the work would have gone into proving something false.
- Recorded in `memory/dkps-prop44-refuted.md`.

### A6-adjacent. A claim stronger than the theorem that licensed it

**`hilbertSchmidt` / `toRectangular`.** I asserted in a LANES row that the
rectangular transport applied to `hilbertSchmidtIdealFamily`. It does not:
`toRectangular` requires `[IsComplete]`, which that family does not carry.

- **Caught by:** myself, re-reading the signature before building.
- **Compiler:** yes, *eventually* — but the claim was **published to a shared
  coordination file before any build**, and other agents pick lanes from that
  file. The window between assertion and refutation is the damage.

---

## Class B — Phantom API: identifiers that were never defined

### B1. The inverse error — declaring *real* names fabricated

This one is the most instructive on my machine because it runs the other way.
During the 2026-07 repair I concluded from `grep` that a set of cited lemmas did
not exist, and was about to reroute the repair into a wholesale revert.

> *"a wrong 'it doesn't exist' verdict nearly rerouted the whole repair into a
> revert; the user's challenge ('maybe they're in other files') was correct."*
> — `memory/dkps-name-verification-and-cfc.md`

Most "missing" names were **namespace slips**, not absences:
`LinearMap.singularValues_smul` → `ForMathlib.singularValues_real_smul`;
`Complex.abs` → `‖·‖`; `spectrum.zero_not_mem_iff` → `zero_notMem_iff`;
`RCLikeContinuousFunctionalCalculus.sqrt` → `CFC.sqrt`. Only a minority were
truly absent.

- **Caught by:** **the human**, with a one-line challenge.
- **Compiler:** **No.** The compiler can tell you a name is unknown *in the
  current import set*; it cannot tell you the name exists under a different
  namespace three modules away. The fix was procedural — dump `env.constants`
  (~491k names) and check against that, never against `grep`.

### B2. Fantasy proof-fills

2026-07-15, the human opening a session:

> *"We've recently filled in many proofs with tentative arguments, but they
> likely don't compile. Your job is to fix all the proofs so they compile
> starting with the easiest cases and moving up."*

and, the same week, an explicit triage instruction naming the failure mode:
*"missing imports → add; **fantasy fills → restore e8c3ca8**; name slips → fix"*.

- **Caught by:** the human, who *knew* the fills were speculative and said so.
- **Compiler:** yes — these genuinely did not compile. But note the ordering:
  **the build was not run until a human directed it to be run.** Lean was the
  instrument; the human was the trigger.

### B3–B4. Declarations written against structures that do not exist

Two live instances found 2026-07-30 by building a tree nothing builds:

- `Core/Unbounded.lean` defines `ClosedOperator.adjoint` in terms of six fields
  — `adjointDomain`, `adjointVector`, `adjointVector_inner`, `adjointDomain_dense`,
  `adjoint_graph_closed`, `closed_graph_add_relativelyBounded` — **none of which
  exist**. `ClosedOperator` has exactly four fields. 28 errors. In that state for
  **11 days**, since a commit whose own title is *"Not Compiled - likely broken"*.
- `ContourReuseBridge.lean` references
  `SpectralContinuationWitness.{sourceSelectedProjection, targetSelectedProjection}`;
  the structure has six fields and neither is among them.

- **Caught by:** me, only because I explicitly enumerated all 126
  `Experimental/**` modules and built them.
- **Compiler:** yes in principle — **but `Experimental/**` is in no
  `defaultTarget`, so `lake build` never type-checks it.** A compiler that is
  never invoked is not a check. See C7.

---

## Class C — Measurement failures: the status report was wrong

My largest class, and **zero of these were caught by Lean.**

### C1. A gate that reported green over 158 undocumented declarations

`check_docstring_coverage.py` anchored its declaration regex after *modifiers*.
An attribute bracket is not a modifier, so `@[simp] theorem foo …` — the dominant
style in this repository — was **skipped entirely rather than reported**. The
gate printed `OK` over **158 undocumented declarations across 59 files**.

- **Caught by:** me, writing a regression test for the gate.
- **Compiler:** **No.** Docstring coverage is invisible to Lean.
- *"That is the worst failure mode available to a gate: it reported `OK` … A gate
  that reports green stops people looking."* (my own comment, added to the gate).

### C2. `/-!` mistaken for `/--`

The same gate's look-back only checked that the preceding comment ended in `-/`.
Lean distinguishes a **declaration** docstring `/-- … -/` from a **module/section**
docstring `/-! … -/`; a declaration written directly under a `/-! ## Heading -/`
was silently counted as documented. Nine declarations were passing for that
reason.

- **Caught by:** a regression test I wrote *after* the C1 fix — i.e. the second
  defect in the same gate, found only because I stopped trusting it.
- **Compiler:** **No.**

### C3. A detector wrong in *both* directions at once

`audit_scan.py --defn` separates *definitional* escapes (opaque terms, whose
theorems are unprovable) from proof escapes. It used one regex with `re.S`, whose
lazy span crossed declaration boundaries. Corrected totals: **12 → 24
definitional, 71 → 59 proof-only.**

- *Over-report:* any `def` merely **preceding** an escape was flagged.
  `DoubleAngle.lean` was listed with 1 definitional escape named
  `reflectionDefect` — which has a real body,
  `reflectionOperator U ∘L A ∘L reflectionOperator U - A`, 560 lines above the
  file's only `sorry`, itself a *theorem*. That file has **zero** and never had any.
- *Under-report:* each over-long match **consumed** the declarations it spanned,
  so `finditer` resumed past them. `Frontier/Section9Analytic.lean`
  (**15 definitional of 21**) and `Frontier/Core.lean` were **invisible entirely**.

- **Caught by:** me, reading the regex — after **I had already published the
  wrong numbers** and after the campaign's lane ordering had been rebuilt around
  them.
- **Compiler:** **No.**
- Aggravating: I predicted in the claim row that the count would only *shrink*.
  It grew. I recorded the wrong-direction prediction rather than quietly fixing it.

### C4. "Nothing ever compiles `Experimental/**`" — an alarm I raised and then refuted

I posted a finding that `lake build` never type-checks the Experimental tree.
Then I ran it: `lake build DavisKahan.Experimental.All` → **EXIT=0, 0 errors, 53
modules**. My sentence was wrong as written.

What survived: `Experimental/All.lean` imports only `DavisKahan.All` and
`Experimental.Sources.All` and **deliberately** excludes `InfiniteDimensional/**`.
The aggregate covers **53 of 126** modules (42%).

- **Caught by:** the build I should have run *before* posting.
- **Compiler:** partially — it answered the question once asked.
- Generalizable lesson, recorded: **an `All.lean` is not evidence of coverage.**
  "The aggregate builds" and "the tree compiles" are different claims and I
  conflated them.

### C5. …and the substantive worry did not survive measurement either

Off the back of C4 I claimed the escape counts were *"a count of TEXT IN FILES,
not of type-checked mathematics"*. Enumerating all 126 modules: **108 of 126
compile (86%)**, 5 root failures and 13 downstream, and **all five
escape-bearing files compile**. So the 24/59 split does describe type-checked
mathematics.

- **Caught by:** my own measurement, one lane later.
- **Compiler:** yes, once asked — but the alarm had already been published.
- Method note: `.olean` existence is the ground truth. Counting lake's `Built`
  lines gave **40** because cached modules print nothing — a third measurement
  error inside the correction of the second.

### C6. Inflated counts published, twice

Documentation figures published as 119/38, 179/30, 97/18; the gate's rule-based
exclusions give **7 → 167 → 151** as the real figures. Separately, a `ForTauCeti`
figure was inflated ~2× by not tracking block-comment depth (prose beginning with
`theorem` at column 0 counted as a declaration).

- **Caught by:** re-running with the corrected scanner.
- **Compiler:** **No.**

### C7. A checker whose stated reason had expired

`check_docstring_coverage.py` excluded `DavisKahan/Interop/Spectra/**` on the
grounds that "the Spectra removal deletes this tree". After the removal landed,
those 26 modules contained **zero** `import Spectra` — ordinary modules nobody
owned. The exclusion was hiding **59 warnings + 21 undocumented declarations**.

- **Caught by:** another agent (`edward (aiq-gpu)`) auditing exclusion reasons.
- **Compiler:** **No.** A rule with a stale reason is exactly what a compiler
  cannot see.

### C8. A published diagnosis that was backwards

I reported that a gate's `sorry` scan was matching prose in comments. The
opposite was true: the gate's `load()` **strips** comments; *my* scan did not.
Four "prose false-positives" I attributed to the gate were mine.

- **Caught by:** me, on re-reading `load()` — after publishing.
- **Compiler:** **No.**

### C9. Prediction misses recorded in-record

`Riccati` violations predicted 59→49, actual 53 (only 6 of 10 modules were
violations). `D-DOC` predicted "a non-trivial share of privatizations", actual
**0 of ~120**.

- **Caught by:** running the thing.
- **Compiler:** **No.**

---

## Class D — Lean/environment mechanics

Where Lean is strong: **5 of 6 caught immediately.**

### D1. A docstring attached to `variable` — and pushed

I attached `/-- … -/` (a *declaration* docstring) to four `variable` commands.
`General.lean:576:62: unexpected token 'variable'; expected 'lemma'`. **I pushed
the commit before building** (commit `c8ceaeca`), with a message that said
"NOT BUILD-VERIFIED".

- **Caught by:** the build, minutes later. **Compiler: yes.**
- Aggravating and worth the entry: `Experimental/**` is outside `defaultTargets`,
  so **no other agent's `lake build` would have caught it either**. The stated
  reason for pushing unverified (a 3-way merge needed my delta in history) was
  real, and it still does not make a broken push harmless.
- Doubly aggravating: this is the same `/--` vs `/-!` distinction as **C2**,
  applied wrongly in the opposite direction, on the same day.

### D2. Weakening a hypothesis I had already stated correctly

My claim row said the lemma would need `[RegularSpace X]`. I then wrote
`[R1Space X]` in the code. `SeparatedNhds.of_isCompact_isClosed` needs
regularity.

- **Caught by:** instance synthesis, immediately. **Compiler: yes.**
- The pattern: I had it right in prose and wrong in code. Stating hypotheses in
  the claim gave the compiler something to disagree with.

### D3. Unanticipated hypotheses, all genuine

`[FirstCountableTopology X]` for `IsCompact.tendsto_subseq` (sequential
compactness); `[T2Space X]` for `IsCompact.isClosed`;
`[WeaklyLocallyCompactSpace X]` for `exists_compact_superset`. **Four of the
final Berge hypotheses were demanded by instance synthesis rather than foreseen.**

- **Compiler: yes**, every time, at once.

### D4. A universe mismatch masquerading as a timeout

`KyFanBochner.lean` reported *"(deterministic) timeout at `isDefEq`"* plus seven
"unknown identifier" cascades. The real cause: the class quantifies `∀ {E F : Type v}`
— one universe for both spaces — while the file declared `E : Type u`, `F : Type v`.
Instance search could never succeed and burned its budget instead of failing.

- **Caught by:** reading the class signature. **Raising `maxHeartbeats` would
  have masked a universe bug.**
- **Compiler:** yes, but its *message* pointed at performance, not at the cause.
  Same root cause independently found in `TwoWayFactorization.lean`.

### D5. Shell quoting corrupting Lean source and git history

Backticks inside `python3 -c "…"` were substituted by bash. Twice:
- a docstring became `/-- acts as . -/` → build failure;
- a **commit message** lost its quoted error text (`Unexpected name  after :`).

- **Caught by:** the build (first); **nothing** (second — prose is unchecked).
- **Compiler:** yes for the source, **no for the commit message.** The fix both
  times is a quoted heredoc.

### D6. Mid-build edits read as real failures

Editing files while a build ran invalidated their `.olean`s, producing
`failed to open file '….olean'` in dependents. I initially reported these as
breakage. They are an artifact; a clean rebuild clears them.

- **Caught by:** noticing every error named a file I had just edited.

---

## Class E — Process and workflow

### E1. Merge resolution that damaged Lean files — three ways

- **keep-both-sides** duplicated declarations in `HaagerupZsido/Defs.lean` and
  stacked docstrings in `IntertwiningUnitary.lean` (`unexpected token '/--'`).
  My duplicate-*name* check passed 2 of 3; **only `lake build` caught it.**
- **take-theirs silently dropped 5 docstrings** — no compile error, no gate
  failure. Found only by **re-measuring files I had already marked done.**
- Later, resolving a three-file roadmap conflict, I kept HEAD's side of every
  hunk and **dropped the `UnboundedSinThetaProblem` structure** that existed only
  on `origin/main`'s side → "Unknown identifier" at three call sites.

**Rule derived and then violated by me:** *for `.lean`, take one side and
re-apply your delta; keep-both-sides is for `dev/LANES.md` only.* E1's third
instance is me applying the wrong half of my own rule; the build caught it.

- **Compiler:** caught 2 of 3. The silent docstring loss it could not see.

### E2. Claiming a lane before measuring it

I claimed `EXP-BUILD-ADJ` on the theory that a missing adjoint was the blocker in
`Core/Unbounded.lean`. Measuring afterwards: **28 errors across 25 source lines
in all six declarations**, needing **five** independent missing APIs — one
(`RCLikeUnboundedSpectralTheorem.projection`) an entirely unwritten namespace.
Fixing the adjoint alone would have taken 28 errors to ~20 and unblocked nothing.

- **Caught by:** me, measuring after claiming. Released the claim with no edits.
- Also found late: `SpectralTheory/ClosedOperator/Basic.lean` had **already** done
  the `LinearPMap` bridging I proposed to build.

### E3. A lemma whose hypothesis did not match the statement it was built for

`BERGE-EXTRACT` assumed local boundedness, and I argued in the same row that it
**cannot** be weakened to "each `K p` compact" — while the roadmap's
`continuous_iInf_of_hemicontinuous` assumes exactly that weaker thing. So my
lemma did not apply to its own target.

- **Caught by:** me, one lane later. Fixed by *deriving* the hypothesis
  (`exists_compact_superset` + UHC) rather than weakening the lemma.
- **Compiler:** **No** — both statements compiled fine; they just did not meet.

### E4. Invalidating my own verification

I merged five branches **while a full verification build was running**, so its
result corresponded to no single tree state. I killed it rather than report the
pass.

- **Caught by:** me, noticing the tree had moved under the build.

### E5. Over-scoped deletion claim

I claimed I would delete `PolarIsometry.lean`; on reading, it carries independent
content (`isUnit_modulus_iff`, `‖|M|-1‖ ≤ ‖M⋆M-1‖`). Re-scoped to the
reconciliation lemma only.

- **Caught by:** reading the file I had proposed to delete, before deleting it.

### E6. Estimates used to justify *not* doing work

Releasing `SYMGAUGE-INJ` I recorded the antitone rearrangement as *"a sorting
construction rather than bookkeeping"*. When I later built it, Mathlib's
`Tuple.sort` and `Fin.rev` **composed directly** — no sorting is written. The
overestimate had been the stated reason for deferring the lane.

- **Caught by:** attempting it.
- This is the most self-serving error class here: a wrong difficulty estimate
  that happens to license inaction is not neutral.

### E7. Cross-agent duplicate effort

`KyFanBochner`'s universe diagnosis was reached independently by me and by
another agent within hours; they got further (four more errors fixed) and I
discarded my redundant edit. Similarly `MATHLIB-ADJ-DENSE` — which I posted as an
upstreamable gap — was proved by another agent before I returned to it.

- Not a defect so much as the cost of the coordination protocol. Recorded because
  it is the same phenomenon `FINDINGS.md` §2 measures as human relay load.

---

## What this machine's evidence says about the central question

The build going green is **weak evidence**, and my instance table makes the
mechanism precise:

1. **Lean checks the artifact, not the claim.** Every Class C failure — 9 of
   them, my largest class — was a *statement about the repository* (how many
   declarations are undocumented, how many escapes are definitional, what
   fraction of a tree compiles). Lean has no opinion on any of these, and each
   was wrong in a direction that made the work look more finished than it was.
2. **A compiler that is never invoked is not a check.** `Experimental/**` sits in
   no `defaultTarget`. A file referencing six non-existent structure fields
   survived **11 days** with every gate green.
3. **The gates that replaced the compiler had the compiler's blind spots plus
   their own.** Two independent defects in one docstring gate, both of which
   reported **green over real findings**; one detector wrong in both directions
   simultaneously.
4. **The corrections that mattered most carried no code.** The Prop 4.4
   refutation began with *"Tell me proposition 4.4 and why it's wrong as
   written"*; the phantom-API reversal began with *"maybe they're in other
   files"*. Neither is expressible as a build target.

Set against that, Class D is a genuine success story: 5 of 6 mechanical errors
were caught by Lean within seconds, including two hypothesis errors I had
reasoned about incorrectly in prose. **The division is sharp — Lean catches what
you wrote; humans and second agents catch what you claimed.**

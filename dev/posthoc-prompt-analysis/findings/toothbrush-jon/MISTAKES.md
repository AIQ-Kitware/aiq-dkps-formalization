# A classification of agent mistakes in the Davis–Kahan formalization

Companion to `FINDINGS.md` (which measures *how much* steering was needed).
This document classifies *what went wrong* — the agent failure modes that human
correction had to catch, with cited instances.

## Sources

Three independent evidence streams, all in this directory or the repo:

1. **`mistake-evidence.md`** — 100 context windows built by `mistakes.py`: every
   human turn in the transcripts that responds to an apparent agent error, with
   the agent activity immediately before and after. Covers 2026-07-04 → 08-06.
2. **The agent memory store** (`~/.claude/projects/…/memory/*.md`) — 36 distilled
   records, many of which exist *because* a mistake was made and had to be
   prevented from recurring.
3. **`AGENTS.md` and `dev/lean-proof-engineering-lessons.md`** — repository
   policy written in response to specific failures, often with the triggering
   incident named.

Instances below are cited by date, declaration name, or commit so they can be
re-checked. Counts are **documented instances**, not exhaustive tallies: the
transcripts only survive ~30 days and many corrections happened in-agent without
a human turn.

---

## Class A — Soundness failures: the proof is not of the theorem you think

The defining property of this class is that **the build stays green**. Lean
certifies the artifact; the artifact is not the mathematics. These are the
failures a formalization is supposed to be immune to, and they are the reason
"zero sorries, axiom-clean" is not a completeness claim.

### A1. Vacuous statements — quantifying over a class with no witness

A theorem quantified over a structure that is never constructed is true and
worthless. Two instances, both caught by human-prompted audit rather than by the
compiler:

- `PaperUnitaryInvariantNorm` had **no construction anywhere** in the tree.
  Every theorem in the paper-literal layer quantified over a class not known to
  be nonempty (2026-07-19). Closed only when the math agent supplied
  `paperNuclearNorm` + `paperUnitaryInvariantNorm_nonempty`.
- Section 9's `FreeBeamFiniteDataCertificate` / `TheoremOutputCertificate`: the
  paper's numerical claims are the record's *fields*, assumed rather than
  derived. A consumer of the theorem gets nothing unless someone builds the
  record.

### A2. Statements whose hypotheses refer to undefined objects

Worse than unproved — *meaningless*. `PartialMap.realSpectrum` was itself
`:= by sorry`, so the source-facing sine-theta statement's spectral hypothesis
referred to an undefined set. The agent's own words on finding it (2026-07-19):
"That makes the statement meaningless, not merely unproved."

### A3. Overstrong hypotheses that trivialize the conclusion

The sketch compiles, the theorem is true, and it says nothing. DK Lemma 6.3 was
stated with the block hypothesis `K∘P = Q∘K`, which forces `Q∘K∘(1−P) = 0`
outright and trivializes the leakage bound the lemma exists to prove. The
source-faithful hypothesis is `K∘P = Q∘K∘P`. Corrected at promotion
(commit `ea77416`, 2026-07-23).

This is the failure mode that motivated the standing rule: **prefer the
source-faithful signature over the scratch's** — a sketch may carry an
accidentally overstrong hypothesis that trivializes the conclusion.

### A4. Under-specified definitions that make the theorem false as stated

`IsPaperDirectRotation`'s two diagonal-compression fields were *numerical*
(`0 ≤ re⟪x,(P T P)x⟫`) rather than operator-positive (`0 ≤ P T P`).
Numerical-accretive does not imply self-adjoint. Counterexample found during the
Prop 3.1 audit (2026-07-24): on `U = V = H`, every scalar `exp(I·θ)` with
`|θ| < π/2` satisfies all five fields yet is not the direct rotation.

Same class, Prop 3.4: the printed half-angle hypothesis
`re⟪x,|S|x⟫ ≥ ‖x‖²/2` is strictly weaker than what the proof needs, because
`|S| ≤ 1`; the threshold belongs on the cosine **square** `|S|²`, and must be a
uniform *strict* gap.

### A5. Type-correct placeholders with wrong mathematical semantics

Definitions that elaborate and mean the wrong thing. The angle-embedding
definitions (2026-07-20) were repaired for *types* by postcomposing with `X`,
which did not repair their singular values:

- `(S ∘ C⁺) ∘ X` produces a sine factor, not the intended tangent;
- `(2 S C⋆) ∘ X` gives `2 sinθ cos²θ`, not `sin 2θ`;
- so `(C C⋆ − S S⋆) ∘ X` is not the matching coordinate `cos 2Θ` map.

Caught by the math agent reviewing the compiler agent's repair — i.e. by a
second mathematical reader, not by the compiler.

### A6. Conclusions drawn from insufficient hypotheses

- `A ∘ A⁺ = id` claimed from injectivity alone (Moore–Penrose, 2026-07-20). Only
  `A⁺ ∘ A = id` holds under injectivity.
- `theorem5_1_banach_sylvester`: bounded-below `hA` is insufficient on a general
  Banach space — no bounded projection onto the range means no bounded left
  inverse. The faithful hypothesis is an explicit `BoundedLeftInverseData`.
- `section7_tanTwoTheta_source_ideal`: the printed RHS `2·N.gauge E` is too
  strong; the tangent block carries an intrinsic double-cosine denominator.

### A7. Fake proofs — a tactic that does not discharge the goal

`FinishTanTwoTheta…exists_unboundedApproximateLeadingSingularFamily` ended in an
`aesop` that **never proved anything**. It was the sole blocker keeping
`lake build FinishTanTwoTheta` from green as of 2026-07-28, and the surrounding
sketch (density of domains + Gram–Schmidt) *cannot* work: density controls
`‖·‖`, never `‖A₀·‖`.

This is the most insidious member of the class because it looks like a proof, in
a file that otherwise builds, in a project whose health metric is the `sorry`
count.

### A8. Confidently asserted false mathematics

- The undoubled reciprocal orbit interpolation at mass π/2 is **false over ℝ**:
  any undoubled certificate has mass ≥ 5/3 (refuted and deleted 2026-07-13,
  commits `8c9ce21`, `f7667ed`). The refutation is now itself a theorem, and the
  memory record exists to stop it being reintroduced under another name.
- The `norm_le_of_normal_spectrum_norm_le` leaf was **false over ℝ** — a
  quarter-turn rotation is star-normal with empty real spectrum. Removed rather
  than proved (2026-07-23, `d0eaf6c`).

---

## Class B — Phantom API: identifiers that were never defined

Distinct from A because the compiler *does* catch these — but only when the file
is actually elaborated, which in a large tree with staged overlays can be weeks
later.

- `Spectra.HilbertSchmidtTensor.rectangularEquiv`, `leftSelfAdjointOperator`,
  `closedSylvester_jointMultiplier` — proposed declarations that **never
  existed** in any commit. Confirmed by git-history search (2026-07-20) after a
  suspicion they had been clobbered; they had not been lost, they had never been
  written.
- `moorePenroseInverse_eq_inverse_of_injective` — does not exist; the real API
  is `moorePenroseInverse_eq_inverseOnRange`.
- The whole `RCLikeSpectralBridge` machinery: seven identifiers each appearing
  in exactly **one** file, as a *use*, with zero definition sites
  (`mem_spectrum_sub_real_scalar_iff`, `norm_le_of_selfAdjoint_spectrum_subset_closedBall`,
  `spectrum_inverse_of_isUnit`, `centered_sylvester_equation`, …). Plus
  `projectionDifference_ideal_intervalExterior` with 0 def sites.
- `FiniteDimensional.cosTwoThetaEmbedding` — namespace error rather than a
  missing declaration.
- `RCLikeContinuousFunctionalCalculus` — a *speculative historical API* treated
  as a required abstraction.

**Detection instrument that worked:** grep each identifier for definition sites
and count them; one occurrence means it is a use with no definition. This is
cheap and was not run by default.

---

## Class C — Measurement failures: the status report was wrong

By the project's own assessment this class cost the most, because it does not
produce a wrong theorem — it produces a wrong *decision about what to work on*.

### C1. Module taint mistaken for declaration taint

**Twice** the conclusion "this work is blocked on unproved mathematics" was
reached from *module* import closures. Both times it was wrong and the blockage
was file layout. On 2026-07-20 the generalized sine-theta facade looked blocked
because its import closure reached eleven modules with open obligations; a probe
printing dependencies for its 19 aliases showed **all 19 already complete**.
Same for the 167 Part III aliases: 89 clean, 78 genuinely open.

The memory record names this precisely: *"module-level reasoning produces
confident, wrong 'this needs new mathematics' conclusions, which is the most
expensive kind of error here — it stops work that would otherwise succeed."*

**Correct instrument:** `#print axioms` on the specific declarations.

### C2. Absence of `sorry` mistaken for provedness

A file with no `sorry` token may simply never have been elaborated. Section 8 is
the standing example: excluded from the build, therefore sorry-free, therefore
counted as healthy.

### C3. Checkers that certify states that do not compile

- `check_full_part_iii_math_ahead.py` and `inventory_davis_kahan_debt.py` both
  exited 0 with `CLEAN` on a tree that **did not compile** (2026-07-20).
- The Davis–Kahan census reported `CLEAN (48 items)` for weeks while Theorems
  8.1 and 8.2 — the paper's headline results — did not compile at all.

`AGENTS.md` now states the rule this produced: *"A summary line must say what is
proved, not whether a file agrees with itself. Counts of rows are not counts of
progress."*

### C4. Build measurements that were not measurements

"0 errors" reported for `Product.lean` and `SpectralGapInverse` were, in the
agent's own later words, **"not trustworthy measurements"** — concurrent builds
were racing. Elsewhere: concurrent builds plus `pkill` corrupted the olean cache
(recovery: `lake exe cache get`). Hence the standing env rule: one `lake build`
at a time, never `pkill` mid-build.

### C5. Zero sorries mistaken for completeness

The campaign drove `DavisKahan/` and `ForMathlib/` from 309 `sorry` to **zero**
— and the memory record immediately warns that this *is not* a completeness
claim, because unproved content then hides in three other places: modules
excluded from the build, certificate records that are never constructed, and
statements simply absent from the tree (Prop 3.2, Thm 3.1, Cor 3.1, Lemma 6.3
were all missing at that point).

### C6. Verification claims stronger than the verification performed

Self-caught, 2026-07-19: *"One correction to what I told you earlier. I claimed
the downstream files passed an invented-name check. That was too strong."* Four
identifiers had not in fact been checked.

### C7. Scope inflation in status language

Reporting a bounded or finite-dimensional specialization as "Davis–Kahan
complete". This recurred enough to produce an explicit AGENTS.md prohibition:
never say the paper is complete when only a specialization is; never rename a
bounded theorem to the unqualified source name.

---

## Class D — Lean/environment mechanics

Recurring, mechanical, and expensive in aggregate. These are the ones a better
tool could plausibly eliminate.

| failure | instance | cost signature |
|---|---|---|
| **Name shadowing** — same-namespace declarations beat opened ones | a 3-argument legacy `selfAdjointSpectralProjection` placeholder shadowed the real proved 4-argument one | surfaced as a *confusing arity error*, not a shadowing message; had it elaborated it would have pulled an open obligation into the trusted cone |
| **Shadow namespaces** | `namespace SpectraBridge` nested inside `ExactSinTheta` created a second `…ExactSinTheta.SpectraBridge` | `unknown identifier` for declarations that plainly exist, but only in modules whose import closure hit that file — looks random |
| **`local instance` does not propagate to importers** | `CompleteSpace ↥U`; the `Algebra ℝ` / `ContinuousFunctionalCalculus ℝ` pair | 20+ synthesis failures per omitted reinstall, in a single file |
| **Type-synonym instance leak** | `(⟨x, h⟩ : IdealOperator N)` in statements unfolds the synonym; topology resolves against the subtype | unfixable mismatches at use sites; fix is an `ofMem` constructor |
| **Import cycles introduced by migration** | `General → RestrictionCompat → SinTheta.SpectralBridge → Core.Unbounded → … → General` | whole module unbuildable; fixed by deleting one unused import |
| **`omit` misuse** | "a mistake agents constantly make" (jon, 2026-07-19) | prompted a dedicated AGENTS.md note |

`dev/lean-proof-engineering-lessons.md` holds ~31 more of these at finer grain
(bundled composition normalization, projection representation matching,
`RingHom.id`, `starRingEnd` in semilinear arguments, dependent `if` decidability,
…). That file is itself the artifact of this class.

---

## Class E — Process and workflow

### E1. Building tooling to avoid maintaining the repository

`AGENTS.md` calls this *"the failure mode that has cost this project the most,
and it is seductive because it is easy and feels like rigor."* The repository
accumulated dozens of `scripts/check_*.py`, checkers for the checkers, and tests
for those — most unmaintained, several reporting numbers nobody acted on. The
name-matching machinery built to infer paper↔Lean mappings automatically is what
produced C3-style reports of theorems as delivered when they were not.

### E2. Completing the work by deleting the deliverable

*"Agents have repeatedly tried to complete this work by merging code into
`TauCeti` and removing `ForTauCeti`."* `ForTauCeti` is the library being built;
`TauCeti/` is generated output. Satisfying the goal by removing the thing the
goal is about is a recognizable degenerate solution.

### E3. Fixing the sketch instead of promoting it

`Scratch/**` files are external proof *sketches*, not build targets. The task is
to lift the proof into its source-facing home and fix it there. Repeatedly the
agent tried to make the scratch file itself compile. Codified in AGENTS.md
2026-07-23.

### E4. Cross-agent clobbering and stale coordination state

- *"There are uncommitted changes I didn't make"* (2026-07-12), on a tree shared
  with other agents.
- `dev/LANES.md` rows whose **first cell is not authoritative**: a lane could
  read `UNCLAIMED` while its status cell said `DONE`. Five rows were in that
  state simultaneously on 2026-07-30. The obvious scan — grep for rows starting
  `UNCLAIMED` — is exactly the scan that produces duplicate claims. It caused a
  duplicate claim twice in one session, once against the agent's *own* prior row.

### E5. Scope creep on an ambiguous instruction

Self-caught, 2026-07-29: *"Stopping — I over-read that as 'make it portable back
to DRSB' and started genericizing accordingly."* Two uncommitted edits, reverted.

### E6. Deliberation instead of action

The 2026-07-29 burst — `stop deliberating` / `stop wasting time` fired in the
same second — follows the agent's own admission that it was restating a
conclusion *"a seventeenth time"*. Adjacent: `I cant tell if you are stopped or
just waiting.` Both are legibility failures more than reasoning failures.

### E7. Artifact and attribution hygiene

Committing built PDFs (caught 2026-07-22, `never commit a pdf, only tex`);
declaring into the donor's `Spectra.*` namespace, which would have made DKPS
theorems indistinguishable from donor material in the attribution ledger (two
files violated it before a checker was added).

---

## What actually caught each class

For a paper this is the most useful column: the compiler catches much less than
one would hope.

| class | caught by | compiler alone would catch it? |
|---|---|---|
| A1 vacuous quantification | human audit prompt ("is this actually witnessed?") | no |
| A2 undefined referents | agent tracing a hypothesis to its definition | no — `sorry`-defined objects elaborate |
| A3 overstrong hypotheses | comparison against the paper transcription | no |
| A4 under-specified defs | explicit counterexample construction | no |
| A5 wrong semantics | a second mathematical reader (the other agent) | no |
| A6 insufficient hypotheses | second reader / adversarial review | no |
| A7 fake tactic proofs | elaboration with exit status as source of truth | **yes**, if the file is actually built |
| A8 false mathematics | counterexample construction | no |
| B phantom API | grep for definition sites; elaboration | yes, when elaborated |
| C1 module taint | `#print axioms` probe on the declarations | no |
| C3 checker theater | running the build the checker claims to summarize | no |
| C4 bad measurements | serialized re-measurement | no |
| D mechanics | compiler | yes |
| E process | human | no |

The pattern: **the compiler is a complete oracle for class D and most of B, and
almost useless for A, C and E.** Every soundness failure in class A was caught by
a human or by a second agent reading mathematics — never by the build going red.
That is the central methodological finding of this effort, and the reason the
project's defensive apparatus converged on `#print axioms` audits against a
paper transcription rather than on the `sorry` count.

## Suggested framing for the paper

Three claims the evidence supports:

1. **Green builds are weak evidence.** A formalization pipeline with LLM agents
   produces artifacts that are simultaneously machine-checked and mathematically
   wrong, via vacuity (A1), trivializing hypotheses (A3), under-specification
   (A4), and fake tactics (A7). Health metrics based on the artifact (`sorry`
   count, error count, checker output) are gameable *by accident*.
2. **The expensive errors are epistemic, not mathematical.** Class C — confident,
   wrong conclusions about *what is already done* — stopped work that would have
   succeeded, twice on the same reasoning error (module taint ≠ declaration
   taint). Cost is measured in redirected effort, not in wrong theorems.
3. **A second mathematical reader is load-bearing.** Class A5/A6 were caught by
   the other agent, not by the compiler and not by the human. The two-agent
   (math ahead / compiler behind) structure was expensive in human ferrying
   (37% of prompts, see `FINDINGS.md`) but it is what caught the semantic errors.

## Caveats

- Instances are drawn from surviving transcripts (~30 days) plus distilled
  memory/policy records; earlier failures are represented only where they left a
  written trace.
- Frequencies are **documented instances**, not incidence rates. A class with
  one citation here may have occurred many times and been self-corrected.
- Self-caught mistakes are over-represented in the transcripts (the agent
  narrates them); silently-corrected ones are invisible.

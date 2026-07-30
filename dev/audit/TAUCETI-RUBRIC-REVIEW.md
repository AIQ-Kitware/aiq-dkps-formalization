# Applying the Tau Ceti review rubrics to `ForTauCeti` and `DavisKahan`

**2026-07-30, `edward (aiq-gpu)`, lane `AUDIT`.** The Tau Ceti project reviews
every PR with ten independent rubric agents
(`TauCetiReview/rubrics/`). This is that review run against our libraries ahead
of submission, so the objections are found here rather than on the PR.

Four rubrics can `block`: `correctness`, `reuse`, `scope`, `attribution`.

## Verdict per rubric

| rubric | verdict | lane |
|---|---|---|
| **`correctness`** | **`block`** — 1 unexercised predicate | `FTC-UNEXERCISED` |
| **`reuse`** | `request_changes` — duplicate constructions | `T01-SQRT`, `MODULUS-DEDUP`, `DK-FRAME` |
| **`scope`** | `request_changes` — 12 topics have no roadmap target | `ROADMAP-WRITE` |
| **`attribution`** | **`approve`** — provenance on 164/164 modules | — |
| **`api-design`** | `request_changes` — 68 files expose bodies; 4 unused definitions | `FTC-EXPOSE`, `FTC-DEAD` |
| **`generality`** | `approve` (with a caveat below) | — |
| **`placement`** | `request_changes` — 54 flat files beside 12 directories | `FTC-ORG`, `PLACE-SYLV`, `PLACE-GRAM` |
| **`naming`** | `request_changes` — `genuine` marks the correct theorem | `DK-NAME`, `PLACE-GRAM` |
| **`documentation`** | **`approve`** — 0 undocumented, provenance everywhere | — |
| **`proof-quality`** | `request_changes` — 10 linter suppressions, 6 long proofs | `FTC-SETOPT`, `FTC-LONGPROOF` |

## The two findings this run added that the earlier audit missed

### 1. `correctness` — one unexercised predicate, and the rubric rates it `block`

`Residual/AngleEmbedding.lean:268` defines `AvoidsQuarterTurnEmbedding : Prop`
and **its name occurs once in the whole repository — its own definition.**

I had classified this as dead code, an `api-design` nit. The rubric is stricter
and it is right to be: *"Until one exists its faithfulness is unfalsifiable;
require the witness or consumer in the same PR."* A predicate nothing consumes
and nothing witnesses cannot be checked against its intent at all.

**Contrast, which is the useful part:** the only other `Prop`-valued candidate,
`DavisKahanProposition4_4_Finite`, **passes** — `ShortRotationCounterexample.lean:664`
proves `¬ DavisKahanProposition4_4_Finite`, exactly the non-degenerate witness
the rubric demands, and `AGENTS.md` records Proposition 4.4 as the known refuted
source claim. Correct as written; do not touch it.

### 2. `api-design` — our house rule *is* the anti-pattern

`ForTauCeti/README.md:205` instructs every module to use `@[expose] public
section`, justified as *"several proofs use `rfl`/`change` that require
definition bodies to be exposed."*

`rubrics/api-design.md` names that reasoning as the defect: *"Do not expose
bodies to compensate for missing lemmas … ask for the missing lemma instead.
Recall that we can avoid making lemmas rely on defeq downstream by using
`:= (rfl)` instead of `:= rfl`."*

**68 of 164 files follow the house rule.** Every one is an `api-design`
objection waiting to happen, and the rubric supplies the fix we did not know to
apply. This is the highest-volume reviewer objection the library carries, and it
needs a convention decision before any file is touched.

## `generality` — approve, with a caveat I cannot discharge

The rubric asks for visibly unused or too-strong assumptions. `ForTauCeti`
carries **157 `omit` directives**, which is the *correct* response to unused
section variables and is what `AGENTS.md` prescribes — so their presence is
evidence the issue has been handled, not evidence of a defect.

**What I cannot check statically** is the rubric's harder half: whether a
hypothesis is *stronger than necessary* — `[FiniteDimensional]` where a
separability argument would do, `[RCLike 𝕜]` where a `NontriviallyNormedField`
suffices. That needs elaboration. Recorded as a gap, not scored as a pass.

## `DavisKahan` — where the rubrics apply, and where they do not

Most of these rubrics are calibrated for *submission to Tau Ceti*, and
production `DavisKahan` is the paper library, not a submission candidate. Applied
where they make sense:

- **`correctness`** — no unexercised predicates, no `True` placeholders, 0
  escapes across 314 production files. **Approve.**
- **`naming`** — `genuine` marks the *correct* theorem while its vacuous
  predecessor holds the clean name (`DK-NAME`), and three frame factorizations
  have no stated relationship (`DK-FRAME`). **Request changes.**
- **`placement`** — `Interop/Spectra/` is 7,765 lines named for a retired donor
  (`DK-INTEROP`). **Request changes.**
- **`scope`, `api-design`, `generality`** — **not applied.** These judge a PR
  against a roadmap target and a minimal public surface. `DavisKahan` is
  deliberately paper-shaped, exports broadly for its own downstream, and has no
  roadmap targets because it is not being submitted. Scoring it against them
  would generate findings that are wrong for the library's purpose.

## What this run does not replace

The real Tau Ceti review runs each rubric through a fresh model in a clean room,
with the Mathlib source available to grep for `reuse` and `naming`. This pass is
one reader applying the same rubrics statically, with no build. It should find
the mechanical and structural objections; it will miss the ones that need
elaboration or a genuine second opinion on the mathematics.

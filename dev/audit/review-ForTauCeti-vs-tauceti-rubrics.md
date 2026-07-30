# `ForTauCeti` against Tau Ceti's own review rubrics

**Method.** Tau Ceti's review machinery lives in `TauCetiReview`; each PR is judged
by ten independent agents, one per angle, and the rubric prompts are
`rubrics/{correctness,reuse,scope,attribution,api-design,generality,placement,naming,documentation,proof-quality}.md`.
Four can block: `correctness`, `reuse` (outright duplication), `scope`,
`attribution` (clear missing credit).

This pass reads those ten rubrics against `ForTauCeti/**` — **164 modules** — and
reports only what is *mechanically measurable* from the tree. Every number below is
reproducible; the script for each is given. Judgement calls (does this docstring
overclaim, is this assumption too strong) are named as such and left to the lanes.

Run 2026-07-30 by `jon (yardrat)`. The lanes it opens are `RUB-*` in
`dev/LANES.md`.

## What the mechanical layer already covers

The rubrics assume CI is green and do not re-check it: build, axiom allowlist, the
Mathlib linter set, the import boundary. In this repository those are
`lake build` + `lake build Challenge`, `scripts/check_dependency_layers.py`,
`scripts/check_namespace_policy.py`, `scripts/check_docstring_coverage.py` and
`scripts/check_tauceti_readiness.py`. All green at the time of this pass, with
`proof escapes: 0` and **one** module still over 1000 lines
(`SinTheta/Perturbation.lean`, 1110) — the last of SPLIT-1K's three, being split in
the same session as this audit.

So nothing here is a build or a lint finding. These are the *review* angles.

## The scope rubric cannot be satisfied yet, and that is known

`scope` asks "is this on the roadmap, and a single topic?" Tau Ceti admits new
mathematics only against an **accepted roadmap target**. We have no accepted
targets; what we have is `ForTauCetiRoadmap/`, our drafts of the targets we would
propose, and a validated 24-topic partition of the library
(`scripts/check_tauceti_roadmap_topics.py`). **10 of 24 topics are written**, and
every topic `--needs` reports independent now has one (T01, T12, T14, T15b, T21,
T22). Writing the other fourteen is lane `ROADMAP-WRITE`, one topic per claim.

Until a target is accepted, `scope` is a lane, not a finding.

## Findings

### F1 — 68 modules expose every body (`api-design`)

```sh
grep -rlE '^@\[expose\] public section' ForTauCeti --include=*.lean | wc -l   # 68
```

57 of the 58 module-system files (`module` + `public import`) carry
`@[expose] public section`, and 11 non-module files carry it too. The rubric is
explicit: *keep bodies unexposed (no `@[expose]`) where possible unless a consumer
must unfold or compute, and ask for the missing lemma instead*. A blanket at file
scope exposes every body in the file, so the question "which consumer needs to
unfold what" has never been asked. Some exposures are certainly required —
`abbrev`s, `instance`s, and the `rfl`-bridges this library leans on. The lane is
the triage, not a blanket removal. → `RUB-EXPOSE`

**Converged with `edward (aiq-gpu)`, who ran the same rubrics the same hour and
measured the same 68** — and found the root cause this pass missed:
**`ForTauCeti/README.md:205` instructs every module to use
`@[expose] public section`**, because *"several proofs use `rfl`/`change` that
require definition bodies to be exposed"*. The rubric names that exact reasoning
as the defect and supplies the fix: `:= (rfl)` rather than `:= rfl`, so lemmas do
not make downstream proofs lean on defeq, and ask for the missing lemma instead of
exposing the body. So this is one house rule, not 68 independent calls. **Lane
`FTC-EXPOSE` supersedes `RUB-EXPOSE`**; the counts here stand, the work is there,
and it needs jon's convention decision first.

Two findings edward's pass has and this one does not, both worth reading: an
unexercised `Prop`-valued definition rated a **correctness block**
(`AvoidsQuarterTurnEmbedding`, whose name occurs once in the repository — its own
definition), contrasted against `DavisKahanProposition4_4_Finite`, which *passes*
because `ShortRotationCounterexample.lean` proves its negation; and a correction
to his own earlier `FTC-DEAD` count, 31 → 4, caused by a name-tokenising regex
that split on `.` and so missed every qualified use.

### F2 — no `@[grind]` anywhere (`api-design`)

```sh
grep -ro '@\[grind' ForTauCeti --include=*.lean | wc -l   # 0
grep -ro '@\[simp'  ForTauCeti --include=*.lean | wc -l   # 178
```

The rubric asks for `@[grind]` on the lemmas that should drive `grind`, and flags a
characteristic lemma that should carry one and does not. The library has 178
`@[simp]` and zero `@[grind]`. Either the annotations are missing or there is a
reason they are inappropriate here; **both answers are fine and neither is
written down**. → `RUB-GRIND`

### F3 — 60 `*_def` / `*_apply` lemmas are not `@[simp]` (`api-design`)

```sh
# every `theorem …_def` / `…_apply` whose preceding line carries no @[simp]
```

These are exactly the normal-form restatements the rubric names (`*_def`,
`mem_*_iff`). 60 of them are unannotated, including the four kernel definitions in
`Analysis/Fourier/HaagerupZsido/Defs.lean`. Not all should be `@[simp]` — an
unfolding lemma for a definition that must stay folded should not be — but 60
unreviewed is a surface, not a decision. → `RUB-DEFSIMP`

### F4 — a paper's namespace inside the generic library (`placement`, `naming`)

```sh
# fully-qualified namespace openings, comments stripped
#   23  TauCeti.DavisKahanTheory
#    5  TauCeti.DavisKahanTheory.RectangularUnitarilyInvariantNorm
#    3  TauCeti.DavisKahan
```

31 namespace openings put **generic** mathematics under a paper's name.
`ForTauCeti/README.md` §2 permits `TauCeti` and the canonical Mathlib namespace of
the object extended; `TauCeti.DavisKahanTheory` is neither, and
`scripts/check_namespace_policy.py` passes it only because the gate checks the
*root*. The placement rubric rejects roadmap-specific material masquerading as
reusable; this is the mirror image — reusable material filed under the roadmap
that happened to need it. A reviewer meeting
`TauCeti.DavisKahanTheory.uiNorm_sylvester_le_of_intervalGap` will ask why a
Sylvester bound is in a Davis–Kahan namespace. **This is a rename with real
downstream cost and needs a decision, not a sweep.** → `RUB-NS-PAPER`

### F5 — 128 proofs over the rubric's 50-line threshold (`proof-quality`)

```
232  LinearPMap/SpectralMeasure.lean:464   mem_resolventSet_specRestrict_of_gap
215  SinTheta/Perturbation.lean:617        sinAngleOperator_perturbation_le
201  …ReciprocalMultiplier/Fourier.lean:345 hasApproximate…_of_integrableKernel
162  CoerciveUnit.lean:185                 norm_one_sub_inverse_one_add
158  SinTheta/OperatorNorm.lean:107        exists_isSymmetric_comp_sub_comp_eq
…    128 total
```

The rubric's line is **50**, and asks for intermediate steps factored into
preliminary lemmas, or — where that is genuinely impossible — comments explaining
the global structure. Lane `FTC-DEAD`'s sibling `FTC-LONGPROOF` measured the same
defect at a 145-line threshold and found 6; against the rubric the number is 128.
Sliceable by file, and the top five are worth doing first. → `RUB-LONGPROOF`

### F6 — 290 undocumented `show` / `change` steps (`proof-quality`)

The rubric: *`change` and `show` are a code smell: flag any used without a comment
documenting why the goal cannot be reached otherwise.* 290 occurrences in
`ForTauCeti/**` have no comment in the two preceding lines. Many are innocuous
`show _ = _ by ring` inline rewrites and the right fix is to convert them to a
rewrite, not to add a comment. → `RUB-SHOW`

### F7 — 32 modules cite no informal source (`attribution`, can block)

```sh
# modules mentioning none of: prose/, arXiv, doi, or a source author's name
```

`attribution` may **block** when work closely follows identifiable existing work
with no credit, and explicitly warns about *laundering* — similarity in theorem
order, notation or proof plan is enough to require credit. 119 of 164 modules cite
something; the 32 that do not include the whole Borel-calculus chain
(`BorelCalculus/{Polarization,Multiplicative,PVM}`), the `LinearPMap` spectral
measure and `HilbertSchmidtLp`. Some of those genuinely follow nothing in
particular and the rubric says not to invent requirements. **The lane is to decide
per module and write the citation where there is one** — the spectral theorem via
the Cayley transform is textbook, and saying which textbook is cheap. → `RUB-ATTRIB`

## Negative results, recorded so they are not re-derived

- **Naming does not overstate.** Zero `_iff`-named theorems without an `↔` in the
  statement, and zero `_eq`-named theorems whose conclusion is an inequality —
  the two mechanical checks the `naming` rubric describes. 164 modules scanned.
- **Docstring presence is already gated**, and `check_docstring_coverage.py`
  reports 0 undocumented. The `documentation` rubric's remaining questions —
  usefulness, staleness, overclaiming — are judgement, and the stale-header class
  was worked off in lanes HDR-DEST, DK-FRAME and MODULUS-DEDUP earlier today.
- **`reuse`'s duplication question was asked twice today and answered with
  evidence**: T01-SQRT collapsed a genuinely duplicated definition;
  MODULUS-DEDUP established that the two moduli are *not* duplicates and
  documented the bridge the library already proves.

## What this pass did not do

- No `correctness` review. That angle asks whether statements say what they should,
  which is not mechanically measurable and is the one that most deserves a human.
- No `generality` measurement. Unused-hypothesis detection needs the elaborator
  (`lean_minimal_hypotheses` per declaration), which is a build-scale job; it is
  worth its own lane.
- No per-declaration `reuse` sweep against Mathlib. The rubric's method is a grep
  per new declaration, which is a review of a diff, not of a 164-module library.

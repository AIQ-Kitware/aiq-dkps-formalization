# Review — `ForTauCeti :: T01` Positive square root, operator modulus, functional calculus

**Status: IN PROGRESS — 2 of 9 files reviewed.** Started 2026-07-29 by
`edward (aiq-gpu)`, lane `AUDIT`. Reviewed in the voice of a reviewer who does
not want to inherit this code.

Reviewed so far, smallest first:

- [x] `Analysis/Normed/Operator/LinearIsometry.lean` — 50 lines
- [x] `Analysis/InnerProductSpace/Basic.lean` — 70 lines

## What is good, and should not be disturbed

Both files are **the right shape for submission**, and that is worth recording
because most of this audit will be complaints.

- `LinearIsometry.lean` is one `rfl` `@[simp]` lemma with a docstring that says
  *why the existing `coe_ofEq_apply` is insufficient* — the result stays in
  subtype form so `simp` can push through explicit `Subtype.mk`s. That is the
  justification a reviewer actually asks for, written before being asked.
- `Basic.lean` proves `inner_linearCombination_linearCombination` in five tactic
  lines with no `simp` sledgehammer, and its name is Mathlib-idiomatic. Its
  header records a real review history — *"following @wwylele's review (PR
  #40567) it moved here to `Basic.lean` — the lemma involves no `Orthonormal`,
  and `Basic` already hosts `Finsupp.sum_inner` / `Finsupp.inner_sum` (its
  dependencies)"*. That is genuine upstream provenance and it should survive any
  reorganization.

No duplication, no over-broad statement, no theorem needing a split in either.

## Finding T01-1 — every file header names the wrong destination `{lane:HDR-DEST}`

**Both files reviewed say `Staged for Mathlib: addition to Mathlib/...` in their
copyright header.** `ForTauCeti` targets **Tau Ceti**; `ForMathlib` is retired
and the Mathlib track is closed (`AGENTS.md`, `ForTauCeti/README.md`).

This is not a stale docstring in the class already documented — those were the
`Extraction class:` lines in the module docstring, and they have been corrected.
This is the **file header**, and it is a different 39 files.

Measured across `ForTauCeti/**`:

| pattern | files |
|---|---|
| `Staged for Mathlib: addition to Mathlib/...` | **39** |
| `To be re-authored per Mathlib's AI-contribution policy at PR time` | **35** |

The second is worse than a stale pointer: it is an **instruction to a future
submitter** naming the wrong project's policy. A Tau Ceti reviewer reading it
learns that this file was aimed somewhere else and never re-aimed.

**Not every one is wrong.** `Basic.lean` genuinely was submitted to Mathlib as
PR #40567, so its history belongs in the header — but as *history*, not as a
statement of where the file is going. The fix must distinguish "this was offered
to Mathlib once" from "this is staged for Mathlib", and only the second is false.

## Finding T01-2 — 33 doc references point at paths that do not exist `{lane:HDR-DEST}`

Both files cite destination paths as if they were current:
`Mathlib/Analysis/InnerProductSpace/GramMatrix.lean`,
`TauCeti/Analysis/InnerProductSpace/GramMatrix.lean`. Neither resolves — the
file is `ForTauCeti/Analysis/InnerProductSpace/GramMatrix.lean` today.

Repo-wide: **33 distinct unresolvable paths, cited by 30 files**, checked against
both the working tree and the pinned Mathlib checkout. Most-cited:
`Mathlib/Analysis/Matrix/Spectrum.lean` (3),
`Mathlib/Analysis/InnerProductSpace/{GramMatrix,Spectrum}.lean` (2 each).

A reader who follows one of these gets nothing. Writing the *post-submission*
path in prose is defensible if it is marked as the intended destination; writing
it as a plain cross-reference, as here, is a dangling link.

## Finding T01-3 — `GramMatrix.lean` is cited from T01 but assigned to T04

`LinearIsometry.lean`'s docstring exists to serve the *"Gram-rigidity composites
in GramMatrix.lean"*. `GramMatrix` sits in topic **T04**, which needs T01 — so
the dependency direction is right and this is **not** a layering violation.

Recording it because it confirms, from the prose side, the finding already in
`CANDIDATE-TOPIC-DESIGN.md` §C: `GramMatrix.lean` does not contain matrix
results, and a reviewer arriving from this docstring will expect matrices and
find `TauCeti.LinearMap`. It strengthens lane `PLACE-GRAM` rather than opening
anything new.

## Still to review in T01

`CourantFischer.lean` (556), `SelfAdjointFunctionalCalculus.lean` (238),
`OperatorModulus.lean` (208), `PositiveSqrt.lean` (180), `BasisSpan.lean` (157),
`SpecialFunctions/Sqrt.lean` (112), `Spectrum.lean` (72).

The group-level review of T01 is **blocked** until those land — in particular,
whether `PositiveSqrt`, `OperatorModulus` and `SelfAdjointFunctionalCalculus`
are three topics or one is a cross-file question that cannot be answered yet.

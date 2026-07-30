# What stands between `ForTauCeti` and Mathlib-quality mergeworthiness

**Every defect below has a lane.** That is the point of this file: jon's rule is
that an issue without a lane does not get worked on, so this is the checklist
that maps *defect → lane*, and anything not here is either fixed or not a
defect. Last measured **2026-07-30, pass 7** over 165 files.

## Green — measured, not assumed

| gate | result |
|---|---|
| proof escapes | **0** |
| provenance on every module | **164/164** |
| docstring coverage | **0 undocumented** — presence only; see defect 13 for *usefulness* |
| namespace policy | **OK** (164 modules, 10 allowlisted Mathlib namespaces) |
| dependency firewall | **OK** |
| header destination | **0** files name Mathlib (was 39) |
| files > 1,000 lines | **0** (was 3) |
| roadmap topics written | **24 of 24** — complete, derived from each README's own topic declaration |

## Reviewed against the actual Tau Ceti rubrics

[`TAUCETI-RUBRIC-REVIEW.md`](TAUCETI-RUBRIC-REVIEW.md) runs the ten rubrics from
`TauCetiReview/rubrics/` over both libraries. It found three objections this
checklist had missed — one rated **`block`** — and all are in the table below
(`FTC-UNEXERCISED`, `FTC-EXPOSE`, `FTC-PROSE`). The third came from taking the
rubric's own division of labour seriously: *"Linters may check presence; you
judge usefulness and honesty."* Our green "0 undocumented" row is the linter
half. It says nothing about whether the prose helps a reader of the repo we are
submitting **to** — and in 69 files it does not.

## Open defects, each with its lane

| # | defect | measure | lane | build? |
|---|---|---|---|---|
| 1 | **No topic has an *upstream* roadmap target** — ours is a proposal, the rubric reads `TauCetiProject/TauCetiRoadmap` | 0 of 24 accepted upstream | `M-SWITCH` **(jon)** | no |
| 2 | **53 flat files beside 12 directories** | 22 files, 7 missing directories | `FTC-ORG` | yes |
| 3 | **4 public definitions with no consumer** | 4 (was mis-measured as 31) | `FTC-DEAD` | yes |
| ~~4~~ | ~~10 linter suppressions~~ | **5 left, each stating why — `FTC-SETOPT` DONE** | — | — |
| 5 | **6 proofs over 145 lines**, one 231 | 6 | `FTC-LONGPROOF` | yes |
| ~~6~~ | ~~files over the 1,000-line limit~~ | **0 — `SPLIT-1K` DONE** | — | — |
| ~~7~~ | ~~flat `Sylvester*` files~~ | **0 — `PLACE-SYLV` DONE** | — | — |
| 8 | **`GramMatrix` is misnamed** and overlaps `GramOperator` | 1 decision | `PLACE-GRAM` | yes |
| 9 | **Two square roots**, one definitionally the other | `rfl`-equal | `T01-SQRT` | yes |
| 10 | **T21/T22 assert a Mathlib target** | 4 files, 2 topics | `HDR-DEST` *(decision open)* | no |
| ~~11~~ | ~~unexercised `Prop` definition (`block`)~~ | **0 — `FTC-UNEXERCISED` DONE; characterization + witness both added** | — | — |
| 12 | **70 files expose bodies** | 70 of 167 | **`FTC-EXPOSE-GATE`** + `-MEASURE` → `-a`..`-e` → `-ENFORCE` | yes |
| 13 | **69 files document our workflow, not the math** — incl. **31 pointers to the deleted `ForMathlib/` tree** | 69 of 167 | `FTC-PROSE-GATE` → `-a`/`-b`/`-c`/`-d` → `-ENFORCE` | no |

## Ordering, and why

1. ~~`ROADMAP-WRITE`~~ — **done, 24 of 24.** Every topic is now proposable.
2. **`FTC-ORG`** — now unblocked: `PLACE-SYLV` finished, so nothing collides in
   `Sylvester/`. This is the defect a reviewer meets before reading a theorem.
3. **`FTC-LONGPROOF`** — `SPLIT-1K` closed without it (the oversize files were
   split on other seams), so this stands on its own: 6 proofs over 145 lines,
   one at 231, all with 5–11-line statements.
4. **`FTC-SETOPT`** and **`FTC-DEAD`** — both sliceable, both mechanical once
   the underlying warning or the keep/delete call is made.
5. **`T01-SQRT`** and **`PLACE-GRAM`** — each needs one design decision first.
6. **`FTC-EXPOSE-GATE`** — **take this first of everything here.** jon settled
   the convention on 2026-07-30 in favour of the Tau Ceti rubric, so the
   direction is no longer open; the ratchet costs nothing, passes on today's
   tree, and stops a count that grew 68 → 70 *during this audit*.
   `FTC-EXPOSE-MEASURE` runs beside it and is the only lane in that chain
   needing a compiler — it converts an unknown conversion cost into a number
   before anyone commits to 70 files.
7. **`FTC-PROSE`** — no build, four disjoint parallel slices, and it is the
   cheapest large win here: it removes 31 pointers to a tree that does not
   exist. Take `FTC-PROSE-GATE` first; the slices are worthless without it
   because the convention that generates the prose is still in force.
8. **`HDR-DEST`'s remainder is jon's**, not an agent's: whether T19–T22 (15
   files) are Mathlib-bound or Tau Ceti-bound.

## Not defects — recorded so they are not re-raised

- **78 of 79 bare `simp` calls are terminal**, which is idiomatic Mathlib. Only
  one is non-terminal. This is not a lane.
- **An aggregator file with no declarations beside its own directory is correct**
  (`RectangularUnitarilyInvariantNorm.lean`). `PLACE-SYLV` and `FTC-ORG` must
  not sweep these up.
- **`Submodule`, `ContinuousLinearMap`, `LinearMap`, `Cardinal` and the other
  allowlisted namespaces are legitimate extensions** — the namespace gate
  encodes which, so the question is settled rather than re-litigated per file.
- **176 `@[simp]` lemmas** were not audited for simp-normal-form or looping.
  That needs elaboration, which needs a build, which this seat does not have.
  **Recorded as a known gap in this audit**, not as a clean result.

## The honest limit of this file

It lists what a *static* review can see. Three Mathlib-quality properties are
not measured here and would need a build:

- **simp-set hygiene** — whether the 176 `@[simp]` lemmas are confluent and
  terminating.
- **defeq and instance-diamond behaviour** at the API boundary.
- **whether a shorter proof exists** — `FTC-LONGPROOF` measures length, which is
  a proxy for reviewability, not for optimality.

A reviewer with a compiler would add those. This file should not be read as
"everything is fine once these ten lanes close."

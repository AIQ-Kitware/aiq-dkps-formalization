# What stands between `ForTauCeti` and Mathlib-quality mergeworthiness

**Every defect below has a lane.** That is the point of this file: jon's rule is
that an issue without a lane does not get worked on, so this is the checklist
that maps *defect → lane*, and anything not here is either fixed or not a
defect. Last measured 2026-07-30 over 164 files.

## Green — measured, not assumed

| gate | result |
|---|---|
| proof escapes | **0** |
| provenance on every module | **164/164** |
| docstring coverage | **0 undocumented** |
| namespace policy | **OK** (164 modules, 10 allowlisted Mathlib namespaces) |
| dependency firewall | **OK** |
| header destination | **0** files name Mathlib (was 39) |
| files > 1,000 lines | **1** (was 3) |
| roadmap topics written | **10 of 22** |

## Open defects, each with its lane

| # | defect | measure | lane | build? |
|---|---|---|---|---|
| 1 | **12 topics have no roadmap** | 10 of 22 written | `ROADMAP-WRITE` | no |
| 2 | **54 flat files beside 12 directories** | 22 files, 7 missing directories | `FTC-ORG` | yes |
| 3 | **31 public definitions with no consumer** | 31 | `FTC-DEAD` | yes |
| 4 | **10 linter suppressions** the README forbids | 10 sites, incl. `checkUnivs` | `FTC-SETOPT` | yes |
| 5 | **6 proofs over 145 lines**, one 231 | 6 | `FTC-LONGPROOF` | yes |
| 6 | **1 file over the 1,000-line limit** | `SinTheta/Perturbation.lean`, 1,110 | `SPLIT-1K` | yes |
| 7 | **1 flat `Sylvester*` file left** | `SylvesterGroup.lean` | `PLACE-SYLV` | yes |
| 8 | **`GramMatrix` is misnamed** and overlaps `GramOperator` | 1 decision | `PLACE-GRAM` | yes |
| 9 | **Two square roots**, one definitionally the other | `rfl`-equal | `T01-SQRT` | yes |
| 10 | **T21/T22 assert a Mathlib target** | 4 files, 2 topics | `HDR-DEST` *(decision open)* | no |

## Ordering, and why

1. **`ROADMAP-WRITE`** — 12 topics, no build, parallel, and it is the only item
   that changes whether a topic can be *proposed* at all. Everything else
   polishes something already proposable.
2. **`FTC-ORG`** then **`PLACE-SYLV`** — the defect a reviewer meets before
   reading a theorem. `FTC-ORG` is blocked on `PLACE-SYLV` finishing so the two
   do not collide in `Sylvester/`.
3. **`FTC-LONGPROOF`** before the remaining **`SPLIT-1K`** — the 1,110-line file
   is `SinTheta/Perturbation.lean`, which also holds a 205-line proof, so
   extracting lemmas may close both.
4. **`FTC-SETOPT`** and **`FTC-DEAD`** — both sliceable, both mechanical once
   the underlying warning or the keep/delete call is made.
5. **`T01-SQRT`** and **`PLACE-GRAM`** — each needs one design decision first.
6. **`HDR-DEST`'s remainder is jon's**, not an agent's: whether T19–T22 (15
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

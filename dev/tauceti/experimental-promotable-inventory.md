# What the 76 `check_library_structure` rule-3 violations actually are

**Measured 2026-07-29 (edward, fable).**

`scripts/check_library_structure.py` rule 3 — *"every Experimental module has an
admission in its closure"* — reports **76 violations**, and has for as long as
the baseline has been recorded. The number reads as "76 misplaced modules". It
is not that, and it is not one thing at all.

## The rule looks down; the meaningful question looks up

Rule 3 asks whether a module's **own import closure** contains an admission.
That is a downward question. It flags any Experimental module that happens to be
fully proved — including modules whose whole purpose is to *support* unfinished
work, which are correctly placed.

The question that determines whether a module belongs in `Experimental/` is the
upward one: **does anything that depends on it still rest on an admission?**

Splitting the 74 fully-proved Experimental modules that way (my count is 74 to
the gate's 76; the gate's `sorry` scan also matches the words "sorry-free" and
"sorries" in prose):

| | count | reading |
|---|---:|---|
| transitively support admission-bearing work | **17** | **correctly placed.** Proved scaffolding under unfinished results. Rule 3 flags these wrongly. |
| support nothing admitted | **57** | **completed mathematics parked in `Experimental/`,** where rule 2 forbids production from importing it. |

Zero are orphans — every one has a consumer.

## The 57 are not scattered

| block | count |
|---|---:|
| `MathAhead.HiddenFoundations.FreeBeam.**` | ~22 |
| `Scratch.**` (Section3/4/6, IdealBanach, RectangularHilbertSchmidt, SharedFoundations) | ~14 |
| `InfiniteDimensional.Riccati.Bounded*` | 6 |
| `MathAhead.*` aggregates and singletons | ~9 |
| `Experimental.{PartIII, FiniteDimensional.All, InfiniteDimensional.All}` | 3 |

The FreeBeam block is the completed campaign recorded as done in `dev/LANES.md`.
The bounded-Riccati block is finished bounded Riccati theory.

## What this means for the gate

Rule 3 cannot be satisfied by moving files, because 17 of its findings are
modules that *should* stay. Two honest options:

1. **Refine the rule** to the upward question — flag an Experimental module only
   when nothing depending on it carries an admission. That turns 76 into 57 and
   makes every remaining finding actionable.
2. **Promote the 57** and leave the rule alone; the 17 stay as permanent
   documented exceptions.

Doing (1) first is cheaper and makes (2) measurable as it proceeds.

## Option (1) is done, 2026-07-29

Rule 3 now asks the upward question and is renamed to match:
*"every Experimental module supports admission-bearing work"*.

**The baseline moves 76 → 59.** Other agents track this number, so: a rule-3
count of 59 is the new expected state, not a regression. Rules 1, 2, 4 and 5
are untouched and still read 3 / ok / 3 / ok.

The gate reports 59 where the independent scan above found 57.

**Correction, 2026-07-29.** An earlier revision of this file blamed that gap on
the gate's `sorry` detection matching prose. **That was wrong, and the error was
mine.** `load()` strips block and line comments before applying
`ADMISSION = \b(?:sorry|admit)\b`, so it does not see prose at all. My own scan
was the crude one: it skipped only lines *starting* with a comment marker, so it
counted `DavisKahan.Experimental.Scratch.Section7.InfiniteTanTwoThetaCore` as
admitted on the strength of a docstring line reading "...behind an axiom or
`sorry`."

The gate is right and there is **no `load()` defect to fix**. The correct
figures are the gate's: **59**, not 57. The block counts above are approximate
for the same reason and should be re-derived from the gate rather than from
this file if an exact split is needed.

## What this does *not* claim

That the 57 are ready to be production modules as they stand. They are proved
and they support nothing unfinished; whether each is *wanted* in production —
naming, generality, whether it duplicates a production result — is a per-block
judgement. `Scratch.SharedFoundations.Sylvester.BoundedLeftInverse`, for
instance, is proved and cascade-free but consumed only inside `Scratch/`, so
promoting it alone would move code without giving production anything.

**Promotion is not claimed by this measurement.** It is released with the
inventory attached.

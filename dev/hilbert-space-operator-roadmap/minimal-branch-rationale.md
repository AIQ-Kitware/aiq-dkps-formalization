# The minimal roadmap branch: what it cuts and why

`hilbert-space-operator-theory-minimal` on `Erotemic/TauCetiRoadmap` is a reduced form of
`hilbert-space-operator-theory`, offered so a reviewer who finds the full branch too large has
something smaller to accept instead. This file records the reasoning. **None of it belongs in
the roadmap itself** — the minimal branch reads as a self-contained roadmap and does not
explain that it is a reduction.

Base: `782b649`. Result: `7bf65e1`, 12 files, +109/−3004.

## The selection rule

One rule: **cut anything that asks a reviewer to accept an invented object.** What survives is
stated in `LinearMap`, `ContinuousLinearMap`, `Submodule`, `LinearPMap` and `Matrix`, so the
only question a reviewer faces is whether the statements are the right statements.

Measured against the full branch (elaborated dependency edges, `leanq`): 195 source
declarations, of which 40 touch one of ten invented bundlings, transitively. The minimal
branch keeps 91.

## What was cut, ranked by the risk it carried

| object | reach | the objection it invites |
|---|---|---|
| `OperatorIdealFamily`, `SymmetricOperatorIdealFamily` | 32 constants | one `gauge` field quantified over all Hilbert pairs in two independent universes; `extends` at `{u,v,v}` |
| `SymmetricGauge` | 24 | carrier `(ℕ →₀ ℝ≥0) → ℝ≥0`, extended to `ℝ≥0∞` in a second step |
| `UnitarilyInvariantSeminorm`, `RectangularUnitarilyInvariantSeminorm` | 20 | three bespoke fields where Mathlib has `Seminorm`, then `nonneg`/`apply_zero`/`sum_le` re-derived by hand |
| `OneParameterUnitaryGroup` | 20 | overlaps TauCeti's `StronglyContinuousSemigroup` and the one-parameter semigroups roadmap |
| `ProjValMeasure` | 18 | carries the diagonal scalar measures as data |
| `IsBddMeasurable` | 10 | bundles measurable + uniformly bounded |
| `IsKyFanDominant` | 6 | a `class` indexed by a term, not a type |
| `SylvesterEquation` | 6 | an equation encoded as a `Prop`-structure |

Two more went for a different reason. `approximationNumber : ℕ → ℝ` collides with Mathlib PR
[#32126](https://github.com/leanprover-community/mathlib4/pull/32126), which drafts
`ContinuousLinearMap.singularValue : ℕ → ℝ≥0`; dropping `OperatorIdeals` Part A removes that
collision and the `singularValues` accessor question with it. `SpectralSubspacePerturbation`
went because it is application-shaped throughout and depends on everything else.

## Second pass: cutting what had evidence against it (`b1c9231`)

The first pass left four risks in place. A second pass removed every definition with a
*documented* objection, as opposed to one I merely disliked. 99 elaborated constants to 72;
all four roadmaps survive.

| cut | the evidence |
|---|---|
| `selfAdjointFunctionalCalculus` | parallels Mathlib's `cfc`; the roadmap's own text says `cfc` is registered only over `ℂ`, so this is a generalization request wearing a new name |
| `IsPositive.sqrt`, `operatorAbs` | downstream of it; `operatorAbs` is additionally flagged in the roadmap as a placeholder name awaiting review |
| `resolventSet`, `spectrum`, `resolvent` | the SelfAdjointSpectralTheory conventions section says the one-parameter semigroups roadmap owns the notion and "that definition should be shared" |
| `IsMoorePenroseInverse`, `moorePenroseInverse` | `conformance-status.md` records a live disagreement: the roadmap states it with loose hypotheses, we deliver a bundle |
| `ContinuousLinearMap.singularValues` | collides with Mathlib PR #32126's `ContinuousLinearMap.singularValue` |

Cutting `IsMoorePenroseInverse` forces cutting `moorePenroseInverse` too: without the
predicate the construction has no characterization, and a definition with no theorems is
worse than no definition.

**Deliberately kept**, because no evidence stands against them — checked, and none duplicates
anything in Mathlib: `IsPartialIsometry` (three carrier-specific forms), `LowerFormBoundOn`,
`UpperFormBoundOn`, `restrictedSpectrum`, `SpectraSeparated`, `OrderedGap`, `InternalGap`,
`SpectrumIn`. All are one-line `Prop`s that unbundle into loose hypotheses if a reviewer
objects. The plain definitions with one obvious formula — `modulus`, `polarInitial`,
`polarPartial`, `sortedEigenvalues`, `specTransform`, the principal-angle vocabulary,
`perturb` — also stayed.

## Sizes

| branch state | elaborated constants | roadmaps |
|---|---|---|
| full (`hilbert-space-operator-theory`) | 248 | 6 |
| first pass (`7bf65e1`) | 99 | 4 |
| evidence-driven (`b1c9231`) | **72** | 4 |

For reference, two lines I measured and did not take: dropping every `Prop`-def and structure
as well leaves 47 constants and collapses SelfAdjointSpectralTheory to two declarations;
allowing no definitions whatsoever leaves 16 theorems, which is a coherent list of Mathlib
gaps but is no longer a roadmap, since pinning names and signatures is what `Suggested.lean`
is for.

## Verification

- Dependency-closed: zero dependency edges out of the kept material into the removed.
  Checked against a `leanq` index built from the minimal branch itself, not inferred by regex
  from the full branch — three separate source-regex counts disagreed with the elaborator
  before I stopped trusting them.
- `lake build` green, 8536 jobs, 0 errors.
- All relative markdown links resolve; no reference to a removed roadmap survives.
- Part letters are unchanged (Majorization keeps B and D, SelfAdjoint keeps C and D,
  MatrixStats keeps A and C), so the two branches diff against each other cleanly.

## Editing constraints used

Deletions, with rewrites only where a deletion left a sentence ungrammatical or a title
inaccurate. Three module titles and three README titles changed because their subject was
removed. Added prose across the whole branch: 104 lines against 3004 deleted.

## If the reduction goes the other way

`OperatorIdeals` Part A (approximation numbers, 7 declarations) was the last thing removed and
is the first thing to restore: it is field-generic, invents no structure, and nothing else in
the branch depends on it. The only reason it is out is the `#32126` name collision.

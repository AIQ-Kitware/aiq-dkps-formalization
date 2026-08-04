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

## What stayed that still carries risk

Naming these here rather than letting "minimal" imply "uncontroversial":

- **`selfAdjointFunctionalCalculus`** — a bespoke `RCLike` finite functional calculus
  alongside Mathlib's `cfc`, which is registered only over `ℂ` in this setting. The only
  *shape* risk left in the branch. It stayed because `IsPositive.sqrt` is the calculus at
  `Real.sqrt` and `operatorAbs` is the sqrt of `A⋆A`, so cutting it takes the polar
  decomposition and the singular systems with it — the spine of the foundations. A reviewer
  could reasonably ask for `cfc` to be generalized instead.
- **`operatorAbs`** — the roadmap already flags the name as a placeholder awaiting review.
- **`resolventSet` / `spectrum` for `LinearPMap`** — the SelfAdjointSpectralTheory README says
  this notion should be shared with the one-parameter semigroups roadmap. It is declared here.
- **`IsMoorePenroseInverse`, `IsPartialIsometry`, `LowerFormBoundOn`, `UpperFormBoundOn`** —
  invented predicates, but one-line `Prop`s that unbundle into loose hypotheses mechanically
  if rejected.

## Verification

- Dependency-closed: 110 elaborated constants in the kept slice, zero dependency edges out of
  it into the removed material. Checked against the `leanq` index, not by regex.
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

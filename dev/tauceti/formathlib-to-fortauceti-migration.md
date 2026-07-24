# ForMathlib → ForTauCeti migration

The primary "polish the major reusable proofs for Tau Ceti review" work: move the
reusable ForMathlib library into `ForTauCeti` (the polished, Tau-Ceti-bound home),
because Mathlib is not taking this contribution. Each module is module-system
converted, renamed `ForMathlib.* → TauCeti.*` (Mathlib-type-extension namespaces
kept for dot notation), given a `## Provenance` section, and its consumers
repointed. See the approximation-number cluster for the reference recipe.

## Firewall rule that shapes the order

`ForTauCeti` may import only `Mathlib` / `TauCeti` / `ForTauCeti`; **`ForMathlib`
may import only `Mathlib` / `ForMathlib`** (enforced by `check_dependency_layers.py`).
Consequence: a ForMathlib module `X` can migrate to ForTauCeti **only if no
remaining ForMathlib module imports `X`** (that importer would then illegally
import ForTauCeti). So migrate **connected components**, or files whose only
consumers are in the paper/DavisKahan layers (which may import ForTauCeti).

## Done (committed, green — ForTauCeti now 16 modules)

Migrated (Mathlib-only leaves, no ForMathlib consumers):
`Analysis/Matrix/Spectrum`, `Analysis/InnerProductSpace/{NearIsometry,OrthogonalSeries,CenteredScatter,OperatorAbsoluteValue}`,
`Analysis/CStarAlgebra/SelfAdjointGapInverse`, `Analysis/Fourier/HaagerupZsidoKernel`,
`MeasureTheory/{CompactExists, Function/ConvergenceInMeasure, Measure/Typeclasses/Probability}`.
Plus the original approximation-number cluster (6 modules).

## Immediately migratable next (Mathlib-only, no ForMathlib consumers)

None remain trivially — the other Mathlib-only leaves all have ≥1 ForMathlib
consumer (see below), so the next work is component migration.

## The big remaining chunk: the singular-value / frame component

A connected ForMathlib subgraph (~15+ files) rooted at CourantFischer. Import edges
(A → B means A imports B):

- `CourantFischer` (leaf), `InnerProductSpace/Spectrum` (leaf)
- `SchurHorn → CourantFischer`
- `RectangularSingularValues → CourantFischer`; `RectangularSingularValuesDkVariant → CourantFischer`
- `SingularSystem → RectangularSingularValues`; `FiniteFrame → RectangularSingularValues`
- `SelfAdjointFunctionalCalculus → CourantFischer, PositiveSqrt`
- `KyFan → CourantFischer, SingularSubspace, PolarDecomposition, ProjectionGeometry, Spectrum`
- `SingularSubspace`, `EntrywiseEigenvalue`, `ApproximationNumberMinMax → CourantFischer`,
  `ApproximationNumberSingularValues → CourantFischer`, `ApproximationNumberAdjoint`,
  `ApproximationNumber`, `PositiveSqrt`, `ProjectionGeometry`, `ReducingSubspace`,
  `PolarDecomposition`, `PartialIsometry`, `SylvesterBound`.

**Migrate bottom-up** (CourantFischer, Spectrum, PositiveSqrt, PartialIsometry,
PolarDecomposition first; then their importers) so no ForMathlib file is ever left
importing a ForTauCeti one. Repoint the many paper/DavisKahan consumers as you go.

### DEDUPLICATION (important)

The first cluster already created ForTauCeti copies of **CourantFischer** (renamed
`ForMathlib.* → TauCeti.*`) and the **ApproximationNumber{,Adjoint,MinMax,SingularValues}**
files (kept `ContinuousLinearMap.*` FQNs — identical to the ForMathlib originals).
So migrating those ForMathlib originals is a **dedup, not a copy**: delete the
ForMathlib original, and repoint ALL its consumers (17 for CourantFischer, incl.
DavisKahan/paper) to the ForTauCeti version — updating `ForMathlib.specSubspace` →
`TauCeti.specSubspace` for CourantFischer's consumers. The approximation-number
`ContinuousLinearMap.*` FQNs are unchanged, so those consumers only repoint imports.
Do the dedup as part of the component migration; do NOT leave two definitions of
`ContinuousLinearMap.approximationNumber` / `TauCeti.specSubspace` importable together.

## Not for ForTauCeti

- ForMathlib files that depend on `DavisKahan`/`Spectra` are NOT ForTauCeti-eligible
  (firewall) — they belong in DavisKahan (e.g. the already-relocated
  `FiniteSourceSingularSystem`). The remaining 36 non-Mathlib-only ForMathlib files
  need per-file classification (Mathlib-only-after-its-deps-migrate vs DavisKahan-bound).

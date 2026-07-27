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

## DONE (2026-07-24): the singular-value / frame component + statistics cluster

The CourantFischer weakly-connected component (37 ForMathlib modules — the
whole singular-value / UI-norm / frame subgraph plus the
probability/statistics cluster) migrated in one commit, as the firewall
requires (movers may leave behind neither dependencies nor importers, so a
weakly-connected component moves atomically). `ForMathlib/CourantFischer.lean`
was **deleted** (dedup — the ForTauCeti copy carries the redesigned API);
consumers of the historical predicate-based signatures compile through the
transitional `ForTauCeti/Analysis/InnerProductSpace/CourantFischerCompat.lean`
shim (delete each wrapper as consumers migrate to the canonical names).
Paper-layer files that re-entered `namespace ForMathlib` to extend the library
tree now extend `namespace TauCeti`. The known-non-elaborating
`RectangularSingularValuesDkVariant.lean` comparison record moved to
`dev/alternates/` (ForTauCeti builds by glob, so it cannot live there).
**Deferred:** module-system conversion of the 36 moved files (a later
mechanical pass — under the module system `private` helpers stop being visible
to later public declarations and non-public transitive Mathlib imports stop
leaking, so each file needs individual import/privacy repair).
`ForMathlib` now contains 12 modules (SpectralOrder bridges, Sylvester
operator layer, projection geometry helpers, Berge/ApproxMinimizer,
PosDef/RankFactorization).

## Historical plan (superseded by the DONE note above)

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

The first cluster already created ForTauCeti copies of **CourantFischer** and the
**ApproximationNumber{,Adjoint,MinMax,SingularValues}** files (the AN files kept
`ContinuousLinearMap.*` FQNs — identical to the ForMathlib originals).
So migrating those ForMathlib originals is a **dedup, not a copy**: delete the
ForMathlib original and repoint ALL its consumers (17 for CourantFischer, incl.
DavisKahan/paper) to the ForTauCeti version. The approximation-number
`ContinuousLinearMap.*` FQNs are unchanged, so those consumers only repoint imports.
Do the dedup as part of the component migration; do NOT leave two copies of a
declaration importable together.

**Operator-modulus name map (2026-07-24).** The three overlapping copies are
unified onto `ContinuousLinearMap.modulus`
(`ForTauCeti/Analysis/InnerProductSpace/OperatorModulus.lean`):

| old name | canonical name |
| --- | --- |
| `TauCeti.rectangularOperatorModulus T` (both copies) | `T.modulus` |
| `TauCeti.rectangularGram_nonneg` | `ContinuousLinearMap.adjoint_comp_self_nonneg` |
| `TauCeti.rectangularOperatorModulus_nonneg` | `ContinuousLinearMap.modulus_nonneg` |
| `TauCeti.isSelfAdjoint_rectangularOperatorModulus` | `ContinuousLinearMap.modulus_isSelfAdjoint` |
| `TauCeti.rectangularOperatorModulus_mul_self` | `ContinuousLinearMap.modulus_mul_self` |
| `TauCeti.norm_rectangularOperatorModulus_apply` | `ContinuousLinearMap.norm_modulus_apply` (`simp`) |
| `TauCeti.norm_rectangularOperatorModulus` | `ContinuousLinearMap.norm_modulus` (`simp`) |
| `TauCeti.operatorAbs T` | `T.modulus` (square case; shim alias retained) |
| `TauCeti.operatorAbs_unique` | `ContinuousLinearMap.eq_modulus_of_nonneg_of_mul_self_eq` |
| `TauCeti.operatorAbs_commute_operatorAbs` | `ContinuousLinearMap.modulus_commute_modulus` |
| `TauCeti.norm_operatorAbs_mul` | `ContinuousLinearMap.norm_modulus_comp` (generalized to rectangular) |
| `TauCeti.norm_mul_operatorAbs` | `ContinuousLinearMap.norm_comp_modulus` (generalized to rectangular) |
| — (new) | `ContinuousLinearMap.adjoint_modulus`, `modulus_eq_sqrt_star_mul_self`, `modulus_mul_self_eq_star_mul_self` |

Historical `operatorAbs` names remain available from the transitional
`OperatorAbsoluteValue.lean` shim; the historical `rectangularOperatorModulus`
names are **gone** (their consumers were repointed in the same commit).

**CourantFischer name map (2026-07-24).** The ForTauCeti copy carries the FINAL
redesigned API (polish backlog §6 executed; basis-span scaffolding generalized
into `ForTauCeti/Analysis/InnerProductSpace/BasisSpan.lean`). The dedup repoints
ForMathlib consumers once, to these names:

| ForMathlib name | canonical name |
| --- | --- |
| `ForMathlib.specSubspace b p` | `OrthonormalBasis.spanIndices b s` (`s : Set ι`; general `ι`, in `BasisSpan.lean`) |
| `ForMathlib.finrank_specSubspace` | `OrthonormalBasis.finrank_spanIndices` (Finset) / `finrank_spanIndices_set` |
| `ForMathlib.orthogonal_specSubspace` | `OrthonormalBasis.orthogonal_spanIndices` |
| — (new) | `OrthonormalBasis.mem_spanIndices_iff`, `repr_eq_zero_of_mem_spanIndices`, `mem_spanIndices_of_mem`, `spanIndices_mono` |
| `ForMathlib.re_inner_map_self_eq_sum_eigenvalues_mul_sq` | `LinearMap.IsSymmetric.re_inner_apply_self_eq_sum_eigenvalues_mul_sq` |
| `ForMathlib.re_inner_map_self_le_of_mem_specSubspace` (+ dual) | `LinearMap.IsSymmetric.re_inner_apply_self_le_of_mem_spanIndices` (+ `le_…_of_mem_spanIndices`) |
| `ForMathlib.exists_unit_vector_re_inner_le_eigenvalue` | `LinearMap.IsSymmetric.exists_unit_vector_re_inner_le_eigenvalue` |
| `ForMathlib.forall_unit_vector_eigenvalue_le_re_inner` | `LinearMap.IsSymmetric.exists_submodule_forall_unit_eigenvalue_le_re_inner` |
| — (new headline) | `LinearMap.IsSymmetric.eigenvalues_eq_iSup_iInf_re_inner` (sup-inf Courant–Fischer equality) |
| `ForMathlib.re_inner_map_self_eq_sum_of_eigenbasis` | `LinearMap.IsSymmetric.re_inner_apply_self_eq_sum_of_eigenbasis` |
| `ForMathlib.eigenvalues_eq_of_eigenbasis` | `LinearMap.IsSymmetric.eigenvalues_eq_of_eigenbasis` |
| `ForMathlib.eigenvalues_le_eigenvalues_of_re_inner_le` | `LinearMap.IsSymmetric.eigenvalue_mono` |
| `ForMathlib.map_mem_specSubspace` | `LinearMap.IsSymmetric.map_mem_spanIndices` |
| `ForMathlib.abs_eigenvalues_sub_le` | `TauCeti.abs_eigenvalue_sub_eigenvalue_le` (LinearMap, pointwise bound) |
| `ForMathlib.abs_eigenvalues_sub_le_opNorm` | `TauCeti.abs_eigenvalue_sub_eigenvalue_le_norm` (CLM; symmetry stated on the coerced linear maps so no `Star`/`CompleteSpace` instance is required; conclusion `‖T − S‖`, no `toContinuousLinearMap` in the signature) |

## Not for ForTauCeti

- ForMathlib files that depend on `DavisKahan`/`Spectra` are NOT ForTauCeti-eligible
  (firewall) — they belong in DavisKahan (e.g. the already-relocated
  `FiniteSourceSingularSystem`). The remaining 36 non-Mathlib-only ForMathlib files
  need per-file classification (Mathlib-only-after-its-deps-migrate vs DavisKahan-bound).

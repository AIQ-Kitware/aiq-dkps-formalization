# Tan two theta source correction overlay

Base Git HEAD:

17d0497a3abcd1b9d648a5dd1cb84a1885d3c930

## Mathematical corrections

- `tanTwoAngleOperator` now applies `safeTanTwo` directly to the canonical angle operator. The old nested functional calculus computed `safeTanTwo (safeTan theta)` rather than `tan (2 theta)`.
- `tanTwoTheta_residual_le` and `tanTwoTheta_perturbation_le` now require `OrderedInternalGap`.
- The operator-norm, Frobenius, and Ky Fan wrappers use the same corrected hypothesis.
- Spectral-side corollaries construct the ordered gap directly from the lower/upper spectral inclusions.
- `InternalGap` documentation now states its actual scope.
- The guarded-signature manifest records the two intentional source corrections.
- The checker now reports that guarded signatures match the manifest rather than claiming every historical signature was preserved.

## Why the hypothesis changed

Absolute separation permits interlacing diagonal-block spectra. An explicit real three-dimensional example satisfies `InternalGap A U 1` and the off-diagonal hypothesis while producing a reducing subspace at exactly angle `pi / 4`. The old quarter-turn conclusion was therefore false. The full construction is recorded in:

`dev/tan-two-theta-ordered-gap-correction-2026-07-20.md`

## Scope

This overlay does not modify the compiler-clean rectangular Schatten, finite lp, weak-majorization, Ky Fan, Moore-Penrose, or angle-embedding implementations. It also does not touch `DavisKahan/Experimental/InfiniteDimensional/Ideals/Rectangular.lean`.

The historical proof bodies of the two experimental arbitrary-UI tan two theta declarations still contain pre-existing fictional helper names. This overlay corrects the mathematical targets before a new proof is written; it does not claim those declarations compile.

## Static validation

- `python3 scripts/check_full_part_iii_math_ahead.py --static-only`: exit 0
- `python3 scripts/generate_all_aggregates.py --check`: exit 0
- `python3 scripts/inventory_davis_kahan_debt.py --json`: 18 intentional Challenge occurrences
- `git diff --check`: exit 0
- `python3 scripts/check_library_structure.py`: inherited check 3 remains at 116 violations; checks 1, 2, 4, and 5 pass

Lean and Lake are unavailable in the packaging environment. Compiler certification is intentionally left to the compiler agent.

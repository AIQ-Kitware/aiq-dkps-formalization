# FinishYuWangSamworth

An independent, citation-priority completion lane for:

> Yi Yu, Tengyao Wang, and Richard J. Samworth, *A useful variant of the
> Davis--Kahan theorem for statisticians*, Biometrika 102 (2015), 315--323,
> arXiv:1405.0680.

## Current theorem coverage

The lane now exposes the complete citation-critical subspace statements:

1. symmetric Theorem 2 and its aligned-basis conclusion;
2. rank-one symmetric Corollary 3;
3. exact right-singular Theorem 4;
4. the identical left-singular theorem;
5. right and left aligned singular-frame conclusions.

The rectangular theorem is available in both an intrinsic operator-norm form
and the paper's literal `2 * sigma_1 + ||Ahat - A||_op` form.

## Architecture

This is a non-default root Lake library. It has no nested `lakefile.toml`, no
nested `lean-toolchain`, and no separate `.lake` directory.

`Rectangular.Theorem4` is intentionally factored through a private generic Gram
transport theorem. Right and left wrappers only provide their Gram perturbation
bounds. This prevents duplicated proofs and keeps all constants synchronized.

Existing production theorems are imported through
`FinishYuWangSamworth.GroundedImports`. New mathematics remains under
`FinishYuWangSamworth/**` until it is ready to migrate into the canonical
`DavisKahan` or `ForTauCeti` layer.

## Build from the repository root

```bash
lake build FinishYuWangSamworth.Rectangular.FrobeniusGram
lake build FinishYuWangSamworth.Rectangular.Theorem4
lake build FinishYuWangSamworth.Rectangular
lake build FinishYuWangSamworth
```

Warnings are errors for this library.

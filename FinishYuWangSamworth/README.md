# FinishYuWangSamworth

An independent, citation-priority completion lane for:

> Yi Yu, Tengyao Wang, and Richard J. Samworth, *A useful variant of the
> Davis--Kahan theorem for statisticians*, Biometrika 102 (2015), 315--323,
> arXiv:1405.0680.

## Scope

The paper's most-used forward-facing results are the population-gap symmetric
subspace theorem (Theorem 2), its rank-one eigenvector corollary (Corollary 3),
and the rectangular singular-vector extension (Theorem 4). The repository
already has the first two theorem families in strong intrinsic form. This lane
exists to finish the exact rectangular theorem and expose all citation-facing
corollaries without destabilizing the existing `DavisKahan` production tree.

### Citation-priority completion target

1. Preserve and audit the exact Theorem 2 sine and aligned-basis surfaces.
2. Preserve and audit the Corollary 3 rank-one eigenvector surface.
3. Prove the full right-singular-subspace Theorem 4 with the paper's `min`
   numerator and constants.
4. Prove the identical left-singular-subspace result.
5. Prove aligned-basis versions for both sides.
6. Expose rank-one singular-vector corollaries suitable for direct use by
   downstream statistics and machine-learning formalizations.

Sharpness examples, equation (4), and the prose application survey are useful
source-fidelity work, but they are secondary to the theorem surfaces cited by
later papers.

## Architecture

This is a non-default root Lake library. It has no nested `lakefile.toml`, no
nested `lean-toolchain`, and no separate `.lake` directory.

Existing production theorems are imported through
`FinishYuWangSamworth.GroundedImports`. New mathematics remains under
`FinishYuWangSamworth/**` until it is complete and ready to migrate into the
canonical `DavisKahan` or `ForTauCeti` layer.

## Build from the repository root

```bash
lake build FinishYuWangSamworth.Symmetric
lake build FinishYuWangSamworth.Rectangular.FrobeniusGram
lake build FinishYuWangSamworth.Rectangular
lake build FinishYuWangSamworth
```

The first new quantitative layer is
`FinishYuWangSamworth.Rectangular.FrobeniusGram`. It proves the right and left
Gram perturbation bounds in Frobenius norm and simplifies their coefficients to
the exact `2 * ||A|| + ||Ahat - A||` form used in Theorem 4.

Warnings are errors for this library.

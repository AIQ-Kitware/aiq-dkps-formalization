# FinishYuWangSamworth

An independent completion lane for:

> Yi Yu, Tengyao Wang, and Richard J. Samworth, *A useful variant of the
> Davis--Kahan theorem for statisticians*, Biometrika 102 (2015), 315--323,
> arXiv:1405.0680.

## Theorem coverage

The lane now represents every numbered mathematical result in the paper:

1. Theorem 1 in general unitarily invariant, Frobenius, and operator norm form;
2. Theorem 2 and the aligned-basis conclusion;
3. rank-one Corollary 3;
4. exact right and left Theorem 4, including aligned frames;
5. Appendix Lemma 5 in a basis-free compression API;
6. both Section 2 sharpness examples.

Every numbered result and every sharpness claim of the paper is now proved in
the default build.

It additionally exposes direct right and left rank-one singular-vector
corollaries and a corrected form of equation (4).

## Architecture

Theorem 4 is factored through one generic Gram transport result. The
`FrobeniusGram` module owns the shared finite-dimensional Hilbert--Schmidt
foundation and the general two-sided ideal theorem consumed by Appendix Lemma
5. Bundled linear-isometry wrappers expose the paper's
orthonormal-column and orthonormal-row hypotheses directly. Rank-one
singular-vector results reuse the symmetric rank-one theorem on Gram operators.
No perturbation argument is duplicated.

See `ELEGANCE_AUDIT.md` for the in-place API and factoring review.

The paper's printed equation (4) is missing a square on
`2 - ‖v̂ - v‖²`; the lane records the corrected identity and documents this
source defect rather than asserting the false printed formula.

## Sharpness

Both of the paper's sharpness constructions are formalized against the *same*
hypotheses the theorems carry, so each is a genuine instance rather than a
numerical coincidence.

`Symmetric/OrthogonalSharpness.lean` — orthogonal top-`d` eigenspaces.  Every
aligned orthonormal pair is at distance exactly `√(2d)` and `‖sin Θ‖_F = √d`,
against a bound of `√(2d)(1+ε)`: the aligned-basis constant `2^{3/2}` and the
`√d` dimension dependence are unimprovable.

`Symmetric/PlanarSharpness.lean` — two nearby lines.  Stated without
coordinates: `diag(3,1)` is `twoLevelOperator 1 3` on a line, conjugation moves
the line, and `twoLevelOperator_sub` makes the perturbation `2 (P_v̂ − P_v)`.
The sine bound is tight up to *exactly* the factor `2` at every angle, so the
constant is pinned in the small-angle regime too — which the orthogonal-blocks
example cannot do.

Building it required the first-ever *constructor* for `CorrespondingEigenblock`
(`ForTauCeti/.../YuWangSamworth/TopEigenblock.lean`): that hypothesis is
consumed by every theorem in the lane and had no instance anywhere in the
repository, so no concrete pair of covariance operators had ever been checked
against it.

This is a root Lake library with no nested workspace, and a **default** build
target since 2026-08-02.

## Build

```bash
lake build FinishYuWangSamworth.Symmetric.Theorem1
lake build FinishYuWangSamworth.Symmetric.OrthogonalSharpness
lake build FinishYuWangSamworth.Symmetric.AngleIdentity
lake build FinishYuWangSamworth.Appendix.Lemma5
lake build FinishYuWangSamworth.Rectangular.RankOne
lake build FinishYuWangSamworth
```

Warnings are errors for this library.

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
6. the Section 2 orthogonal-blocks sharpness example, which exhibits the
   aligned-basis constant and dimension dependence as unimprovable.

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

`Symmetric/OrthogonalSharpness.lean` formalizes the paper's first sharpness
construction against the *same* hypotheses Theorem 2 carries, so it is an
instance of `yuWangSamworth_alignedBasis_le` rather than a numerical
coincidence.  Both printed equalities are proved: every aligned orthonormal
pair is at distance exactly `√(2d)`, and `‖sin Θ‖_F = √d`, against a bound of
`√(2d)(1+ε)`.

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

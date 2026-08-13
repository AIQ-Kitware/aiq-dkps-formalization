# FinishYuWangSamworth

A paper-facing formalization package for:

> Yi Yu, Tengyao Wang, and Richard J. Samworth, *A useful variant of the
> Davis--Kahan theorem for statisticians*, Biometrika 102 (2015), 315--323,
> arXiv:1405.0680.

## Theorem coverage

Numbering is the **published** Biometrika numbering (checked against the article
on 2026-08-13): Theorem 1, Theorem 2, Corollary 1, Theorem 3, Lemma A1.  The
2014 preprint shares one counter and calls the last three Corollary 3, Theorem 4
and Lemma 5, which is what several Lean declaration names here still spell; the
census carries the translation table.

The package represents every numbered result in the paper, and since 2026-08-13
each is stated at the printed generality:

1. Theorem 1 in general unitarily invariant, Frobenius, and operator norm form;
2. Theorem 2 and its aligned-frame conclusion, for **arbitrary** orthonormal
   eigenframes at a common index block — no sample eigengap, which is the whole
   point of the paper — together with the sharper residual-numerator forms its
   proof establishes;
3. Corollary 1, both displays, including the literal real sign-aligned bound;
4. Theorem 3, right and left, including aligned frames, in its corrected form;
5. Lemma A1 in a basis-free compression API;
6. both Section 2 sharpness examples.

It additionally exposes direct right and left rank-one singular-vector
corollaries.

## Two source defects, both machine checked

The paper contains two false printed statements.  Each is refuted here, and each
has a proved repair; neither is silently corrected.

* **Equation (4)** is missing a square on `2 − ‖v̂ − v‖²`.  The corrected
  identity and a counterexample to the printed polynomial are in
  `Symmetric/AngleIdentity.lean`.
* **Theorem 3's convention `σ²_{rank(A)+1} := −∞`** makes the denominator
  infinite when `s = rank(A)`, so the printed bound asserts that the sample and
  population right singular subspaces coincide when they can be orthogonal.
  `Rectangular/RankBoundary.lean` refutes it with two rank-one orthogonal
  projections.  The repair is the ambient-dimension convention the paper's own
  proof uses, and is what the theorems here already carry.

## Architecture

Theorem 3 is factored through one generic Gram transport result, at both index
and frame generality.  The `FrobeniusGram` module owns the shared
finite-dimensional Hilbert--Schmidt foundation and the general two-sided ideal
theorem consumed by Lemma A1. Bundled linear-isometry wrappers expose the paper's
orthonormal-column and orthonormal-row hypotheses directly. Rank-one
singular-vector results reuse the symmetric rank-one theorem on Gram operators.
No perturbation argument is duplicated.

See `ELEGANCE_AUDIT.md` for the in-place API and factoring review.

## Sharpness

Both of the paper's sharpness constructions are formalized against the *same*
hypotheses the theorems carry, so each is a genuine instance rather than a
numerical coincidence.

`Symmetric/OrthogonalSharpness.lean` — orthogonal top-`d` eigenspaces.  Every
aligned orthonormal pair is at distance exactly `√(2d)` and `‖sin Θ‖_F = √d`,
against a bound of `√(2d)(1+ε)`: the aligned-basis constant `2^{3/2}` and the
`√d` dimension dependence are unimprovable.  This is the *preprint's*
construction; the published article uses a middle block over three levels
`5 > 3 > 1`, so that the population gap is two-sided.  Both establish the same
printed conclusion; the published instance itself is not formalized, and the
census records that under gap `published-sharpness-example`.

`Symmetric/PlanarSharpness.lean` — two nearby lines.  Stated without
coordinates: `diag(3,1)` is `twoLevelOperator 1 3` on a line, conjugation moves
the line, and `twoLevelOperator_sub` makes the perturbation `2 (P_v̂ − P_v)`.
The sine bound is tight up to *exactly* the factor `2` at every angle, so the
constant is pinned in the small-angle regime too — which the orthogonal-blocks
example cannot do.

Building it required the first-ever *constructor* for `CorrespondingEigenblock`
(`ForTauCeti/.../YuWangSamworth/TopEigenblock.lean`): that hypothesis is
consumed by every theorem in the package and had no instance anywhere in the
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
lake build FinishYuWangSamworth.Rectangular.RankBoundary
lake build FinishYuWangSamworth
```

Warnings are errors for this library.

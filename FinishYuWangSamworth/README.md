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
4. Theorem 3, right and left, including aligned frames, in its corrected form,
   and in the paper's own singular-value notation;
5. Lemma A1 in a basis-free compression API;
6. all three Section 2 sharpness examples, including the published middle-block
   construction.

It additionally exposes direct right and left rank-one singular-vector
corollaries, the Section 1 numerical illustration that Theorem 1's separation
can vanish, and the deterministic core of the Section 3 diagnosis of the
statistical literature.

The population-gap results are also available in the source's *shape*: the block
`r, …, s` with `d` tied to them by `r + d = s + 1`, the two-sided boundary gap
`min(λ_{r-1} − λ_r, λ_s − λ_{s+1})` and the printed endpoint conventions, and an
aligned conclusion that exhibits the orthogonal `Ô` and compares `V̂Ô` against
the supplied population frame — over `ℝ`, with `Ô` an element of
`Matrix.orthogonalGroup (Fin d) ℝ`.  `Symmetric/Corollary1.lean` carries the rank-one
case together with `yuWangSamworth_corollary1_scalarSample`, the witness that
the sample eigenvector is genuinely arbitrary: for `Σ = diag(1, 0)` and
`Σ̂ = I/2` every unit vector of the plane is admissible.

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

All three of the paper's sharpness constructions are formalized against the
*same* hypotheses the theorems carry, so each is a genuine instance rather than a
numerical coincidence.

`Symmetric/OrthogonalSharpness.lean` — orthogonal top-`d` eigenspaces.  Every
aligned orthonormal pair is at distance exactly `√(2d)` and `‖sin Θ‖_F = √d`,
against a bound of `√(2d)(1+ε)`: the aligned-basis constant `2^{3/2}` and the
`√d` dimension dependence are unimprovable.  This is the *preprint's*
construction.

`Symmetric/MiddleBlockSharpness.lean` — the *published* construction, a middle
block over three levels `5 > 3 > 1`, so that the population gap `min(5−3, 3−1)`
is genuinely two-sided, over the full parameter range `0 < ε < 3`.  The model
needs `2 < 2 + ε < 5` so that `2 + ε` is the *second* level of the sorted sample
spectrum; at `ε = 3` it merges with `5` and its multiplicity becomes `p − d`, so
the range is maximal whenever `2d < p` and merely sufficient in the degenerate
case `p = 2d`, where there is no leading level `5` at all.  It proves the same printed conclusion,
and it was the
harder of the two: its block sits in the middle of both spectra, so the
branch-selection hypothesis cannot be produced by any "leading `d` eigenvectors"
argument.  Closing it needed the position of an arbitrary eigenvalue level set
inside Mathlib's sorted eigenbasis — `eigenvalues_level_eq_Ico`,
`card_filter_lt_eigenvalues_basisDiagonal`, and the general
`correspondingEigenblock_eigenvalueLevel`, of which the earlier top-eigenspace
constructor is now the case `m = 0`.

`Symmetric/PlanarSharpness.lean` — two nearby lines.  Stated without
coordinates: `diag(3,1)` is `twoLevelOperator 1 3` on a line, conjugation moves
the line, and `twoLevelOperator_sub` makes the perturbation `2 (P_v̂ − P_v)`.
The sine bound is tight up to *exactly* the factor `2` at every angle, so the
constant is pinned in the small-angle regime too — which the orthogonal-blocks
example cannot do.

Building the first of them required the first-ever *constructor* for
`CorrespondingEigenblock` (`ForTauCeti/.../YuWangSamworth/TopEigenblock.lean`):
that hypothesis is consumed by every theorem in the package and had no instance
anywhere in the repository, so no concrete pair of covariance operators had ever
been checked against it.

This is a root Lake library with no nested workspace, and a **default** build
target since 2026-08-02.

## Build

```bash
lake build FinishYuWangSamworth.Symmetric.Theorem1
lake build FinishYuWangSamworth.Symmetric.OrthogonalSharpness
lake build FinishYuWangSamworth.Symmetric.MiddleBlockSharpness
lake build FinishYuWangSamworth.Symmetric.MixedGap
lake build FinishYuWangSamworth.Symmetric.AngleIdentity
lake build FinishYuWangSamworth.Symmetric.Corollary1
lake build FinishYuWangSamworth.Appendix.Lemma5
lake build FinishYuWangSamworth.Rectangular.RankOne
lake build FinishYuWangSamworth.Rectangular.RankBoundary
lake build FinishYuWangSamworth.Rectangular.SingularBlock
lake build FinishYuWangSamworth
```

Warnings are errors for this library.

# Paper sharpness repair handoff

Authoritative base: `7b9d230f50ad874bac99515cf2ec4aa3d6613027`.

This note supersedes the `PaperSharpness` portion of the older overnight plan.
The accepted Theorem 6.2 chain is not modified by this patch.

## Current state at the base

Seven of the eight paper-facing modules compile.  The only remaining module in
the full sine-theta audit is `PaperSharpness.lean`, specifically its printed
one-gap counterexample.  The agent has already completed the independent
universe parameters and corrected the real mathematical defect in Proposition
6.1.  Preserve those changes.

The previous counterexample proof tried to rewrite the approximation-number
square norm directly with a finite Frobenius formula.  No theorem connected
those quantities, and the real sine operator lives on the canonical complexified
space rather than the original real plane.

## Mathematics added here

### Finite-dimensional square norm

`PaperHilbertSchmidtFrobenius.lean` proves, for any finite-dimensional
rectangular real or complex operator,

1. the extended paper square energy is the finite sum of squared ordinary
   singular values;
2. the paper square norm equals the rectangular Frobenius norm;
3. for square maps, it equals the existing square Frobenius norm.

The proof truncates the infinite approximation-number sum at the domain
finrank, uses the accepted finite-dimensional equality between approximation
singular values and ordinary singular values, and then applies the existing
rectangular Frobenius singular-value formula.

This theorem is general-purpose.  In the reorganization it belongs with the
paper operator-ideal implementation; its lower finite-dimensional
approximation/Frobenius ingredients are candidates for `ForMathlib` if they can
be stated independently of the paper vocabulary.

### Real sine operator

`paperHilbertSchmidtNorm_sinAngleOperatorRC_eq_projectionDifference` removes
three representation layers without changing the norm:

1. the positive modulus has the same approximation singular sequence as its
   underlying projection difference;
2. projections of complexified real subspaces are complexifications of the
   real projections;
3. real complexification preserves the paper square norm.

The counterexample is then a finite real two-by-two Frobenius calculation.

### Finite multiplicity

The old declaration named `paperFiniteMultiplicity_equality` proved only scalar
homogeneity of an arbitrary finite-dimensional operator.  It has been renamed
to `paperFiniteDimensional_scalar_homogeneity`, and its documentation now says
exactly what it proves.

A genuine finite-multiplicity extremal model remains open.  Do not restore the
old overclaiming name.  Build the real direct-sum model later or leave this row
explicitly open in the correspondence matrix.

## Compile order

Run serially:

```bash
lake env lean \
  DavisKahan/Experimental/InfiniteDimensional/Ideals/PaperHilbertSchmidtFrobenius.lean

lake env lean \
  DavisKahan/Experimental/InfiniteDimensional/SinTheta/PaperSharpness.lean

python3 scripts/audit_full_paper_sine_theta.py
```

Repair elaboration issues in the new bridge without weakening its statement.
If the direct `tsum_eq_sum` proof needs reshaping, the fallback is to prove the
operator rank is at most the domain finrank, invoke
`paperHilbertSchmidtEnergy_eq_sum_range_of_rank_le`, and then rewrite each term
with `approximationSingularValue_eq_singularValues`.

For the two-dimensional calculation, keep the proof at the real projection
level.  Do not unfold the complex functional calculus or the infinite energy
sum inside `norm_num`.

## Acceptance condition

The task is complete only when:

- both files above compile;
- `scripts/audit_full_paper_sine_theta.py` prints its clean success message;
- the dependency audit reports only the standard foundational dependencies;
- the accepted Theorem 6.2 chain remains green;
- the current audit is not weakened or narrowed.

After that, resume the staged reorganization in
`dev/flawless-sine-theta-reorganization-overnight-plan-2026-07-20.md`.

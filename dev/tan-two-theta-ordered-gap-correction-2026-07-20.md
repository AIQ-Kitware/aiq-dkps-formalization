# Tan 2 Theta requires an ordered internal gap

## Defect

The restored experimental declarations `tanTwoTheta_residual_le` and
`tanTwoTheta_perturbation_le` used `InternalGap A U δ`, meaning only absolute
pairwise separation of the spectra of the two diagonal blocks. That hypothesis
is too weak: it permits the two spectra to interlace. Under interlacing, a
symmetric off-diagonal perturbation can produce a reducing subspace at exactly
a quarter turn, so the claimed `AvoidsQuarterTurn` conclusion is false.

The source theorem uses an ordered block separation. The finite API must use
`OrderedInternalGap A U δ`, or the equivalent interval/form hypothesis that one
block lies entirely below the other by at least `δ`.

## Explicit finite counterexample to the old statement

Work over `R^3` with the orthogonal splitting

- `U = span(e1, e2)`,
- `U^perp = span(e3)`.

Let

    A = diag(-1, 1, 0).

The spectra of the two diagonal blocks are `{-1, 1}` and `{0}`. They are
absolutely separated by one, so `InternalGap A U 1` holds, but they are not
ordered.

Set

    x = (e1 + e2) / sqrt(2),
    z = (e1 - e2) / sqrt(2),
    y = e3.

Then `A x = -z`. Define the symmetric off-diagonal map `H` by

    H y = z,
    H x = 0,
    H z = y.

It has zero diagonal blocks relative to `U + U^perp`. For `B = A + H`,

    B (x + y) = 0.

Consequently `V = span(x + y)` reduces `B`, and its unique principal angle
with `U` is `pi / 4`. This contradicts the quarter-turn conclusion of the old
experimental theorem while satisfying its absolute-gap assumptions.

## Corrections in this batch

1. `InternalGap` documentation no longer claims it supports the sharp
   `tan (2 Theta)` theorem.
2. The experimental tan-two-theta declarations and concrete endpoint wrappers
   now require `OrderedInternalGap`.
3. A reusable bridge constructs `OrderedInternalGap A U (b-a)` from spectral
   inclusions `spectrum(A|U) <= a` and `spectrum(A|U^perp) >= b`.
4. `tanTwoAngleOperator` now applies `safeTanTwo` directly to the angle
   operator. The old body first applied `safeTan`, and therefore computed
   `safeTanTwo(tan theta)` instead of `tan(2 theta)`.

## Remaining proof work

The fictional helper names in the historical body are not to be recreated.
The correct arbitrary-unitarily-invariant-norm proof should follow the ordered
principal-plane/Ky-Fan argument of Davis--Kahan Section 7, or an equivalent
ordered Sylvester reduction. It must prove the tangent-double-angle singular
value dictionary and quarter-turn exclusion from the ordered gap before using
the Moore--Penrose inverse branch.

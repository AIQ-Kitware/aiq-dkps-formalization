# Finite residual sin 2Theta signature correction

Date: 2026-07-20

## Defect

The historical candidate `sinTwoTheta_residual_le` assumed only
`InternalGap A U delta`, while its conclusion concerned an arbitrary trial pair
`(X,M)` and the residual `A X - X M`.  That hypothesis does not locate the
spectrum of `M` relative to the unwanted spectrum of `A` on `U orthogonal`.
It therefore cannot support the residual Sylvester estimate used by the
single-angle and double-angle theories.

The restored proof body also had an independent type defect.  Its displayed
right-hand side contained compositions of type `E -> E`, while the supplied
rectangular unitarily invariant norm acted on maps of type `F -> E`.  Adding
names for the missing declarations would not repair that mismatch.

## Correction

The public residual theorem now uses the same source-complete
interval/exterior hypotheses as the accepted single-angle residual theorem:

- the spectrum of `M` lies in a finite interval;
- the unwanted spectrum of `A` on `U orthogonal` lies outside the interval
  enlarged by the gap.

Two companion declarations expose the other canonical regimes:

- `sinTwoTheta_residual_le_of_orderedGap`, with
  `OrderedGap M top A U orthogonal delta` and constant two;
- `sinTwoTheta_residual_le_of_spectralDistance`, with
  `SpectraSeparated M top A U orthogonal delta` and the general-separation
  constant pi.

All three results follow from the corresponding accepted single-angle
residual theorem and the intrinsic rectangular UI-norm estimate

`N (sinTwoThetaEmbedding U X) <= 2 * N (sinThetaEmbedding U X)`.

The latter is obtained from the canonical formula
`sinTwoThetaEmbedding = 2 S |C|`, the right ideal inequality, and the
contractivity of the positive source cosine `|C|`.

## API consequence

`generalizedSinTwoTheta_unequalFinrank` now accepts the ordered residual gap
between `M` and `A` on `U orthogonal`.  The previous internal-gap wrapper was
not a valid specialization.

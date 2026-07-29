# Quantitative resolvent continuity along the perturbation path

Date: 2026-07-18

## Result

The second resolvent identity is now accompanied by the operator-norm estimate

```text
||R_B(z) - R_A(z)|| <= ||R_B(z)|| ||A-B|| ||R_A(z)||.
```

For the affine path `A_t = A + tH`, the exact increment identity

```text
A_t - A_u = (t-u) H
```

gives

```text
||R_t(z) - R_u(z)|| <= M^2 ||H|| |t-u|
```

whenever `z` lies in both resolvent sets and both resolvent norms are at most
`M`.  A set-uniform wrapper makes the estimate directly usable on `[0,1]` or
on a local path neighborhood.

## Why this is the correct next Section 8 seam

The close-projection theorem completed the local geometry.  The new estimate
completes the local operator algebra.  The remaining continuity proof no
longer needs to manipulate inverses: it only needs a proof-carrying contour,
a contour-uniform resolvent bound, and the standard norm estimate for the
Bochner integral.

## Remaining contour work

1. Replace the provisional `ContourSeparatesSpectrum` proposition by data
   carrying rectifiability or piecewise `C1` regularity, closedness,
   resolvent-set membership, and a uniform resolvent bound.
2. Define `rieszProjection` as the normalized contour integral.
3. Integrate the path-parameter Lipschitz estimate to prove
   `continuous_continuedProjection`.
4. Prove agreement with the Borel spectral projection by functional-calculus
   extensionality and winding-number data.

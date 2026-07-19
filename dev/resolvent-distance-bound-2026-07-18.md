# Complex self-adjoint resolvent distance bound

Date: 2026-07-18

## Base audit

The authoritative base is commit `d7a606f`.  It contains the accepted commits
for Halmos decomposition and direct-rotation minimality (`e31daef`), local
close-projection transport (`ed6fce5`), and quantitative resolvent path
continuity (`5cca222`).  The later approximation-number commits change
separate files and do not modify the continuation or resolvent proofs.

The earlier resolvent-path survey was absent from the commit history even
though it accompanied the overlay.  It is restored in this change as
`dev/resolvent-path-lipschitz-2026-07-18.md`; no Lean declaration was missing.

## New analytic result

For a bounded self-adjoint operator on a complex Hilbert space, if a complex
number `z` remains at distance at least `delta > 0` from every real spectral
point, the continuous functional calculus constructs `(A-z)^{-1}` and proves

```text
||R_A(z)|| <= delta^{-1}.
```

The theorem returns resolvent-set membership together with the norm bound, so
later continuation code does not need to prove the two facts separately.

The affine-path corollary combines this result with the quantitative second
resolvent identity.  A common spectral-distance margin along a set of path
parameters now gives

```text
||R_t(z) - R_u(z)|| <= delta^{-2} ||H|| |t-u|.
```

## Remaining Section 8 work

1. Bundle one fixed rectifiable contour with a positive spectral-distance
   margin uniform over the contour and the path interval.
2. Define the normalized Bochner contour integral giving the Riesz projection.
3. Integrate the new path estimate to prove projection-path continuity.
4. Identify the contour projection with the Borel spectral projection.

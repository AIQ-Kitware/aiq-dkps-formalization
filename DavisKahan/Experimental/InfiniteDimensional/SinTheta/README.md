# Exact infinite-dimensional `sin Θ` scaffold

This subtree is an additive experimental dependency graph for the complete
Davis--Kahan `sin Θ` theorem. It distinguishes four targets that must not be
conflated:

1. the bounded complementary-block estimate;
2. the bounded exact directed-sine theorem, which additionally requires a
   complete orthogonal exact-space decomposition;
3. the unbounded finite-interval/exterior theorem, where one diagonal block has
   bounded spectrum;
4. the genuinely two-unbounded ordered theorem, where both blocks may be
   unbounded and the source spectral-cutoff argument is required.

The files are ordered by dependency:

1. `RectangularIdeals.lean`
2. `BoundedSylvester.lean`
3. `BoundedSpectralBridge.lean`
4. `FrameFactorization.lean`
5. `BoundedSinTheta.lean`
6. `UnboundedCore.lean`
7. `ApproximationNumbers.lean`
8. `UnboundedSylvester.lean`
9. `UnboundedSinTheta.lean`

`SemigroupSylvester.lean` is intentionally not imported by `All.lean`. It
records why a generic Laplace-semigroup route cannot be derived from ordinary
two-sided ideal laws alone: strong semigroup continuity need not imply
continuity in an arbitrary ideal gauge.

## Soundness boundaries

`RectangularSymmetricIdealFamily` records ordinary Banach operator-ideal laws.
Those laws suffice for the bounded theorem and for the finite-interval/exterior
case with one bounded spectral block. They do not imply infinite-dimensional
Fan dominance.

`UnitaryInvariantIdealFamily` is the source-facing alias for the stronger
`KyFanDominantIdealFamily`. Its finite-Ky-Fan majorization law is explicit, and
its concrete operator-norm, compact, Ky Fan, Hilbert--Schmidt, trace-class, and
Schatten instances are separate proof obligations. The genuinely two-unbounded
ordered endpoint uses this stronger family instead of incorrectly deriving Fan
dominance from arbitrary Banach ideal laws.

The unbounded spectral layer does not use a record with opaque fields of type
`Prop`. Measurable projection laws, countable strong additivity, spectral
support, cutoff-domain inclusion, cutoff commutation, strong convergence,
bounded truncation, and semibound preservation are separate declarations.

The complex Cayley transform is stated only over complex Hilbert spaces. The
generic real spectral-projection declarations leave complexification and
descent as part of their implementation burden.

The residual block identities use the signs

```text
R* F1 = X* F1 Lambda1 - A0 X* F1
A0 X* F1 - X* F1 Lambda1 = -R* F1.
```

`gram_coercive` explicitly assumes a nonnegative frame constant. The exact
angle endpoints additionally require `OrthogonalExactDecomposition`, so an
arbitrary invariant complementary block is not mislabeled as the full directed
sine.

The fastest useful tranche remains the bounded chain through
`generalizedSinTheta_bounded_exact`. The complete unbounded endpoint remains
downstream of a stable partial-operator adjoint, real/complex spectral bridge,
measurable spectral projections, approximation numbers, strong cutoff
convergence, and finite-Ky-Fan dominance.

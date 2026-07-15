# Experimental Hilbert-space Davis--Kahan theory

This subtree contains unfinished foundations and theorem families needed to
formalize Davis--Kahan (1970) in the ambient scope stated by the paper. It is
not an optional extension of a completed finite-dimensional project. The
finite library is a valuable specialization and weaker-foundation alternative;
the bounded Hilbert-space main body, operator-ideal norm scope, and unbounded
passages remain the default source-fidelity target.

This subtree is organized by the locations its modules are intended to occupy
once their statements and proofs stabilize.

- `Core/` provides actual restricted-operator spectrum predicates together
  with experimental spectral-projection, real/complex bridge, form,
  unbounded-operator, and operator-angle interfaces.
- `Sylvester/` develops bounded, resolvent, and unbounded Sylvester estimates.
- `SinTheta/` develops bounded and unbounded sine-theta theorems and the
  required frame-factorization and spectral bridges.
- `Ideals/` develops compact, approximation-number, rectangular, and symmetric
  operator-ideal interfaces.
- `OperatorBlocks/`, `Riccati/`, `DirectRotation.lean`, `GraphSubspace.lean`,
  `DoubleAngle.lean`, and `Sharpness.lean` retain the corresponding geometric
  and analytic programs. Some are direct source obligations; others are later
  extensions and must be identified as such in their module documentation.

### Restricted-spectrum statement repair (2026-07-15)

`Core/AbstractSpectrum.lean` now defines `realSpectrum` using Mathlib's
real Banach-algebra spectrum and `restrictedSpectrum` using the spectrum of
`A.restrict hU` for an invariant subspace.  `SpectrumIn`, ordered and unordered
separation, and the derived gap predicates carry invariance explicitly.  This
removes the former empty-point-spectrum loophole for continuous-spectrum
self-adjoint operators.  The affected Sylvester, sine-theta, ideal, Riccati,
and off-diagonal declarations remain experimental proof obligations, but their
gap hypotheses are no longer false for that reason.

The graph-subspace donor and vendor audit is recorded in
`dev/graph-subspace-vendor-survey-2026-07-14.md`. It identifies the pinned
Mathlib closed-graph, anti-Lipschitz, closed-range inverse, and near-identity
inversion APIs that should be used before introducing new functional-analysis
infrastructure.

Definitions in this subtree are implementation seams rather than frozen APIs.
Experimental modules may import supported modules; supported modules must not
import this tree.

Build this subtree with:

```bash
lake build DavisKahan.Experimental.InfiniteDimensional.All
```

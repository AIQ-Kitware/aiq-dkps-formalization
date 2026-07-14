# Experimental Hilbert-space Davis--Kahan theory

This subtree contains unfinished foundations and theorem families needed to
formalize Davis--Kahan (1970) in the ambient scope stated by the paper. It is
not an optional extension of a completed finite-dimensional project. The
finite library is a valuable specialization and weaker-foundation alternative;
the bounded Hilbert-space main body, operator-ideal norm scope, and unbounded
passages remain the default source-fidelity target.

This subtree is organized by the locations its modules are intended to occupy
once their statements and proofs stabilize.

- `Core/` provides provisional abstract-spectrum, spectral-projection,
  real/complex bridge, form, unbounded-operator, and operator-angle interfaces.
- `Sylvester/` develops bounded, resolvent, and unbounded Sylvester estimates.
- `SinTheta/` develops bounded and unbounded sine-theta theorems and the
  required frame-factorization and spectral bridges.
- `Ideals/` develops compact, approximation-number, rectangular, and symmetric
  operator-ideal interfaces.
- `OperatorBlocks/`, `Riccati/`, `DirectRotation.lean`, `GraphSubspace.lean`,
  `DoubleAngle.lean`, and `Sharpness.lean` retain the corresponding geometric
  and analytic programs. Some are direct source obligations; others are later
  extensions and must be identified as such in their module documentation.

Definitions in this subtree are implementation seams rather than frozen APIs.
Experimental modules may import supported modules; supported modules must not
import this tree.

Build this subtree with:

```bash
lake build DavisKahan.Experimental.InfiniteDimensional.All
```

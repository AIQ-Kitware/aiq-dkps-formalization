# Experimental Davis--Kahan development

This tree mirrors the mathematical organization of the stable `DavisKahan`
library. A completed cluster can therefore be promoted by moving it to the
corresponding stable path rather than redesigning its module boundary.

- `FiniteDimensional/` contains open finite-dimensional extensions.
- `InfiniteDimensional/Core/` contains provisional spectral, form, and
  operator-angle infrastructure.
- `InfiniteDimensional/Sylvester/` contains bounded, resolvent, and unbounded
  Sylvester developments.
- `InfiniteDimensional/SinTheta/` contains bounded and unbounded sine-theta
  targets and their frame-factorization bridge.
- `InfiniteDimensional/Ideals/` contains compact, approximation-number,
  rectangular-ideal, and symmetric-ideal work.
- `InfiniteDimensional/OperatorBlocks/`, `Riccati/`, and the top-level
  direct-rotation, graph-subspace, double-angle, and sharpness modules retain
  the corresponding operator-theoretic programs.

Experimental modules may import stable modules. Stable modules must not import
this tree.

Build the complete experimental development with:

```bash
lake build DavisKahan.Experimental.All
```

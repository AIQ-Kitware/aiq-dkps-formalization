# Experimental Davis--Kahan development

This tree contains unfinished work toward both the canonical full-paper theory
and optional extensions. In particular, the Hilbert-space modules are not a
secondary generalization of an already completed finite theory: they contain
major portions of the default Davis--Kahan 1970 objective.

The tree mirrors the mathematical organization of the stable `DavisKahan`
library. A completed cluster can therefore be promoted by moving it to the
corresponding stable path rather than redesigning its module boundary.

- `FiniteDimensional/` contains open finite-dimensional extensions.
- `InfiniteDimensional/Core/` contains provisional spectral, form, and
  operator-angle infrastructure required by the paper's Hilbert-space scope.
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
this tree. Status as experimental means the declarations are not yet accepted
as stable APIs; it does not mean they are outside the main source-fidelity
roadmap.

Build the complete experimental development with:

```bash
lake build DavisKahan.Experimental.All
```

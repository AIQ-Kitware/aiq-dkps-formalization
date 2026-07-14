# DavisKahan

This is the canonical Davis--Kahan library root.

- `Core/` contains spectral-subspace, gap, angle, and block-operator vocabulary.
- `Residual/` contains Ritz, trial-map, and angle-embedding residual interfaces.
- `Sylvester/` contains finite-dimensional and bounded-operator Sylvester estimates.
- `FiniteDimensional/` contains the stable sine, tangent, and double-angle theory.
- `BoundedOperator/` contains the supported scalar-generic bounded theory.
- `Sources/` contains publication-facing theorem surfaces and source-specific wrappers.
- `Specialized/` contains useful secondary endpoints and is not re-exported by `DavisKahan`.
- `Experimental/` mirrors the intended stable hierarchy for unfinished finite- and
  infinite-dimensional work.

`import DavisKahan` exposes the stable bounded-operator, finite-dimensional, and
source-facing libraries. Specialized and experimental endpoints require explicit
imports.

The former `DavisKahan.Specialized.EigenbasisFrobenius*` module trees have
been removed. General-purpose infrastructure remains under `ForMathlib`, while
Davis--Kahan-specific definitions and theorems now live here.

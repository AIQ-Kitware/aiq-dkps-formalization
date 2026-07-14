# DavisKahan

This is the canonical Davis--Kahan library root.

- `BoundedOperator/` contains the supported arbitrary-Hilbert-space bounded
  operator theory.
- `FiniteDimensional/Core/` contains finite spectral-subspace, gap, angle, and
  block-operator vocabulary.
- `FiniteDimensional/Residual/` contains Ritz, trial-map, and angle-embedding
  residual interfaces.
- `FiniteDimensional/Sylvester/` contains finite-dimensional Sylvester
  estimates and their internal reciprocal-multiplier machinery.
- `FiniteDimensional/SinTheta/`, `TanTheta/`, and `DoubleAngle/` contain the
  stable finite theorem families.
- `Sources/` contains publication-facing theorem surfaces and source-specific
  wrappers.
- `Specialized/` contains distinct useful secondary endpoints.
- `Alternative/` contains proof-complete duplicate or lower-dependency proofs
  and noncanonical wrapper APIs retained for explicit reuse and cherry-picking.
- `Experimental/` contains incomplete or unstable finite- and
  infinite-dimensional work.

The dependency direction is deliberate: canonical bounded and finite modules
must not import `Sources`, `Specialized`, `Alternative`, or `Experimental`.
Those branches are leaves built on the canonical library.

`import DavisKahan` exposes the supported bounded-operator and
finite-dimensional theory together with the flagship Davis--Kahan Part III
facade. Other source transcriptions, specialized endpoints, alternative proofs,
and experiments require explicit imports.

`import DavisKahan.All` exposes every proof-finished source, specialized, and
alternative module, while still excluding `Experimental`.

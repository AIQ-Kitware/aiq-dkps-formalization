# DavisKahan

This is the canonical Davis--Kahan library root.

## Project mission

The default target is the full Hilbert-space theory of Davis--Kahan (1970), not
only the finite-dimensional specialization. The paper's main development uses
bounded Hermitian operators on a separable Hilbert space, states all four
headline theorems for infinite and finite dimensions and arbitrary
unitary-invariant norms, and includes unbounded self-adjoint extensions under
domain conditions.

The finite branch is a valuable proof-complete specialization with weaker
foundational requirements and a richer currently implemented UI-norm API. It
must not be presented as completion of the paper unless the claim is explicitly
qualified as finite-dimensional.

- `BoundedOperator/` contains the supported arbitrary-Hilbert-space bounded
  operator theory and is the canonical direction for the paper's main-body results.
  It is not yet a complete implementation of all four source theorem families.
- `FiniteDimensional/Core/` contains finite spectral-subspace, gap, angle, and
  block-operator vocabulary.
- `FiniteDimensional/Residual/` contains Ritz, trial-map, and angle-embedding
  residual interfaces.
- `FiniteDimensional/Sylvester/` contains finite-dimensional Sylvester
  estimates and their internal reciprocal-multiplier machinery.
- `FiniteDimensional/SinTheta/`, `TanTheta/`, and `DoubleAngle/` contain the
  stable finite theorem families.
- `FiniteDimensional/DirectRotation/` contains the proved canonical rotation
  construction and its basic intertwining surface.
- `Sources/` contains publication-facing theorem surfaces and source-specific
  wrappers. `Sources/DavisKahan1970/README.md` records the exact boundary
  between the proof-complete Part III package and the remaining paper audit.
- `Specialized/` contains distinct useful secondary endpoints.
- `Alternative/` contains proof-complete duplicate or lower-dependency proofs
  and noncanonical wrapper APIs retained for explicit reuse and cherry-picking.
- `Experimental/` contains incomplete or unstable finite- and
  infinite-dimensional work, including scaffolding toward the missing
  bounded, operator-ideal, and unbounded source layers.

The dependency direction is deliberate: canonical bounded and finite modules
must not import `Sources`, `Specialized`, `Alternative`, or `Experimental`.
Those branches are leaves built on the canonical library.

`import DavisKahan` exposes the supported bounded-operator and
finite-dimensional theory together with the current finite Davis--Kahan Part
III facade. That import surface is a convenience and stability boundary, not a
claim that the full paper has been formalized. Other source surfaces,
specialized endpoints, alternative proofs, and experiments require explicit
imports.

`import DavisKahan.All` exposes every proof-finished source, specialized, and
alternative module, while still excluding `Experimental`.

The maintained completion standard is documented in
[`docs/planning/davis-kahan-full-paper-goal.md`](../docs/planning/davis-kahan-full-paper-goal.md).

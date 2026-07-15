# DavisKahan

This is the canonical Davis--Kahan library root.

## Project mission

The default target is the full Hilbert-space theory of Davis--Kahan (1970), not
only a bounded or finite-dimensional specialization.  The canonical
source-facing single-angle theorem must include the paper's unbounded
self-adjoint scope with explicit domains and bounded residuals, together with
arbitrary supported unitary-invariant norms.  Bounded Hermitian operators are a
major specialization and proof seam, not the final API boundary.

The finite branch is a valuable proof-complete specialization with weaker
foundational requirements and a richer currently implemented UI-norm API. It
must not be presented as completion of the paper unless the claim is explicitly
qualified as finite-dimensional.

- `BoundedOperator/` contains supported arbitrary-Hilbert-space bounded
  specializations and reusable geometric foundations. It is not the owner of
  the unqualified source-facing theorem names.
- `Experimental/InfiniteDimensional/SinTheta/Canonical.lean` records the
  maximally general source target while the closed-operator, ideal, and
  spectral-cutoff dependencies are still incomplete.
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
The controlling single-angle dependency plan is
[`docs/planning/davis-kahan-general-sin-theta-roadmap.md`](../docs/planning/davis-kahan-general-sin-theta-roadmap.md).

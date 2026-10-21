# Upstream consumption: native reducing restrictions and UI-seminorm API

## Exact checkpoint

- Apply over DKPS commit `7cd3d7a11b91` (the 2026-10-21 12:13 snapshot).
- That snapshot pins TauCeti `87dad819828705ed8329ff53b9bc53634a064b1a`,
  Mathlib `e3e75e86143b43849829fdcd44a39a6b0fe35234`, and Lean `v4.36.0-rc1`.
- The pre-upstream formal proof remains recoverable at DKPS `acac427e5a34`.
- These changes have not been compiled in the overlay-generation environment.
  Do not record a verified build on the basis of static checks.

## Mathematical change 1: reducing subspaces

`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean` formerly
implemented the density, closed-graph, and self-adjointness proofs for a
restriction to an orthogonally complemented reducing subspace. They are now
proofs by application of the accepted TauCeti theorems.

The donor predicate has *four* components: domain preservation under both
orthogonal projections, and invariance of both subspaces. Upstream's
`_root_.LinearPMap.IsReducing A U` has *three*: domain preservation under
`P_U`, and the two invariances. The fourth follows because
`P_{Uᗮ}x = x - P_U x`. This is not a change of hypothesis scope.

New exact, non-axiomatic conversion points:

- `TauCeti.LinearPMap.ReducesSubspace.toIsReducing`
- `TauCeti.LinearPMap.ReducesSubspace.ofIsReducing`
- `TauCeti.LinearPMap.reducesSubspace_iff_isReducing`
- `TauCeti.LinearPMap.reducingRestriction_eq_restrict`

The latter identifies the historical `reducingRestriction` partial map with
`A.restrict hred.toIsReducing.isInvariant`. Three formerly independent donor
proofs now forward to accepted upstream results:

- `IsReducing.dense_restrict_domain`
- `IsClosed.restrict`
- `IsReducing.isSelfAdjoint_restrict`

**All three existing donor theorem statements are textually unchanged.**
The legacy declarations and the old restriction *representation* remain in this
checkpoint because downstream source-facing theorem implementations still use
their original types. The next migration step can substitute the canonical
`IsReducing` and `restrict` directly and then delete these non-headline
compatibility entry points. Do not keep them indefinitely. The stronger local
adjoint-domain iff has been retained: no equivalent public upstream theorem
was established in this inspection.

Upstream sources at the pinned SHA:

- `TauCeti/Analysis/InnerProductSpace/LinearPMap/Reducing.lean`
- `TauCeti/LinearAlgebra/LinearPMap/Restrict.lean`
- `TauCeti/Topology/Algebra/Module/LinearPMap/Restrict.lean`

## Mathematical change 2: eliminate temporary seminorm shims

`ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm/Transport.lean`
no longer declares nine forwarding lemmas (`nonneg`, `apply_zero`, `add_le`,
`smul_eq`, `apply_neg`, `invariant`, `invariant_left`, `invariant_right`,
`eq_of_same_singularValues`). All maintained callers were changed to the
accepted `apply_nonneg`, `map_zero`, `map_add_le_add`, `map_smul_eq_mul`,
`map_neg_eq_map`, `map_linearIsometryEquiv_comp_comp`,
`map_linearIsometryEquiv_comp`, `map_comp_linearIsometryEquiv`, and
`map_eq_of_singularValues_eq` APIs. This touches finite-dimensional sine/double
angle, direct rotations, sharpness, and the local Sylvester norm estimates.

The actual **codomainIsometryTransport** and **domainIsometryTransport**
constructions remain: they cover *isometric embeddings*, not just the
surjective isometric equivalences TauCeti provides. Do not delete these
unless an accepted upstream replacement is identified.

## Build and repair order

Run sequentially from the DKPS repository root. Download the Mathlib cache
before the first build. The two core modules can be repaired independently:

```bash
cd ~/code/aiq-dkps-formalization
lake exe cache get
lake build ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Closed
lake build ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Transport
lake build ForTauCeti.Analysis.InnerProductSpace.SinTheta.Perturbation
lake build DavisKahan.FiniteDimensional.DoubleAngle.SinTheta
lake build DavisKahan.FiniteDimensional.Sharpness
lake build DavisKahan.Sources.DavisKahan1970.SineTheta.Presentation
```

Once these pass, run the complete library and source census:

```bash
lake build
python3 scripts/check_davis_kahan_1970_source_census.py
```

If a kernel/elaboration error arises in `reducingRestriction_eq_restrict`,
first check the domain extensionality and action equality under `Subtype.ext`.
Do **not** weaken `ReducesSubspace`, assume boundedness, change the target
source theorem, or introduce `sorry`/new axioms. If one of the canonical
seminorm methods does not elaborate by dot notation, use its fully qualified
upstream name with the same arguments, not a replacement forwarding theorem.

No headline or census theorem statements were edited. This is a dependency
and proof-implementation cleanup, not a research-paper graph/tooling change.

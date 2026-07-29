# Graph-subspace vendor survey — 2026-07-14

## Purpose

This survey records the search performed before implementing the arbitrary-Hilbert-space
acute-subspace/graph-operator theorem. It exists so later agents do not repeat the same searches,
miss already available functional-analysis infrastructure, or mistake the absence of a direct
Davis--Kahan donor for the absence of useful lower-level tools.

The target seam is:

> If two closed subspaces have orthogonal projections whose operator-norm difference is less than
> one, then one subspace is the graph of a unique bounded angular operator over the other.

This is the geometric bridge from the existing bounded `sin Theta` projector estimate to bounded
`tan Theta`, Riccati equations, direct rotation, and the acute branch of the double-angle theory.

## Search scope

The search covered:

- this repository's finite and infinite experimental graph, angle, Riccati, direct-rotation, and
  operator-block modules;
- the pinned Mathlib source and API at revision
  `c368140668f5fa16a1bd977448c1f665d48c3df4`;
- GitHub code searches for graph subspaces, graphs of bounded operators, angular operators,
  two-projection geometry, bounded inverses, anti-Lipschitz closed-range results, Riccati graph
  methods, and operator angles;
- Mathlib pull-request history for projection geometry and Davis--Kahan work;
- external Lean repositories already known to contain spectral or operator theory, especially
  `YuanheZ/lean-stat-learning-theory` and `adambornemann-glitch/Spectra`.

No external Lean implementation of the full acute-projections-to-unique-bounded-graph theorem was
found. No existing Lean formalization of the full Halmos two-projection decomposition or general
operator angles between arbitrary closed Hilbert subspaces was found.

### Concrete search log

| Search direction | Result |
|---|---|
| `graphSubspace`, `angularOperator`, `operatorAngle` in Lean repositories | Returned this repository's experimental files and unrelated uses of the word graph; no donor theorem. |
| `Halmos two projections`, `acute projections`, `projection gap graph` | No Lean implementation of the two-projection decomposition or acute graph theorem found. |
| `Riccati graph subspace` | Returned this repository's bounded Riccati scaffolding; no external completed graph bridge. |
| `LinearPMap.graph`, closed operator graph | Found the pinned Mathlib closed/closable graph infrastructure used by the unbounded-operator API. |
| `AntilipschitzWith.isClosed_range` | Found the direct closed-range theorem needed for the graph embedding. |
| `ContinuousLinearMap.equivRange`, bounded inverse, closed range | Found the Banach open-mapping and continuous-inverse packaging needed for `P_U\|_V`. |
| `Units.oneSub`, near-identity inverse | Found the Neumann-series route for the compressed projection. |
| Mathlib Davis--Kahan pull requests | Found PR `#40771`, a finite eigenspace bound; useful context but not an infinite graph-subspace donor. |
| External operator-theory Lean libraries | `Spectra` is the strongest future donor for PVM, unbounded, polar, and ideal infrastructure, but it does not eliminate the immediate two-projection graph proof. |

## Immediate vendor conclusion

The best immediate donor is **pinned Mathlib**, not another Davis--Kahan project. The genuinely new
work is the two-projection estimate and coordinate algebra. Closedness, closed-range equivalences,
and inverse continuity should be delegated to existing APIs.



They are reference snapshots and are not imported by the project build. Production code should
import the corresponding Mathlib modules directly.

## Pinned Mathlib tools

### Canonical graph language

Source:
`Mathlib/Topology/Algebra/Module/LinearPMap.lean`.

Relevant declarations:

- `LinearPMap.graph`;
- `LinearPMap.IsClosed`;
- `LinearPMap.IsClosable`;
- `LinearPMap.IsClosable.graph_closure_eq_closure_graph`;
- `LinearPMap.isClosable_iff_exists_closed_extension`.

Use:

- represent operator graphs canonically;
- align the bounded graph-subspace construction with the later unbounded appendix;
- avoid creating an unrelated local graph abstraction that must later be reconciled.

The immediate bounded theorem may define the ambient graph as the range of a continuous graph
embedding. A comparison theorem with the corresponding total `LinearPMap.graph` should then be
proved explicitly.

### Anti-Lipschitz closed range

Source:
`Mathlib/Topology/MetricSpace/Antilipschitz.lean`.

Relevant declarations:

- `AntilipschitzWith.isUniformEmbedding`;
- `AntilipschitzWith.isComplete_range`;
- `AntilipschitzWith.isClosed_range`;
- `AntilipschitzWith.isClosedEmbedding`.

Use:

For an angular operator `X`, define the graph embedding

```text
J_X(u) = u + X u.
```

Orthogonality of `u` and `X u` gives

```text
norm (J_X u - J_X v)^2
  = norm (u - v)^2 + norm (X u - X v)^2,
```

hence `J_X` is one-anti-Lipschitz. `AntilipschitzWith.isClosed_range` then gives closedness of the
graph range directly from completeness of the subtype `U`.

This replaces a hand-written Cauchy-sequence proof.

### Closed-range equivalence and continuous inverse

Source:
`Mathlib/Analysis/Normed/Operator/Banach.lean`.

Relevant declarations:

- `ContinuousLinearMap.equivRange`;
- `ContinuousLinearMap.equivRange_symm_apply`;
- `ContinuousLinearMap.antilipschitz_of_injective_of_isClosed_range`;
- `ContinuousLinearMap.isClosed_range_iff_antilipschitz_of_injective`;
- `ContinuousLinearMap.leftInverse_of_injective_of_isClosed_range`;
- `ContinuousLinearEquiv.ofBijective`.

Use:

- package the restricted projection `P_U|_V : V -> U` as a continuous equivalence after proving
  injectivity and surjectivity;
- obtain inverse continuity from the Banach open-mapping theorem instead of proving estimates for a
  chosen inverse manually;
- use `equivRange` when the image subtype is convenient, and `ofBijective` when the codomain is
  already known to be all of `U`.

### Near-identity inversion

Source:
`Mathlib/Analysis/Normed/Ring/Units.lean`, using `Units.oneSub` from the imported geometric-series
infrastructure.

Relevant declarations:

- `Units.oneSub`;
- `Units.add`;
- `Units.ofNearby`;
- `NormedRing.inverse_one_sub`.

Potential use:

On `U`, study the compression `P_U P_V P_U`. If the acute hypothesis yields

```text
norm (I_U - P_U P_V P_U) < 1,
```

then `Units.oneSub` gives an inverse by a Neumann-series construction. This may be a cleaner Lean
route to surjectivity of `P_U|_V` than proving dense range from orthogonal complements and combining
it with closedness.

This route is promising but not yet selected as the final proof. The implementation should compare
it against the direct bijectivity proof before committing to one.

### Orthogonal-projection API

Sources:

- `Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`;
- `Mathlib/Analysis/InnerProductSpace/Projection/Submodule.lean`.

Relevant existing tools include:

- `Submodule.orthogonalProjectionOnto`;
- `Submodule.starProjection`;
- `Submodule.starProjection_eq_self_iff`;
- `Submodule.ker_starProjection`;
- `Submodule.starProjection_orthogonal`;
- `Submodule.isCompl_orthogonal`;
- `Submodule.orthogonal_orthogonal`.

These modules are already central dependencies of the local bounded theory, so separate vendor
excerpts were not added in this pass.

## External repositories screened

### `YuanheZ/lean-stat-learning-theory`

Status: licensed and already represented in `vendor/lean/`.

Useful content:

- finite-dimensional spectral subspaces;
- finite operator-norm Davis--Kahan theorems;
- singular systems and Eckart--Young--Mirsky.

Not supplied:

- arbitrary-Hilbert-space graph subspaces;
- acute projection pairs;
- operator angles in infinite dimensions;
- a bounded graph/Riccati bridge.

Decision: retain as a finite specialization and audit donor, not as the implementation base for this
seam.

### `adambornemann-glitch/Spectra`

Audited commit: `8dbaaf6728d1342ae16acf79fd7eef7c59b37e63`.
License: Apache-2.0.
Toolchain reported by the repository: Lean `v4.31.0-rc1`; this project currently uses
`v4.32.0-rc1`.

The repository reports a proof-complete operator-theory stack containing:

- closed and unbounded operators;
- self-adjointness and self-adjoint extensions;
- resolvents;
- projection-valued measures;
- two constructions of the spectral theorem;
- bounded and unbounded functional calculus;
- polar decomposition;
- trace-class and Hilbert--Schmidt infrastructure.

Decision:

- **do not add it as a project dependency for the graph-subspace theorem**;
- **do not copy a large subtree blindly** across a toolchain boundary;
- perform theorem-level audits before adapting PVM, spectral-cutoff, unbounded, polar-decomposition,
  or ideal code;
- treat it as the leading future vendor candidate for Section 8, the unbounded appendix, and the
  infinite-dimensional norm-ideal layer.

No `Spectra` source file is copied in this pass because none is necessary for the immediate graph
seam, and selecting files without a theorem-level dependency audit would create a misleading vendor
snapshot.

## Signature defect found during the survey

The current experimental declaration

```lean
noncomputable instance graphSubspace_hasOrthogonalProjection
    (U : Submodule k E) [U.HasOrthogonalProjection]
    (X : E ->L[k] E) : (graphSubspace U X).HasOrthogonalProjection
```

is too strong if `graphSubspace` is defined from the range of `u |-> u + X u` for an arbitrary
ambient map `X`. Such a range is not automatically closed.

The implementation pass must do one of the following:

1. add `hX : IsAngularOperator U X` to the instance;
2. bundle angularity into a graph-operator structure;
3. state a more general bounded-below hypothesis and derive the angular case as a corollary.

The first option is the smallest correction. The third is the most reusable. The existing
unconditional surface must not be proved by an arbitrary-choice construction.

## Revised implementation order

1. Define `graphEmbedding U X hX : U ->L[k] E` by `u |-> u + X u`.
2. Prove the Pythagorean norm identity.
3. Package the embedding as one-anti-Lipschitz.
4. Define `graphSubspace` as its range and obtain closedness through
   `AntilipschitzWith.isClosed_range`.
5. Correct the orthogonal-projection instance to require angularity or bounded-below data.
6. Define the restricted projection `P_U|_V : V ->L[k] U`.
7. Prove injectivity from `norm (P_U - P_V) < 1`.
8. Prove surjectivity either directly or by near-identity compression and `Units.oneSub`.
9. Package the map using `ContinuousLinearEquiv.ofBijective` or `equivRange`.
10. Define the ambient angular operator by composing the inverse with `P_{U-perp}` and extending by
    zero on `U-perp`.
11. Prove graph equality and uniqueness by applying the two coordinate projections.
12. Only after this seam is green, develop the normalized graph isometry and projection formula.

## Completion boundary for the next proof pass

The next proof overlay should aim to close:

- the graph embedding and closedness lemmas;
- the corrected graph projection instance;
- existence and uniqueness of the angular operator for acute subspaces.

The projection formula involving `(I + X* X)^(-1/2)` is a stretch goal and should not block the
acute graph theorem.

# Public API review for Tau Ceti integration

## Principles

- Generic mathematics belongs in canonical analysis/operator modules.
- Paper numbering and historical terminology belong in source-facing wrappers.
- Existing Tau Ceti and Mathlib vocabulary wins over repository-local wrappers.
- A contribution PR should advance one roadmap target or one tightly coupled
  prerequisite layer.

## Namespaces to reconsider

### `ForMathlib`

The current repository uses `ForMathlib` for generally useful declarations.
Tau Ceti should place these directly under its canonical topic namespaces.
Examples include approximation numbers, orthogonal-series helpers, coercive
inverse lemmas, and Hilbert--Schmidt basis identities.

### `DavisKahanExt`

This namespace contains both genuinely generic operator theory and
Davis--Kahan-specific geometry.  Split by ownership:

- closed-operator, spectral-restriction, Sylvester, graph-subspace, and
  projection formulas -> canonical analysis/operator namespaces;
- sine/tangent perturbation endpoints -> spectral perturbation namespace;
- literal paper aliases -> Davis--Kahan source namespace.

### `paper*` declarations

Keep `paper*` names only in the source correspondence layer.  Generic results
such as basis independence, Frobenius equivalence, pairwise spectral separation,
or operator-modulus invariance should receive mathematical names in their
canonical modules; the paper layer may alias them.

### `Experimental`

Do not transfer the current directory classification mechanically.  For every
proved declaration, determine its minimal clean dependency closure and natural
home.  Transfer unfinished APIs only if a roadmap explicitly asks Tau Ceti to
build them.

## Structures to reconcile rather than duplicate

Before porting, compare these against current Tau Ceti/Mathlib definitions:

- `ClosedOperator` versus the selected `LinearPMap`-based unbounded-operator API;
- reducing subspaces and spectral restrictions;
- spectral gap predicates;
- rectangular unitarily invariant norm families;
- Hilbert--Schmidt membership and norm;
- graph-subspace and angular-operator structures;
- source-specific data records such as `PaperTheorem61Data`.

Source data records are useful theorem-packaging devices but should not become
the general public API unless they express a reusable mathematical object.

## Proposed PR sequence

### PR 1 -- approximation numbers

Rectangular approximation numbers, basic inequalities, finite-dimensional
agreement, and operator modulus.  No Davis--Kahan theorem in this PR.

### PR 2 -- rectangular ideal families and Hilbert--Schmidt equivalences

Ideal abstraction, column energy, tensor correspondence, adjoint symmetry, and
Frobenius specialization.

### PR 3 -- closed operators and reducing restrictions

After the local U1 convergence migration is complete. The foundational choice is
already fixed: use Mathlib `LinearPMap` plus property predicates, matching Tau
Ceti's semigroup generator. Coordination may refine names and PR boundaries, but
it does not justify retaining the DKPS `ClosedOperator` bundle as a peer API.

### PR 4 -- Sylvester equations

Closed equation structure, homogeneous uniqueness, interval/exterior estimates,
and pairwise Hilbert--Schmidt estimate.  Split finite reciprocal-multiplier
internals if review size demands it.

### PR 5 -- operator angles and graph subspaces

Directed sine/cosine, projection identities, graph projection formulas, and
angle-gap compatibility.

### PR 6 -- finite Davis--Kahan Part III

Port the stable source-facing finite package audited in
`finite-dimensional-part-iii-audit.md`.

### PR 7 -- unbounded sine-theta and source correspondence

Port the already compiled domain-aware theorem, common-domain/core variants, real
descent, equality, counterexample, finite-multiplicity, and pairwise square-norm
surface after its prerequisite APIs have landed.

### Later PRs

Double-angle genuine-spectrum extraction, Riccati theory, direct-rotation
extremality, continuation, and other results should be independently scoped.

## Avoid during integration

- a permanent `ForMathlib` bucket;
- a permanent whole-project `Vendor/Spectra` subtree without maintainer
  agreement;
- broad root imports that obscure declaration dependencies;
- source aliases whose targets still live under Experimental;
- importing a source facade to obtain a generic helper;
- combining namespace cleanup, new mathematics, and paper correspondence in one
  PR;
- claiming the complete 1970 paper from the finite specialization alone.

## Immediate pre-submission checklist

- obtain human scope guidance through a Meta issue;
- settle whether this is one roadmap or several coordinated roadmaps;
- compare against current Mathlib master and Tau Ceti main;
- register a narrow intention only after target headings are accepted;
- identify the first small prerequisite PR and its exact provenance;
- run Tau Ceti's build, linter, module-system, and trusted-dependency checks in a
  clean checkout.

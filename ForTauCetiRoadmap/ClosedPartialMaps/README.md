# Roadmap: closed partial linear maps — graphs, constructions, form bounds

**Topic T15a of the candidate design.** Six modules; needs T04 (Gram matrices,
orthogonal projections and spectral subspaces) and nothing else. The base of the
unbounded stack: everything in T15b (resolvents) and T15c (the spectral measure)
is stated about the objects defined here.

## The decision this topic embodies

**An unbounded operator is a Mathlib `LinearPMap`, and its analytic properties are
hypotheses rather than fields.**

```lean
-- not this
structure ClosedOperator (E : Type*) … where
  toFun : …
  closed : …
  denseDomain : …

-- this
variable {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A)
```

The declarations take raw partial maps; closedness, dense domain and
self-adjointness are separate hypotheses supplied by the theorem that needs them.
This is fixed by interoperability, not taste: **Tau Ceti's own semigroup generator
already is a `LinearPMap`**, so a second bundled foundation would need an adapter
at every boundary. `AGENTS.md` records the decision as U1.

The cost is visible and worth stating: a theorem that needs three properties
carries three hypotheses. The benefit is that no consumer ever unwraps a bundle,
and Mathlib's `LinearPMap` API — `domain`, `graph`, `adjoint`, `IsSelfAdjoint`,
`le_def` — applies directly.

## What the topic supplies

* **`LinearPMap/Closed.lean`** — the domain-aware infrastructure: domain
  transport, extension, symmetry, graph norms, relative bounds, and the elementary
  real resolvent predicates. It is the largest module in the topic and the one
  every later file leans on.
* **`LinearPMap/GraphCore.lean`** — a *graph core* is a submodule of the domain
  from which every domain vector is reachable by a sequence converging in the
  graph norm. The sequence formulation is deliberate: it records exactly the two
  convergences a closed-graph argument consumes, **without installing a second
  topology on the domain subtype**, which would force every consumer to move
  between two topological structures.
* **`LinearPMap/Constructions.lean`** — `perturb A V`, the domain-preserving
  perturbation that Kato–Rellich arguments start from, and the fact that a bounded
  self-adjoint operator viewed as a partial map on all of `H` is self-adjoint in
  the `LinearPMap` sense. Neither has spectral content.
* **`LinearPMap/Sylvester.lean`** — the domain-aware equation `A X - X B = C` with
  its semibounds and bounded-everywhere inverse data, stated for partial maps.
  Analytic properties stay separate hypotheses here too.
* **`QuadraticFormBounds.lean`** and **`SpectralOrder/Complex.lean`** — lower and
  upper bounds for the real part of a bounded operator's quadratic form on a
  subspace, and the bridge from an actual spectral inclusion to those bounds over
  `ℂ`. They are in this topic because the semibounded theory consumes them, and
  they are stated for *bounded* operators because that is what the bridge needs.

## Pinned conventions

### Semibounds are predicates on the partial map, not a subtype

`SemiboundedBelow A c` and `SemiboundedAbove A c` are `Prop`s about `A` and a real
constant. A `Semibounded` subtype would re-create the bundle the U1 decision
rejects, and the predicates compose with `le_def` for free. Two bundled wrappers
of exactly this shape existed downstream and were deleted as dead in 2026-07-28;
the deletion is the evidence that the predicate form is what consumers use.

### The consumer supplies the bound, and the general form takes it as a hypothesis

Where a lower bound `c ‖x‖ ≤ ‖A x - z x‖` is available for free — off the real
axis, from `|Im z|` — the theorem in T15b proves it. Where it is not, the theorem
takes it. Neither is a weaker statement than the other; see T15b's roadmap, which
records the same split from the resolvent side.

## Existing foundations

Mathlib supplies `LinearPMap` with `domain`, `graph`, `adjoint`, `IsSelfAdjoint`,
`le_def` and the closed-graph theorem for bounded maps, `Submodule` with its
topology and closure API, and `ContinuousLinearMap` adjoints.

What Mathlib does not have: graph-norm convergence as a usable relation, graph
cores, relative boundedness, the domain-preserving perturbation, and the
domain-aware Sylvester equation.

A sorry-free staged implementation exists under `ForTauCeti/` (six modules;
`scripts/check_tauceti_roadmap_topics.py --topic T15a`). It still requires Tau
Ceti review and migration.

## What remains to land

- **A closed-graph characterisation of closedness in these terms.** The module has
  graph norms and graph cores; the statement *`A` is closed iff its graph is
  closed iff every graph-convergent sequence has its limit in the domain with the
  expected image* is not stated as one iff, and it is what a reader checks first.
- **Kato–Rellich itself.** `perturb` exists and is documented as where such an
  argument starts; the theorem — that a symmetric relatively-bounded perturbation
  of a self-adjoint operator with bound `< 1` is self-adjoint — is not here.
- **Theorem-level acceptance examples**, in Tau Ceti's shape.

## Ordering and PR slices

1. `LinearPMap/Closed.lean` alone. It is 963 lines and the whole topic depends on
   it; reviewing it with anything else attached is what makes a PR unreviewable.
2. `LinearPMap/{GraphCore, Constructions}` — two short, independent additions.
3. `LinearPMap/Sylvester.lean` with `QuadraticFormBounds` and
   `SpectralOrder/Complex` — the equation and the form bounds it uses.

## Provenance and coordination

The six modules were authored in place in this repository (Davis–Kahan/DKPS
formalization, Kitware, Inc.). Their history is the U1 migration: a bundled
`ClosedOperator` foundation existed and was demoted, with `LinearPMap` chosen as
the canonical carrier; `dev/tauceti/u1-linearpmap-migration.md` records the
measured hand-off, and `AGENTS.md` records the decision.

T15a is rung **L** of `dev/tauceti/submission-ladder.md`. It is consumed by T15c
and T17.

**This topic was T15's first third until 2026-07-30.** Lane T15-SPLIT divided a
25-module, 6,700-line T15 into T15a/T15b/T15c, and
[`../UnboundedOperators/README.md`](../UnboundedOperators/README.md) is the
pre-split roadmap covering all three — read it for the U1 decision's full
statement, and this file for what T15a itself contains.

Written 2026-07-30 by `jon (yardrat)` under lane ROADMAP-WRITE, claimed together
with T15c.

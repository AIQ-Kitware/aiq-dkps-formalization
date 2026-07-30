# Unbounded operators on `LinearPMap`


> **This is the pre-split roadmap, and it now spans three topics** (`jon (yardrat)`,
> 2026-07-30). It was written against a single 25-module, 6,700-line T15. Lane
> T15-SPLIT divided that topic along the three chains the audit found, so the
> milestones below are distributed as:
>
> * **T15a** — closed partial maps, graphs, constructions, form bounds →
>   [`../ClosedPartialMaps/`](../ClosedPartialMaps/README.md)
> * **T15b** — resolvents, semiboundedness, the gap inverse →
>   [`../UnboundedResolvent/`](../UnboundedResolvent/README.md)
> * **T15c** — the spectral measure, Stone uniqueness, Yosida →
>   [`../UnboundedSpectralMeasure/`](../UnboundedSpectralMeasure/README.md)
>
> Kept because the **U1 decision** — that an unbounded operator *is* a Mathlib
> `LinearPMap`, with closedness and self-adjointness as hypotheses rather than
> structure fields — is stated here at length and is the premise all three inherit.
> Read this for the decision, and the three topic files for what each contains.

## Summary

Develop a reusable unbounded-operator layer using Mathlib `LinearPMap` as the
canonical object. Closedness, dense domain, symmetry, self-adjointness, domain
transport, bounded extension, graph norms, restrictions, and perturbations are
expressed as properties and constructions on partial linear maps.

This roadmap deliberately does **not** introduce a second bundled
`ClosedOperator` foundation. Tau Ceti's semigroup generator already is a
`LinearPMap`, so the representation is fixed by interoperability with existing
Tau Ceti and Mathlib APIs.

## Motivation

Spectral perturbation, closed Sylvester equations, reducing restrictions, and
semigroup generators all require domain-aware operators. A common
`LinearPMap`-based vocabulary lets these theories compose without adapters and
prevents every downstream theorem from carrying a project-local wrapper.

The Davis--Kahan development supplies mature proofs for many of the required
facts, but its historical bundle is provenance, not the desired public API.

## Scope

### Milestone U1: basic predicates and domain relations

- closed and densely-defined partial linear maps;
- consequences of self-adjointness;
- equality of domains and extension of partial maps;
- transport of domains by continuous linear maps;
- characteristic and simp lemmas for domain-subtype application.

### Milestone U2: bounded embeddings and extensions

- canonical full-domain `LinearPMap` associated to a continuous linear map;
- bounded extensions of partial maps;
- uniqueness and restriction lemmas;
- interaction with composition and adjoints where defined.

### Milestone U3: graph norm and relative boundedness

- graph norm on the domain subtype;
- completeness under closedness;
- relative boundedness and elementary closure laws;
- bounded perturbation closedness.

### Milestone U4: reducing restrictions

- invariant and reducing subspaces for domain-aware operators;
- projection preservation of the domain;
- restricted partial maps and canonical embeddings;
- inheritance of symmetry/self-adjointness under appropriate hypotheses.

### Milestone U5: operator equations and semigroup interoperability

- domain transport used by closed Sylvester equations;
- compatibility with Tau Ceti semigroup generators and resolvents;
- no separate generator/closed-operator conversion layer.

## Representation decisions

1. `LinearPMap` is the foundational object.
2. Closedness, dense domain, symmetry, and self-adjointness are properties.
3. A bundle may be added only as a derived convenience carrying a `LinearPMap`
   and proofs; it may not own a parallel domain/action representation.
4. Bounded operators use the existing full-domain partial-map construction.
5. Same-domain and maps-domain-to concepts are predicates unless additional
   mathematical data is genuinely required.
6. Spectral calculus, PVMs, and real/complex descent are separate roadmap
   dependencies and do not block the core representation migration.

## Exclusions

- Davis--Kahan sine/tangent theorem statements;
- paper numbering and source records;
- a new bundled `ClosedOperator` universe;
- wholesale Spectra PVM or Borel-calculus porting;
- PDE/Fredholm applications beyond the basic reusable operator layer.

## Provenance

The initial proof corpus comes from
`DavisKahan/SpectralTheory/ClosedOperator/` and related reducing-subspace and
Sylvester modules. Spectra informs compatibility and provides some downstream
spectral-calculus implementations. Every transferred declaration must record its
original path, commit, authorship, and whether it was copied, generalized, or
re-proved.

## Acceptance criteria

- all public foundational declarations are over `LinearPMap`;
- no dependency on DavisKahan or Spectra in the reusable core;
- no duplicate of pinned Mathlib/Tau Ceti declarations;
- module-system, documentation, provenance, line-limit, axiom, and lint gates
  pass in Tau Ceti;
- DavisKahan can consume the canonical layer with its historical bundle reduced
  to a temporary adapter;
- semigroup generators and closed-operator results compose without conversion
  between independent representations.

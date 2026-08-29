# Foundation-building route

Use this route when a formalization task exposes a reusable mathematical layer that belongs in
Tau Ceti. The target theorem becomes a consumer of that layer.

## Goal

Build the strongest stable paper-independent foundation at its natural mathematical generality,
polish it in `ForTauCeti`, and derive the source-facing theorem from the reusable API.

The resulting library should be useful when the motivating paper is removed from the repository.

## Foundation test

A foundation candidate is ready for this route when several of the following hold:

- it is a standard mathematical object, theorem, decomposition, representation, or transport law;
- multiple current or expected consumers use the same underlying argument;
- local proofs repeatedly introduce the same coordinates, decompositions, finite-dimensional
  reductions, scalar specializations, or compatibility lemmas;
- the concept has a stable canonical carrier and a coherent public API;
- a dimension-free or scalar-generic statement captures the mathematics more directly than the
  current consumer-specific statement;
- proving it turns the motivating theorem into a short composition of reusable results;
- it belongs naturally in an existing Tau Ceti roadmap area or supplies a foundation for one.

## Workflow

1. **Inventory the available foundation.** Inspect pinned Mathlib, the pinned Tau Ceti
   dependency, and `ForTauCeti` before designing a new declaration. Record the strongest existing ingredients and
   their exact hypotheses.
2. **State the mathematical foundation independently.** Write the intended public statements
   with paper-independent names, mathematical constants, and library terminology.
3. **Choose the canonical representation.** Use the representation already established by Mathlib
   or Tau Ceti when one exists. Make structural data explicit when the mathematics contains a real
   choice.
4. **Choose natural generality.** Use the weakest stable hypotheses supported by the mathematics.
   Prefer arbitrary Hilbert dimension, rectangular operators, and `RCLike` scalar fields when the
   statements are intrinsically uniform. Keep genuinely real or complex constructions at their
   natural scalar type.
5. **Build a dependency-closed API cluster.** Put the reusable implementation in `ForTauCeti` with
   final `TauCeti.*` declaration names, provenance, module documentation, and the basic lemmas that
   make the object usable by later developments.
6. **Expose canonical structure first.** Prefer basis-free decompositions, subspaces, isometries,
   equivalences, and universal properties. Add enumerations, bases, coordinates, and finite-rank
   truncations as derived APIs when they carry additional mathematical content.
7. **Cover boundary cases in the foundation.** Include kernels, zero values, repeated eigenvalues,
   infinite-dimensional ambient spaces, finite-rank branches, and other natural degeneracies in the
   public design.
8. **Migrate the motivating theorem.** Make the paper-facing result consume the new foundation and
   retain source vocabulary in `DavisKahan` wrappers.
9. **Consolidate ownership.** Move reusable lemmas to their canonical module, migrate consumers, and
   leave one public spelling for each concept.
10. **Validate the library layer and the consumer layer.** Build the new `ForTauCeti` modules first,
    then their paper consumers, then the repository checks and roadmap-topic checks.

## Proof engineering

Use intermediate lemmas that reveal the reusable mathematical structure. A successful foundation
usually has a small set of load-bearing theorems from which specialized estimates and source
wrappers become short corollaries.

When a local route becomes complicated, restate the obstacle as a candidate library theorem and
check whether proving that theorem improves the surrounding API. Continue through the library
statement when it does.

## Completion standard

The foundation-building route is complete when:

- the reusable theorem lives in `ForTauCeti` at its natural scope;
- its API has stable names, precise hypotheses, provenance, and usable basic lemmas;
- the motivating paper theorem is a downstream consumer;
- repeated local implementations have converged on the canonical owner;
- the implementation supports the relevant Tau Ceti roadmap mathematics at Mathlib-quality style;
- remaining work is an explicitly scoped mathematical extension supported by the completed
  infrastructure.

## Evergreen handoff prompt

Use `dev/foundation-building.md` for this task. Treat the requested theorem as a consumer of the
best reusable mathematical foundation. Inspect Mathlib, Tau Ceti, and `ForTauCeti`; identify the
missing paper-independent layer whose presence makes the target theorem direct; design that layer
at its natural generality and canonical representation; build and polish it in `ForTauCeti`; then
rewrite the source-facing theorem to consume it. Prefer coordinate-free and dimension-free core
statements, with chosen bases, enumerations, finite-dimensional forms, and paper vocabulary as
later interfaces. Report the foundation added, the consumers migrated, and any genuinely separate
mathematical extension that remains.

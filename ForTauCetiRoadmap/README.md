# ForTauCetiRoadmap — in-repo Tau Ceti roadmap drafts

This folder holds **roadmap drafts authored inside the DKPS repository**, in the
shape the [Tau Ceti Roadmap](https://github.com/TauCetiProject/TauCetiRoadmap)
expects: one folder per area, a definitive `README.md`, and optional prototype
signatures in `Suggested.lean`.

We do the full prep to be Tau-Ceti-ready **here**, and structure everything as if
the contribution will be accepted — without assuming it will. Nothing in this
folder depends on external acceptance; when a real submission is authorized, an
area is lifted out verbatim into a `TauCetiRoadmap` PR.

This mirrors the `ForTauCeti/` staging library (final `TauCeti.*` namespaces,
reproduced into `TauCeti/` on demand by `scripts/export_for_tauceti.py`): code
stages in `ForTauCeti/`, its roadmap stages here.

## Areas

1. [Approximation numbers and Hilbert-space singular values](ApproximationNumbers/README.md)
   — the first, dependency-closed, paper-independent foundation. Maps to the
   staged `ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/**` cluster.

2. [Symmetric operator ideals](SymmetricOperatorIdeals/README.md) — the
   dependent roadmap area (1) explicitly disowns: the ideal-family interface,
   symmetric norming functions, Ky Fan dominance, and the Schatten /
   Hilbert--Schmidt / trace-class instances. The interface itself is already
   staged as `ForTauCeti/Analysis/OperatorIdeal/Family/**`, so this area starts
   with a landed decision record rather than a blank page.

3. [Unbounded operators on `LinearPMap`](UnboundedOperators/README.md) — the
   active U1 representation-convergence roadmap. The canonical object is already
   fixed by Mathlib/Tau Ceti; local implementation proceeds now through a
   temporary Davis--Kahan adapter. This roadmap specifies the reusable API and
   migration gates, not a competing bundled operator type.

## Planned (later) areas

These are gated on the remaining Track B convergence waves (see
[`dev/tauceti/convergence-matrix.md`](../dev/tauceti/convergence-matrix.md)).

4. **Projection-valued measures and Borel functional calculus** (its own
   roadmap) — PVMs, spectral projections, bounded/unbounded Borel calculus,
   spectral restriction and localization, real/complex descent. This is the
   largest genuinely *missing* foundational layer (Wave 5 Cluster B); Tau Ceti
   does not supersede it and Spectra is a real donor, so it is specified
   separately, coordinated with Spectra's author, and does not ride on the
   spectral-perturbation roadmap.
5. **Spectral Subspaces, Sylvester Equations, and Davis–Kahan Perturbation
   Bounds** — depends on (1), (2), (3), and (4); coordinates its closed-operator layer with
   Tau Ceti's existing one-parameter-semigroup roadmap. Its APIs (reducing
   subspaces on `LinearPMap`, directed operator angles, bounded/unbounded
   Sylvester theory) must be dependency-closed via Waves 2–3 before they are
   specified here.

## Authoring rules (from the Tau Ceti Roadmap)

Every draft here follows the upstream conventions so it transfers without
rework:

- **Build the library, don't race to the theorem.** For each object, specify its
  complete basic theory, not only the lemma a headline needs.
- **Everything is grounded, no leaps.** Every milestone rests on existing
  Mathlib/Tau Ceti material, earlier material in the same roadmap, or an
  explicitly cited dependency. If something needed does not exist, building it is
  itself a target.
- **Use Mathlib's vocabulary**; do not wrap a standard notion in a private one.
- **Specify the mathematics, not our code.** Any file-by-file map goes in a
  clearly secondary *Provenance* section so reviewers never treat the DKPS source
  as prescriptive.
- **Decide generality and conventions up front** and write them down.
- **Nothing is "optional"** — everything lives in some milestone.

See [`docs/planning/tauceti-adaptation-and-spectra-extraction.md`](../docs/planning/tauceti-adaptation-and-spectra-extraction.md)
for the dual-track policy, acceptance gates, and submission (A1–A3) split.

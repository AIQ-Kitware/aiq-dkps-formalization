# Tau Ceti PR 1 — package

Prepared, not pushed. See the safe push command at the bottom.

* **Repository**: `https://github.com/TauCetiProject/TauCeti.git`
* **Branch**: `approximation-numbers` (created from `origin/main`)
* **Observed `origin/main` head**: `92c79e5e0a618f8c5c2b9909be1ce50f6891dde7`
* **Diff scope**: only `TauCeti/…` — 6 new files, 1662 insertions. No change to
  `scripts/`, `.github/`, `lakefile.toml`, `formalization.yaml`, `TauCeti.lean`,
  `lake-manifest.json`, or `lean-toolchain`.

---

## PR title

```
Add rectangular approximation numbers for Hilbert-space operators
```

## PR body

### Summary

Adds the reusable, paper-agnostic foundation of **approximation numbers** for
continuous linear maps: the zero-based approximation number
`ContinuousLinearMap.approximationNumber T n : ℝ≥0` — the operator-norm distance
from `T` to maps of rank at most `n` — together with its order and ideal API, its
adjoint invariance on Hilbert spaces, its finite-dimensional agreement with
singular values (Eckart–Young), a Spectra-free Courant–Fischer lower-bound
(min–max) helper layer, and the positive rectangular operator modulus with its
pointwise-norm identity. Independent source and target universes are preserved
throughout. No Davis–Kahan perturbation theorem and no Spectra dependency are
introduced.

<!--tauceti-target:v1 {"focus":"spectral-subspace-perturbation","id":"SpectralSubspacePerturbation/PartB/approximation-numbers"}-->

> **Roadmap-target note for the maintainer:** this maps to *Part B — Approximation
> numbers and rectangular symmetric ideals* of the SpectralSubspacePerturbation
> roadmap draft, i.e. "PR 1 — approximation numbers" in the extraction plan. The
> draft is not yet merged into TauCetiRoadmap, so the `id` above is provisional;
> replace it with the canonical accepted target id (roadmap file + label) before
> merge, and claim `author/spectral-subspace-perturbation/<target-id>` per
> COORDINATION.md §4 first.

### Roadmap target

Part B (Approximation numbers and rectangular symmetric ideals). Acceptance
checks from the roadmap are met: operator norm recovered at index zero
(`approximationNumber_zero`), finite-dimensional agreement with singular values
(`approximationNumber_eq_singularValues`), adjoint invariance
(`approximationNumber_adjoint`), and the two-sided ideal/contraction behavior
(`approximationNumber_comp_comp_le`, `approximationNumber_smul`).

### Scope (what is included)

Files (all `module`, `public import`, `@[expose] public section`, warning-clean,
< 1000 lines):

* `TauCeti/Analysis/OperatorIdeal/ApproximationNumber/Basic.lean` — the definition
  and the elementary order + ideal API over a `NontriviallyNormedField`:
  `approximationNumber`, `approximationNumber_zero` (= operator norm),
  antitonicity, nonnegativity, operator-norm bound, zero/negation/scalar/addition
  behavior, the additive shift `approximationNumber_add_le_add`, the left/right/
  two-sided composition inequalities, and absolute homogeneity `approximationNumber_smul`.
  Includes the universe helper `Cardinal.le_natCast_of_lift_le` and the
  cross-universe rank lemma `rank_comp_left_le_of_rank_le`.
* `TauCeti/Analysis/OperatorIdeal/ApproximationNumber/Adjoint.lean` — adjoint
  invariance `approximationNumber_adjoint` on Hilbert spaces.
* `TauCeti/Analysis/InnerProductSpace/CourantFischer.lean` — the finite-dimensional
  Courant–Fischer / spectral-subspace min–max helpers (`specSubspace`,
  `finrank_specSubspace`, the eigenvalue min–max comparison lemmas,
  `orthogonal_specSubspace`) supporting the singular-value identification.
* `TauCeti/Analysis/OperatorIdeal/ApproximationNumber/FiniteDimensional.lean` —
  the finite-dimensional Eckart–Young identification
  `approximationNumber_eq_singularValues` and its two inequalities.
* `TauCeti/Analysis/OperatorIdeal/ApproximationNumber/MinMax.lean` — the
  infinite-dimensional Courant–Fischer lower bound
  `lowerBound_le_approximationNumber_of_finrank` and its linear-independent form
  (Spectra-free; only the `≥` half of the min–max, which needs no witnessing-subspace
  existence theorem).
* `TauCeti/Analysis/OperatorIdeal/ApproximationNumber/OperatorModulus.lean` — the
  positive rectangular source modulus `rectangularOperatorModulus T = (T* T)^{1/2}`
  for complex Hilbert spaces, its self-adjointness/positivity/defining square, and
  the pointwise identity `‖|T| x‖ = ‖T x‖` and `‖|T|‖ = ‖T‖`.

### Deliberate exclusions

This PR does **not** include:

* any Davis–Kahan sine/tangent/spectral-subspace perturbation theorem;
* rectangular symmetric ideal families or paper unitary-invariant norm structures;
* Hilbert–Schmidt / Schatten theory (a later PR);
* Spectra / PVM infrastructure or arbitrary-Hilbert-space spectral localization;
* the full **approximation-number invariance under the source modulus**
  (`sameApproximationSingularValues_rectangularOperatorModulus`) — its current proof
  routes through a Spectra-based infinite-dimensional min–max
  (`SpectraBridge.lt_approximationNumber_iff_exists_finiteDimensional_lowerBound`);
  the modulus definition and its pointwise-norm identity are included, but the
  invariance theorem is deferred to a later dependency-closed PR (per the extraction
  plan's option 2 — do not import Spectra to keep a theorem count);
* exact orthogonal block-sum merge formulas whose proof depends on Spectra;
* real-complexification machinery unrelated to the basic API;
* any Davis–Kahan source `SameApproximationSingularSequence` record or paper
  correspondence.

### API decisions

* **Canonical object.** The foundation is the `ℝ≥0`-valued
  `ContinuousLinearMap.approximationNumber`, not the Davis–Kahan real-valued wrapper
  `approximationSingularValue`. `ContinuousLinearMap.approximationNumber` does not yet
  exist in Mathlib (checked at the pinned revision), so this contributes it; the
  definition and API follow Mathlib PR #32126, from which the Davis–Kahan version was
  originally adapted.
* **Namespace.** Declarations extend the existing Mathlib namespaces
  `ContinuousLinearMap` and `Cardinal` rather than living under `TauCeti`, so that
  dot notation (`T.approximationNumber`) resolves and the names match the eventual
  Mathlib upstreaming target. Lean field projection binds `T.approximationNumber`
  only to a literal `ContinuousLinearMap.approximationNumber`, so a `TauCeti.`
  prefix would break every dot-notation proof. The Courant–Fischer *helpers* (not
  dot-notation on a Mathlib type) do live under `namespace TauCeti`. **Flagged for
  maintainer review** — happy to move everything under `TauCeti` and drop dot
  notation (as `TauCeti.ContinuousLinearMap.index` does) if that is preferred.
* **Independent universes.** Source and target spaces move in independent universes
  wherever the mathematics allows; cross-universe rank comparisons are routed through
  `Cardinal.lift` and the natural-number-bound helper.
* **File split.** Split by mathematical responsibility (definition/order API;
  adjoint; finite-dimensional singular-value identification; infinite-dimensional
  min–max; operator modulus) and to keep the finite-dimensional Courant–Fischer
  support importable on its own, each file well under the 1000-line new-file limit.
* **Finite-dimensional singular values.** Connected to Mathlib's
  `LinearMap.singularValues` via the Eckart–Young theorem in `FiniteDimensional.lean`
  (lower bound by dimension counting against a Courant–Fischer test subspace; upper
  bound by projecting onto the top singular directions).
* **Operator-modulus invariance is deferred**, not included (see exclusions).

### Provenance

* Source repository: the Davis–Kahan / DKPS formalization (Kitware, Inc.), commit
  `fc38eb48b9b49f2e1d87fe0c7022dc5e262820a7`.
* Original paths: `ForMathlib/Analysis/Normed/Operator/ApproximationNumber*.lean`,
  `ForMathlib/Analysis/InnerProductSpace/CourantFischer.lean`, and the clean part of
  `DavisKahan/OperatorIdeal/ApproximationNumbers/OperatorModulus.lean`.
* Original authors / copyright: Jon Crall, OpenAI GPT-5.6 Thinking, Niels Voss,
  Arnav Mehta, Rawad Kansoh; Copyright (c) 2026 Kitware, Inc., Apache 2.0 (headers
  preserved verbatim; each file carries a Provenance section).
* Mathlib relation: adapted from Mathlib PR #32126.
* Spectra influence: none for the included declarations.

### Validation

Run in `external/TauCeti` on the branch (see the build log
`dev/tauceti/migration-build-log-2026-07-24.md`):

```
lake build (cluster targets, warningAsError=true)  # PASS — 3036 jobs, no warning/error
#print axioms (all cluster decls)                  # PASS — {propext, Classical.choice, Quot.sound} only
module-system                                      # PASS by construction (module + @[expose] public section, built under warningAsError)
```

`lake exe axioms`, `lake exe module-system`, and `bash scripts/lint-env.sh`
enumerate the whole `TauCeti` tree and so need a full `lake build TauCeti` (run
in CI). Locally the cluster modules were validated individually: they build
warning-clean under `warningAsError=true`, every declaration is axiom-clean by
`#print axioms`, and every file is a `module`. See
`dev/tauceti/migration-build-log-2026-07-24.md`.

### Downstream validation

The same declarations, staged in `ForTauCeti`, build warning-clean as a library
in the Davis–Kahan workspace and are consumed by the Davis–Kahan
approximation-number cluster; the post-merge import switch was simulated (see
`dev/tauceti/migration-build-log-2026-07-24.md`).

---

## Safe push command (do NOT run without explicit instruction)

New branch, create-only, force-with-lease against an empty expected value (per
`external/TauCeti/COORDINATION.md` §1):

```sh
git -C external/TauCeti push --force-with-lease=approximation-numbers: \
    https://github.com/TauCetiProject/TauCeti.git HEAD:approximation-numbers
```

Before pushing: claim the roadmap target per COORDINATION §4
(`author/spectral-subspace-perturbation/<accepted-target-id>`), confirm the
canonical `tauceti-target` id, and confirm the observed `origin/main` head is
still `92c79e5e0a618f8c5c2b9909be1ce50f6891dde7` (re-fetch; if it moved, rebase
the branch onto the new head first).

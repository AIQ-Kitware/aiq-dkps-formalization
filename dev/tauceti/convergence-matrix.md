# Convergence matrix — collapsing three operator-theory stacks into one

**Status:** primary Tau Ceti planning artifact (supersedes the extraction
manifest as the central document). Authored 2026-07-24.

## Why this exists

The near-term job is **not** "copy `ForMathlib` files to `ForTauCeti`, then submit
them." That framing skips the phase that actually matters. We currently carry
**three independently evolved operator-theory stacks**:

```text
DKPS local abstractions        (ForMathlib/*, DavisKahan/*, our ClosedOperator, CoerciveFormData, …)
Tau Ceti canonical abstractions (LinearPMap-based generators, Lax–Milgram, Fredholm, semigroups, …)
Spectra donor abstractions      (SelfAdjointOperator, PVMs, Borel calculus, polar/HS/trace, …)
```

The objective is not to preserve our architecture upstream. It is to produce
**one coherent Tau Ceti-native stack** and rewrite Davis–Kahan to consume it,
**without losing the genuinely new Davis–Kahan mathematics or Spectra
provenance**. Most Tau Ceti PRs must wait on the relevant convergence wave; the
one exception is the approximation-number cluster (Track A), which is largely
independent of Tau Ceti's semigroup / PDE / unbounded-operator architecture and
can proceed now.

This document is the **convergence matrix**: one row per public declaration (or
small declaration family), classifying it and recording its canonical
destination. It, not a file-level extraction manifest, is what tells us whether a
theorem is ported, rewritten, deleted, or kept downstream.

## Declaration classification (five classes)

Every relevant declaration gets exactly one class. This is a **declaration-level**
judgment, not a file-level one.

| Class | Meaning | Action |
| --- | --- | --- |
| **Exact duplicate** | Same definition/theorem already exists in Tau Ceti (or Mathlib) | Delete ours; repoint consumers |
| **Wrapper duplicate** | Our object merely bundles/renames theirs | Replace with a thin temporary adapter |
| **Parallel formulation** | Same mathematics, incompatible structures | Rewrite our theorem over Tau Ceti's structure |
| **Missing reusable result** | Tau Ceti lacks it; Spectra or DKPS has it | Port/generalize into Tau Ceti with provenance |
| **Paper-specific** | Depends on Davis–Kahan terminology/numbering | Keep downstream in `DavisKahan/` |

## Matrix row schema

Each row of the matrix (tables below, filled incrementally) carries:

```text
Local declaration        — our FQN(s)
Tau Ceti counterpart     — canonical FQN or "none"
Spectra counterpart      — donor FQN or "none"
Relationship             — one of the five classes
Canonical destination    — final Tau Ceti module (or DavisKahan for paper-specific)
Required semantic changes — generality/scalar/universe/structure changes needed
Current downstream users  — who imports it now (for repointing)
Temporary adapter         — DavisKahan/Interop/TauCeti/ shim, if any
Deletion condition        — when the local/Spectra original is removed
Upstream roadmap / PR     — the ForTauCetiRoadmap area this maps to
```

## Two tracks, in parallel

- **Track A (now): approximation numbers.** Deduplicate (Wave 1) and polish the
  approximation-number cluster, then pursue
  [`ForTauCetiRoadmap/ApproximationNumbers`](../../ForTauCetiRoadmap/ApproximationNumbers/README.md).
  Independent of the unbounded/semigroup/PDE architecture, so it does not block
  on Track B.
- **Track B (now): convergence audit.** Perform the convergence audit and
  refactor waves for closed operators, semigroups, forms/Fredholm, PVMs, polar
  decomposition, and Hilbert–Schmidt theory. Gates the *later* PRs.
- **Later PRs:** authored only after the relevant Track B wave is complete.

## Revised overall ordering

```text
0. Inventory and equivalence map      (this matrix, filled to the declaration level)
1. Internal deduplication             (Wave 1 — the ForTauCeti/ForMathlib twins)
2. Refactor onto existing Tau Ceti structures   (Waves 2, 4)
3. Port missing Spectra foundations into Tau Ceti (Waves 3, 5)
4. Rewrite DavisKahan consumers
5. Delete old local and Spectra APIs
6. Polish and submit the residual new mathematics
```

NOT: `copy ForMathlib → ForTauCeti → submit`.

## Wave 1 — status (2026-07-24)

- **Done (commit `f73d9e7`):** the approximation-number cluster deduped. The five
  `ForMathlib/Analysis/Normed/Operator/ApproximationNumber*` originals were
  deleted; the four live ones map to the existing `ForTauCeti` twins
  (`Basic`/`Adjoint`/`MinMax`/`FiniteDimensional`), `ApproximationNumberHilbert`
  was a declaration-free aggregate with 0 consumers and was deleted. Consumers
  repointed (FQNs unchanged — `ContinuousLinearMap.*` dot-notation). Exactly one
  importable `ContinuousLinearMap.approximationNumber`. No alternates warranted
  (statements+proofs were byte-identical). Gates green: layer OK (672 modules),
  census CLEAN, frontier 80/80 textual.
- **Blocked — the CourantFischer dedup pulls a runaway closure.** Closed under
  both forward imports and reverse ForMathlib importers (firewall), CourantFischer
  drags **42 of 54** ForMathlib modules — the whole singular-value / UI-norm /
  frame subgraph **plus an unrelated probability/statistics subsystem**
  (`Probability/Moments/*`, `MeasureTheory/CfcMeasurable`, matrix-measurability).
  The attaching edges to break first: `EntrywiseEigenvalue → CourantFischer`
  (drags stats via `EntrywiseEigenvalue → MatrixConcentration → SampleCovariance
  → …`) and the `KyFan → {Spectrum, PolarDecomposition, ProjectionGeometry}`
  norm/frame tangle. **Decision needed (phase 0):** classify the
  probability/statistics subsystem as its own component (likely its own migration
  or DavisKahan-bound), and sever `EntrywiseEigenvalue → CourantFischer`, before
  CourantFischer can dedup. Do NOT migrate the 42-file runaway as one blob.
- **Regression surfaced (maintenance-track, pre-Wave-1):** two DavisKahan modules
  are build-broken at HEAD because an earlier leaf migration
  (`OperatorAbsoluteValue`, `SelfAdjointGapInverse` → ForTauCeti) moved
  `operatorAbs` and `IsSelfAdjoint.exists_two_sided_inverse_of_spectrum_gap` out
  of `ForMathlib` without repointing these consumers:
  `DavisKahan/TanTheta/UnboundedGenuineSpectrum` (needs
  `TauCeti.IsSelfAdjoint.exists_two_sided_inverse_of_spectrum_gap` from
  `ForTauCeti/Analysis/CStarAlgebra/SelfAdjointGapInverse`) and
  `DavisKahan/Sources/DavisKahan1970/SineTheta/Sharpness` (needs
  `TauCeti.operatorAbs` from `ForTauCeti/Analysis/InnerProductSpace/OperatorAbsoluteValue`).
  Stale oleans masked this; it drops the frontier Lean-resolution probe to "not
  available". Being repaired.

## Refactor waves

### Wave 1 — internal deduplication (Track A; can begin immediately)

The staging already contains deliberate duplicate copies. This must become
active work, ahead of any PR prep:

1. Pick the intended Tau Ceti-form API.
2. Repoint all `ForMathlib` and `DavisKahan` consumers.
3. Delete the old definitions.
4. Add a check preventing both copies from being importable (extend
   `scripts/check_dependency_layers.py`).
5. Ensure exactly one canonical fully-qualified declaration name.

Known duplicate families (see matrix): Courant–Fischer infrastructure;
approximation-number definitions and lemmas; approximation-number
adjoint/min–max/singular-value files; some operator-absolute-value
infrastructure. Mechanical; runs alongside roadmap discussion.

**Preserve interesting alternate proofs.** Deduplication removes duplicate
*declarations* (exactly one importable copy of each fully-qualified name), but a
*materially different and mathematically interesting proof* of the same statement
is worth keeping. When two copies prove the same result by genuinely different
methods, keep one canonical declaration and move the alternate proof — renamed so
it does not collide with the canonical name, with a docstring noting it is an
alternate — to an `Alternates` folder: `DavisKahan/Alternative/` for paper-facing
alternates, `ForTauCeti/.../Alternates/` (mirroring the module path) for reusable
ones. The alternate must still compile and pass all gates. This is a judgment
call: keep alternates only for genuinely interesting methods, not routine
variations; when in doubt, keep and flag it.

### Wave 2 — canonical unbounded-operator refactor onto `LinearPMap`

Three representations of an unbounded operator currently coexist and **must not
all survive as peer public APIs**:

- DKPS `ClosedOperator` — bundles domain, action, density, closed graph.
- Tau Ceti — Mathlib `LinearPMap` directly; the semigroup generator *is* a
  `LinearPMap` so it composes with Mathlib's unbounded-operator API.
- Spectra `SelfAdjointOperator` — bundles a `LinearPMap` with `IsSelfAdjoint`;
  density/symmetry derived, not stored.

Canonical design: **`LinearPMap` + properties** (`IsClosed`, `IsSelfAdjoint`,
dense domain), with thin bundled objects only where they materially improve an
API. Our `ClosedOperator` becomes, at most, a temporary downstream adapter; its
useful results (`SameDomain`, `MapsDomainTo`, bounded extensions, restrictions,
relative bounds, resolvent facts) are reformulated directly over `LinearPMap`.

Refactor onto `LinearPMap`: closedness/dense-domain predicates; self-adjointness
and symmetry; same-domain relations; domain transport under bounded maps;
bounded extensions and full-domain totalization; reducing subspaces and
restricted operators; closed Sylvester equations; unbounded graph and Riccati
operators.

Temporary adapters live under `DavisKahan/Interop/TauCeti/`; they are **not**
upstream candidates. **Completion criterion:** *no production theorem takes DKPS
`ClosedOperator` as its fundamental unbounded-operator representation unless it is
a compatibility wrapper.* Must precede any closed-operator / reducing-restriction
/ unbounded-Sylvester / unbounded-Davis–Kahan PR.

### Wave 3 — semigroup and resolvent convergence

Tau Ceti already has C₀ semigroups, `LinearPMap` generators, generator domains,
resolvents and resolvent identities, contraction-semigroup and power bounds.
Spectra also has Yosida–Hille / semigroup spectral machinery — **do not port that
subsystem wholesale.** Instead:

1. Rebuild our semigroup-dependent proofs on Tau Ceti's semigroup/generator
   objects.
2. Inventory the precise missing lemmas.
3. Port only the missing pieces — likely complex-vs-real scalar support; unitary
   *groups* not one-sided semigroups; self-adjoint-generator bridges; spectral-gap
   flow estimates; functional-calculus identification of the generated flow.
4. Keep those as focused Tau Ceti additions.

`FourierSemigroup`, the Hilbert–Schmidt generator bridge, and parts of the
unbounded Sylvester theory are **blocked** until this convergence is done.

### Wave 4 — coercivity, forms, PDE, and Fredholm reconciliation

Tau Ceti already has Lax–Milgram, energy forms, ellipticity, PDE, and Fredholm
infrastructure. Our free-beam/coercive-form work cannot upstream as a parallel
hierarchy. Compare our `CoerciveFormData`, `formOperator`, `solutionOperator`,
`associatedOperator`, compact graph embedding against Tau Ceti's Lax–Milgram API,
energy forms, ellipticity/Fredholm predicates and index, PDE realization.

Likely outcome: delete or greatly shrink `CoerciveFormData`; express its solution
operator via Tau Ceti Lax–Milgram; reuse Tau Ceti Fredholm/energy-form
structures; retain only genuinely new compact-resolvent and fourth-order beam
results; treat the free-beam example as a downstream consumer / test case.

### Wave 5 — Spectra decomposition and porting

The latest archive has **≈59 direct Spectra import lines** over a much larger
transitive closure. These form distinct donor clusters, handled separately.

- **Cluster A — self-adjoint unbounded operators.** Spectra's `LinearPMap`-based
  self-adjoint layer + derived closedness/symmetry. Port only missing general
  lemmas after comparing with Mathlib/Tau Ceti; do not preserve
  `Spectra.Operator.SelfAdjointOperator` for compatibility if a property-based
  Tau Ceti API is preferred. (Coordinated with Wave 2.)
- **Cluster B — PVMs and spectral calculus.** The largest genuinely missing
  foundational layer: projection-valued measures, spectral projections, bounded
  and unbounded Borel calculus, spectral restriction, generator links, spectral
  localization, real/complex descent. Tau Ceti does not supersede this; Spectra
  is a real donor. **Needs its own roadmap** (not the approximation-number one):
  identify the minimal DK-needed slice → coordinate with Spectra's author → port
  dependency-closed modules to canonical Tau Ceti locations → preserve license +
  declaration provenance → rewrite DKPS bridges → remove the Spectra imports.
- **Cluster C — polar decomposition and partial isometries.** Overlapping local
  and Spectra implementations. Choose one canonical Tau Ceti partial-isometry /
  polar API; port missing support/range/kernel lemmas; rewrite operator-angle and
  direct-rotation proofs onto it; delete local duplicate positive-square-root and
  polar wrappers.
- **Cluster D — Hilbert–Schmidt and trace class.** Reconcile, do not select from
  one side: Tau Ceti owns **one** HS predicate and norm; basis-column, tensor,
  approximation-number, and finite-Frobenius characterizations become
  equivalence theorems for that one object; Spectra trace-class results ported
  only after the API is settled; DK's arbitrary-ideal layer consumes the
  canonical implementation. (Coordinates with Track A Layer C.)
- **Cluster E — separated spectra and intertwiners.** Keep Spectra's general
  spectral facts; keep our genuinely new norm estimates; reformulate both over
  the same operator/spectrum APIs; remove bridge structures such as
  `GenuinePairwiseSpectrumGap` when a simpler predicate over canonical spectra
  suffices.

## Seed matrix (to be filled to the declaration level)

Concrete rows we already know; expand each into the full schema during phase 0.

| Local declaration | Tau Ceti counterpart | Spectra counterpart | Class | Canonical destination | Roadmap |
| --- | --- | --- | --- | --- | --- |
| `ContinuousLinearMap.approximationNumber` (ForMathlib + ForTauCeti twins) | none (candidate upstream) | none | Exact duplicate (internal) | `ForTauCeti/…/ApproximationNumber/Basic` (single copy) | ApproximationNumbers |
| CourantFischer infra (ForMathlib + ForTauCeti twins) | partial (fin-dim spectral) | none | Exact duplicate (internal) | `ForTauCeti/…/InnerProductSpace/CourantFischer` (single copy) | ApproximationNumbers |
| approx-number adjoint / min–max / singular-value files (twins) | none | none | Exact duplicate (internal) | `ForTauCeti/…/ApproximationNumber/*` (single copy) | ApproximationNumbers |
| operator-absolute-value infra (partial twins) | partial (CFC.sqrt) | polar/HS layer | Wrapper/Parallel | consolidate on CFC `|T|` | ApproximationNumbers (Layer B) / Cluster C |
| DKPS `ClosedOperator` (+ SameDomain, MapsDomainTo, extensions, restrictions, relative bounds, resolvent) | `LinearPMap` + property predicates | `SelfAdjointOperator` | Wrapper/Parallel | `LinearPMap`-based; `ClosedOperator` → `DavisKahan/Interop/TauCeti/` adapter | (spectral-perturbation, later) |
| `CoerciveFormData`, `formOperator`, `solutionOperator`, `associatedOperator`, compact graph embedding | Lax–Milgram / energy forms / Fredholm | — | Wrapper/Parallel | shrink onto Tau Ceti Lax–Milgram; keep only new compact-resolvent/beam results | (PDE/forms, later) |
| PVM / spectral projection / Borel calculus bridges | none | PVM + Borel calculus layer | Missing reusable result | new **spectral-calculus roadmap** area, canonical Tau Ceti location | (spectral calculus, its own) |
| polar decomposition / partial isometry (local + Spectra) | partial | polar/partial-isometry layer | Parallel | one canonical Tau Ceti polar/partial-isometry API | (spectral-perturbation, later) |
| Hilbert–Schmidt / trace class (column-expansion + approx-number + Spectra tensor) | partial | HS/trace tensor layer | Parallel | one HS predicate+norm; others are equivalence theorems | ApproximationNumbers (C) + Cluster D |
| Sylvester uniqueness/estimates + `GenuinePairwiseSpectrumGap` | resolvent/spectrum API | separated-intertwiner results | Parallel | reformulate over canonical spectra; drop bridge predicate | (spectral-perturbation, later) |

## Relationship to existing artifacts

- `dev/tauceti/extraction-manifest.json` — demoted from central doc to a
  file-level inventory feeding phase 0 of this matrix.
- `dev/tauceti/formathlib-to-fortauceti-migration.md` — the firewall-ordered
  mechanics of Wave 1 (the ForTauCeti/ForMathlib dedup); still valid, now scoped
  as Wave 1 rather than the whole program.
- `docs/planning/tauceti-adaptation-and-spectra-extraction.md` — the dual-track
  policy and acceptance gates; this matrix is its phase-0 instrument.
- `ForTauCetiRoadmap/` — the roadmap drafts; the "Roadmap / PR" column points
  here.

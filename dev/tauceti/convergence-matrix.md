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
- **Phase-0 decision RECORDED (2026-07-24, edward): the probability/statistics
  subsystem is its own convergence cluster.** Evidence gathered at the
  declaration level: the chain is *linear* —
  `SampleCovariance → MatrixConcentration → EntrywiseEigenvalue →
  CourantFischer` — and the trio
  `{SampleCovariance, MatrixConcentration, EntrywiseEigenvalue}` has **zero**
  paper/DavisKahan consumers (only the `ForMathlib.lean` aggregate and
  `Challenge/MathlibPending/*` leaderboards). Its remaining ForMathlib deps
  (`EntrywiseOpNorm`, `SpectralFunctionMeasurable`, `CfcMeasurable`) have only
  repoint-style consumers (`DkpsQuench2026/Geometry/Covariance`,
  `Acharyya2025/OperatorBridge` import `EntrywiseOpNorm` directly).
  **Classification:** its own ForTauCeti-bound cluster (destination
  `ForTauCeti/Probability/Moments/**` + the matrix-measurability files under
  `ForTauCeti/Analysis/Matrix/**`), its own roadmap area and PR slice —
  *not* DavisKahan-bound (the material is reusable, Mathlib-candidate-grade).
  Because the firewall forbids `ForMathlib → ForTauCeti` imports and the chain
  is linear with no external consumers, "severing
  `EntrywiseEigenvalue → CourantFischer`" is realized not by refactoring the
  proof but by having the stats chain **ride the same dedup commit** as the
  singular-value component while remaining a separate roadmap/PR unit.
  (Alternative rejected: parking the trio in a paper layer — it serves no
  paper and would demote reusable mathematics.) The `KyFan → {Spectrum,
  PolarDecomposition, ProjectionGeometry}` edges are all *inside* the
  singular-value component, so they enlarge no closure and need no severing.
- **DONE (2026-07-24, edward): the CourantFischer dedup wave landed.** The
  37-module weakly-connected component (singular-value/UI-norm/frame subgraph
  + statistics cluster) migrated to `ForTauCeti` in one commit;
  `ForMathlib/CourantFischer.lean` deleted; consumers repointed (historical
  signatures ride the transitional `CourantFischerCompat` shim; paper files
  extending the library namespace now extend `TauCeti`). `ForMathlib` is down
  to 12 modules. Module-system conversion of the moved files is deferred to a
  dedicated mechanical pass (see the migration doc for why). Gates: full build
  9266 green, layer check 684 OK, census CLEAN.
- **CourantFischer final API landed (2026-07-24, edward).** The ForTauCeti
  copy no longer mirrors the ForMathlib names: the P0 redesign of
  `dev/tauceti-signature-polish-todo.md` §6 is executed
  (`OrthonormalBasis.spanIndices` in the new `BasisSpan.lean`; eigenvalue API
  in the `LinearMap.IsSymmetric` namespace; the genuine sup-inf
  Courant–Fischer equality `eigenvalues_eq_iSup_iInf_re_inner`; Weyl at
  `ContinuousLinearMap` level with `‖T − S‖`). The dedup therefore repoints
  the 17 ForMathlib consumers **once, straight to the final names** — see the
  name map in `formathlib-to-fortauceti-migration.md`.
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

## Mechanical duplicate audit (edward, aiq-gpu, 2026-07-28)

The matrix is supposed to carry one row per duplicate declaration.  These rows
were found mechanically rather than by reading, and were not in the matrix.

**The check, so it is repeatable.**  Normalise the body of every `def`/`abbrev`
in `DavisKahan/`, `ForTauCeti/`, `ForMathlib/` (excluding `Experimental/**` and
`Scratch/**`) to a single whitespace-collapsed string, keep bodies of 20–250
characters, and group by body text.  640 bodies, **9 groups shared by more than
one name**.  Body-text matching ignores types, so every hit needs confirming by
hand — one did not survive that (below).

### Row: `IsOrthogonalProjection` — exact duplicate, blocked on governance

```text
Local declaration        — TauCeti.DavisKahan.Experimental.Foundation.IsOrthogonalProjection
                           (DavisKahan/SpectralTheory/AbstractSpectrum.lean:59)
                         — IsOrthogonalProjectionMap
                           (DavisKahan/OperatorIdeal/ApproximationNumbers/Core.lean:48)
Tau Ceti counterpart     — none
Spectra counterpart      — none
Relationship             — Exact duplicate (identical type AND identical body,
                           `P ∘L P = P ∧ P.IsSymmetric`)
Canonical destination    — a ForTauCeti bounded-operator module, alongside
                           `TauCeti.LinearPMap.IsUnitaryOperator`
Required semantic changes — none; the two are already the same proposition
Current downstream users  — both are live: 23 occurrences of the first, 26 of
                           the second
Temporary adapter         — none yet
Deletion condition        — once a canonical declaration exists, both become
                           reducible abbrevs over it and the duplicate `def`s go
Upstream roadmap / PR     — needs an accepted roadmap target first (see below)
```

**Why this was not simply fixed.**  It is the same shape as the
`IsUnitaryOperator` collapse landed earlier today — two byte-identical `def`s
under different names — but the fix does not transfer.  `IsUnitaryOperator` had
a canonical `ForTauCeti` copy already, so collapsing was a local edit.  Here
there is none, and:

- neither module reaches the other in the import graph, so making one an abbrev
  of the other would introduce a `SpectralTheory` ↔ `OperatorIdeal` edge purely
  to deduplicate a one-line predicate;
- creating the canonical `ForTauCeti` declaration is the right answer, but
  AGENTS.md gates that — "Tau Ceti admits new mathematical declarations only
  against an accepted roadmap target, one topic per PR".

So this is a roadmap question, not a cleanup.  Recorded here rather than
actioned.

### Other groups from the same audit

| bodies shared by | verdict |
| --- | --- |
| `ClosedOperatorE` / `ClosedOperatorAmbient` / `DirectClosedOperatorOnE` (and the `F` variants), `ComplexClosedOperatorH` / `DKClosedOperator` | **not duplicates to collapse** — per-file local abbrevs for the same bundled type. They disappear with the bundle itself, so U1 subsumes them |
| `Plane` / `PaperPlane` (`EuclideanSpace 𝕜 (Fin 2)`), `RealPlane` / `PaperRealPlane` | duplicate abbrevs across `FiniteDimensional/Sharpness`, `SinTheta/Natural/Examples` and `Sources/.../Sharpness`. Low value, but the paper-facing and general spellings should not both exist once the source layer settles |
| `paperScalarColumn` / `finiteMultiplicityScalarColumn` (`(ContinuousLinearMap.id 𝕜 𝕜).smulRight v`) | **not a duplicate — a generality inversion, which is the more interesting defect.** `finiteMultiplicityScalarColumn` is general in `H`; `paperScalarColumn` is the same body pinned to `PaperPlane 𝕜`, and its body never uses the plane structure. The general one is therefore an instance-for-instance replacement for the special one — except that `FiniteMultiplicity.lean` **imports** `Sharpness.lean`, so **the general declaration sits downstream of the special one and cannot be used by it**. Collapsing means generalising `paperScalarColumn` in place and deleting the downstream copy. Left alone here because it changes a signature in `Sources/**`, which is source-fidelity territory and phase-C adjacent |
| `directedSinThetaOperatorProseLike` / `directedSinThetaOperatorClassicalProseLike` | **intentional** — the `Alternative/**` prose-like API deliberately carries parallel spellings |
| `RectangularUnitarilyInvariantNorm.toSquare` / `toRectangular` | **false positive, and worth recording as one.** Identical field-copying bodies, but *opposite directions* between `RectangularUnitarilyInvariantNorm 𝕜 E E` and `UnitarilyInvariantNorm 𝕜 E`. Body-text matching cannot see this; the types must be compared too |

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

> **STATUS: ACTIVE AND CLAIMED (2026-07-27). This is implementation work, not an
> open representation discussion.** See `dev/tauceti/u1-linearpmap-migration.md`
> and the corresponding row in `dev/LANES.md`.

Three representations of an unbounded operator currently coexist and **must not
all survive as peer public APIs**:

- DKPS `ClosedOperator` — bundles domain, action, density, and closed graph;
- Tau Ceti — uses Mathlib `LinearPMap` directly; a semigroup generator is a
  `LinearPMap`, so it composes with Mathlib's unbounded-operator API;
- Spectra `SelfAdjointOperator` — stores a `LinearPMap` with self-adjointness and
  derives density/symmetry rather than storing an independent domain/action pair.

The canonical design is forced: **`LinearPMap` plus properties**. Closedness,
dense domain, symmetry, and self-adjointness are facts about the partial linear
map. A thin bundle may be introduced later only when a concrete Tau Ceti API
benefits from it; it may not become a second foundational universe.

There is no remaining roadmap decision that blocks local convergence. In
particular, agents must not preserve `ClosedOperator` merely because a direct
signature migration temporarily breaks consumers. The required technique is:

1. add the canonical `LinearPMap` theorem first;
2. make the historical bundled declaration a thin adapter or derived wrapper;
3. repoint consumers in dependency order;
4. keep every committed step green;
5. delete the adapter once the last production consumer is gone.

#### U1.1 — dependency-clean reusable core

Create a `ForTauCeti` layer whose public declarations are stated directly over
`E →ₗ.[𝕜] F`. Reuse pinned Mathlib declarations rather than redefining them.
The first closure includes:

- closedness and densely-defined predicates/lemmas;
- symmetry and self-adjointness consequences;
- domain equality / extension relations;
- domain transport by bounded maps;
- bounded extensions and full-domain embeddings of continuous linear maps;
- graph norm and relative boundedness on the domain subtype;
- bounded perturbation closedness where it is dependency-clean.

The core may import only Mathlib, Tau Ceti, and `ForTauCeti`. It may not import
DavisKahan or Spectra.

#### U1.2 — downstream compatibility seam

Move the historical bundle behind
`DavisKahan/Interop/TauCeti/ClosedOperator.lean`. The adapter may preserve old
field projections, coercions, and theorem names temporarily, but it must be
implemented from the canonical `LinearPMap` API and must be documented as
transitional. No `ForTauCeti` module may import it.

#### U1.3 — production consumer migration

Migrate consumers by mathematical dependency rather than directory size:

1. same-domain, maps-domain-to, extensions, graph norm, and relative bounds;
2. reducing restrictions and restricted operators;
3. closed Sylvester equations and unbounded norm estimates;
4. graph/Riccati inputs and unbounded perturbation endpoints;
5. Spectra-facing bridges, while keeping the Spectra-specific spectral calculus
   isolated downstream.

Completed Davis--Kahan theorem statements should remain stable unless the old
bundle itself leaks into the public statement. When it does, replace it with the
`LinearPMap` statement and retain a source-facing compatibility corollary only
when the paper API requires one.

#### Explicit deferrals, not blockers

The following do not block the core migration and remain separate lanes:

- PVM/Borel functional calculus and spectral projections;
- Spectra real-spectrum and resolvent identification proofs;
- real-to-complex closed-operator complexification;
- source-facing theorem redesign unrelated to the representation;
- semigroup theorem additions beyond adapting to Tau Ceti's existing generator.

#### Completion gates

Wave 2 is complete only when:

- no generic production theorem takes DKPS `ClosedOperator` as its fundamental
  unbounded-operator representation;
- the reusable API is dependency-clean and stated over `LinearPMap`;
- `ClosedOperator` is confined to an explicitly temporary interoperability or
  source-compatibility layer, or deleted;
- the direct consumer count and import graph are recorded and monotonically
  shrinking;
- default targets and focused migrated targets build after each committed slice;
- dependency-layer, source-census, and trusted-dependency checks remain clean.

This wave must precede any Tau Ceti PR for closed operators, reducing
restrictions, unbounded Sylvester equations, or unbounded Davis--Kahan results.
It does **not** need to wait for those theorem PRs before starting.

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

> **The Spectra half of this is now filled** — see
> [`spectra-to-tauceti-port-ledger.md`](spectra-to-tauceti-port-ledger.md) and its
> machine-readable companion [`spectra-port-surface.json`](spectra-port-surface.json)
> (2026-07-28). Measured from the compiled environment rather than from import
> lines: the production surface is **61 Spectra constants** across **27 donor
> modules**, consumed by **178 declarations in 42 `DavisKahan` modules** — not the
> "≈59 direct Spectra import lines" over a 152-module closure that Wave 5 sizes
> it by. `ForTauCeti` and `ForMathlib` are already entirely Spectra-free. The
> ledger also adds **Cluster F** (Cayley / Stone / one-parameter groups), which
> Wave 5 folded into Wave 3 but which has its own DKPS consumer surface, and
> **Cluster X**, the 14 DKPS-authored theorems currently declared into
> `namespace Spectra.*` — a provenance defect, not donor material.
>
> Wave 5's *execution* now lives in
> [`spectra-removal-plan.md`](spectra-removal-plan.md) (phases S0–S6, claimed).
> One correction to Wave 5's implied ordering: **Cluster F has no single-cluster
> consumers**, so it cannot be closed independently of B — B and F converge last,
> and the size-ordered intuition is wrong.

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
| Sylvester uniqueness/estimates + `GenuinePairwiseSpectrumGap` | `LinearPMap` equation/domain API; no canonical spectrum API yet | separated-intertwiner results | Spectra-dependent parallel formulation | **2026-07-28:** raw `LinearPMap.GenuinePairwiseSpectrumGap` and `linearPMapSylvester_*` now own the implementation in `DavisKahan/Sylvester`; keep the bundled predicate and three old theorem signatures only for the seven source/audit consumers until those data records migrate | (spectral-perturbation, later) |

## Completion-lane seed rows: `FinishTanTwoTheta` and `FinishYuWangSamworth`

Added 2026-07-28 by jon (toothbrush). Neither completion lane had a single row
in this matrix, so both were invisible to the convergence plan even though they
are the two libraries that carry the remaining paper mathematics. Declaration
lists below are **measured from the trees**, not guessed; the classifications
are first-pass and each one flagged *(verify)* still needs the counterpart
diffed before any code moves.

Both libraries are non-default Lake targets sharing the root dependency graph.
`FinishYuWangSamworth` builds clean and sorry-free; `FinishTanTwoTheta` builds
except for one declaration (see
[`../finishtantwotheta-completion-lane.md`](../finishtantwotheta-completion-lane.md)).

### `FinishYuWangSamworth` (37 declarations, 1207 lines)

| Local declaration | Tau Ceti / ForTauCeti counterpart | Class | Canonical destination |
| --- | --- | --- | --- |
| `yuWangSamworth_theorem1_{uiNorm,frobenius,opNorm}_le` | none | Paper-specific | paper package (`YuWangSamworth/`), not `ForTauCeti` |
| `yuWangSamworth_{right,left}SingularSubspace{,_opNormCoefficient}_le` | `…/InnerProductSpace/SingularSubspace` *(verify)* | Paper-specific conclusion over reusable core | paper package; core to `SingularSubspace` |
| `yuWangSamworth_{right,left}SingularAlignedBasis{,_opNormCoefficient}_le` | `…/InnerProductSpace/AlignedBasis` *(verify)* | Paper-specific conclusion over reusable core | paper package; core to `AlignedBasis` |
| `yuWangSamworth_{right,left}SingularVector{,_opNormCoefficient}_le` | none | Paper-specific | paper package |
| `yuWangSamworth_lemma5_{columns,rows,isometricColumns,orthonormalColumns,orthonormalRows}` | `…/InnerProductSpace/{FrameFactorization,NearIsometry}` *(verify)* | Parallel formulation | reusable core to `ForTauCeti`; wrappers stay |
| `yuWangSamworth_equation4`, `yuWangSamworth_equation4_printed_counterexample` | none | Paper-specific | paper package — this is a **source-defect record** and must not be silently dropped |
| `CorrespondingRightSingularBlock`, `CorrespondingLeftSingularBlock`, `RightSingularPopulationGap`, `LeftSingularPopulationGap` | none | Paper-specific predicates | paper package |
| `rectangularFrobenius_adjoint`, `rectangularFrobenius_twoSided_comp_le`, `frobenius_comp_rectangular_le_opNorm_mul` — **BLOCKED, see note below the table** | **none — verified 2026-07-29.** `ForTauCeti/…/RectangularUnitarilyInvariantNorm/Instances` has `frobenius_apply`, `frobenius_linearIsometry_comp`, `frobenius_projection_comp_le`, `frobenius_subtype_comp`, `frobenius_eq_sqrt_sum_sq_singularValues` — but no adjoint-invariance and no two-sided ideal bound | **Missing reusable result** (not a duplicate; my first-pass guess was wrong) | `…/RectangularUnitarilyInvariantNorm/Instances`, beside the existing `frobenius_*` family |
| `frobenius_{right,left}Gram_sub_le{,_paperCoefficient}`, `opNorm_{right,left}Gram_sub_le_paperCoefficient` | `…/InnerProductSpace/GramMatrix` *(verify)* | Missing reusable result | Gram-perturbation layer |
| `opNorm_eq_topSingularValue` | `TauCeti.opNorm_eq_singularValues_zero` in `…/InnerProductSpace/TwoDimensionalSingularValues` — **verified duplicate 2026-07-29**, identical proof, strictly more general (dimension explicit rather than `[Nontrivial E]`) | Wrapper duplicate — **DEDUPED 2026-07-29** | now a one-line wrapper carrying no proof; inline it at migration |
| `sum_opNorm_le_paperCoefficient` | none | Paper-specific coefficient | paper package |

### `FinishTanTwoTheta`

| Local declaration | Tau Ceti / ForTauCeti counterpart | Class | Canonical destination |
| --- | --- | --- | --- |
| `WeaklySubmajorized` (on `ℕ → ℝ`), `sequencePrefixSum`, `sequencePrefixVector`, `finitePrefixSum_sequencePrefixVector`, `finite_weaklyMajorized_of_weaklySubmajorized` | `ForTauCeti/Analysis/Convex/Majorization.WeaklyMajorized` (on `Fin n → ℝ`) — landed by jon (namek) | **Missing reusable result — the infinite-sequence extension.** *Not* a duplicate: checked 2026-07-28, the Tau Ceti object is indexed by `Fin n`, this one by `ℕ`, and `finite_weaklyMajorized_of_weaklySubmajorized` is the bridge between them | `Analysis/Convex/Majorization` as a second section. The four order lemmas (`refl`, `trans`, `of_pointwise`, `nonneg_smul`) are stated twice, once per index type — that lemma-level parallelism is the only real duplication, and it is the kind that is normally left alone rather than unified |
| `exists_gauge_decomposition_of_weaklyMajorized`, `exists_l1_paperGauge_decomposition_of_weaklyMajorized` | none | Missing reusable result | gauge-decomposition layer beside `FiniteSymmetricGauge` |
| `sequenceGauge`, `sequencePrefixGauge`, `sequenceExtendedGauge`, `SequenceMem`, `paperFiniteSymmetricGauge` | `ForTauCeti/Analysis/Normed/FiniteLpGauge` *(verify)* | Parallel formulation | one symmetric-gauge API |
| `StandardSymmetricIdeal` (+ `Mem`, `gauge`, `mem_adjoint`, `gauge_adjoint`), `StandardSymmetricCompletion` | `RectangularSymmetricIdealFamily` / `SymmetricOperatorIdealFamily` | Parallel formulation — **collides with §13.2 adapter retirement** | one canonical symmetric-ideal family; coordinate with the §13.2 sweep before moving |
| `FiniteRankGaugeClosure`, `MinimalFullySymmetricMem`, `standard_fanDominance`, `minimalFullySymmetricMem_of_kyFan_dominated` | none | **Missing reusable result** | operator-ideal layer — Fan dominance as a theorem is genuinely new |
| `paperLpNorm`, `paperOperatorNorm`, `paperLinftySymmetricNormingFunction`, `{maximal,minimal}SchattenIdeal`, `nuclearIdeal`, `{bounded,compact}OperatorNormIdeal` | `…/InnerProductSpace/SchattenNorm`, ideal `Instances` *(verify)* | Parallel / wrapper | one ideal-instances module |
| `doubleAngleTangentOperator`, `doubleAngleDenominator`, `approximationNumber_doubleAngleTangentOperator`, `doubleAngleTangent_approximationNumber_le` | none | **Missing reusable result** | the tangent operator and its approximation numbers are reusable spectral-perturbation material |
| `ApproximateLeadingSingularFamily`, `exists_approximateLeadingSingularFamily`, `GramSpectralBandModel`, `exists_gramSpectralBandModel` | none | **Missing reusable result — the most valuable thing in this library** | approximate simultaneous singular systems for an *arbitrary* bounded operator, with no compactness and no attainment assumption |
| `gramOperator`, `gramPVM`, `gramSelfAdjointOperator`, `gramUnitaryGroup` | Spectra PVM / Borel calculus | Spectra-dependent | folds into Wave 5 / spectral-calculus area; a Spectra consumer, so it gates on the removal plan |
| `finiteValue*` family, `gramBands_disjoint`, `exists_uniform_positive_separation` | none | Missing reusable (small) | finite-value/band combinatorics; low priority |
| `sharp_*` (bounded and unbounded, `stableSingularPair_*`, `unboundedStableSingularPair_*`) | none | Paper-specific | `DavisKahan/` — Davis--Kahan Section 7 |
| `UnboundedApproximateLeadingSingularFamily`, `exists_unboundedApproximateLeadingSingularFamily` | none | **BLOCKED — not proved** | do not migrate; see the lane document |

### Y3 is not independent: the Frobenius items are gated on the Hilbert--Schmidt wave

Measured 2026-07-29. The three missing-reusable Frobenius results above cannot
move to `ForTauCeti` yet. Their proofs all route through the `paperHilbertSchmidt*`
layer — `IsPaperHilbertSchmidt`, `paperHilbertSchmidtNorm`,
`paperHilbertSchmidtNorm_comp_le`, `paperHilbertSchmidtNorm_adjoint`,
`paperHilbertSchmidtNorm_eq_rectangularFrobenius`,
`paperHilbertSchmidtNorm_eq_frobenius` — which lives in
`DavisKahan/Sources/DavisKahan1970/Ideals/HilbertSchmidt.lean`.

`ForTauCeti` may import only `Mathlib` / `TauCeti` / `ForTauCeti`, so moving the
Frobenius lemmas requires the **Hilbert--Schmidt / trace-class row** of the seed
matrix ("one HS predicate+norm; others are equivalence theorems", Cluster D /
Wave 5) to land first. That row is itself gated on the Spectra removal plan.

Consequence for sequencing: **Y3 cannot be completed as an independent lane.**
What Y3 *can* do now, without waiting:

- the paper-specific rows (Theorem 1, Theorem 4 right/left, aligned-frame and
  rank-one corollaries, Lemma 5 wrappers, equation (4) and its counterexample) —
  these stay downstream by classification, so they need a paper package, not
  `ForTauCeti`, and that move is unblocked;
- the wrapper dedups against results `ForTauCeti` already has
  (`opNorm_eq_topSingularValue` is done);
- the Gram-perturbation rows, once checked the same way — they may or may not
  share the HS dependency.

The reusable *core* of Yu--Wang--Samworth reaches `ForTauCeti` only after the HS
wave. That is a real ordering constraint, not a scheduling preference, and it
should be reflected in any plan that promises "the complete YWS set" upstream.

### Ordering note

The `Majorization` row is the one that should move first: it lands beside a
module that is already in `ForTauCeti`, it is independent of the blocked seam,
and it is independent of the §13.2 ideal-family sweep. Move it as an
**addition** — the `ℕ`-indexed `WeaklySubmajorized` is new mathematics, not a
copy of the `Fin n`-indexed `WeaklyMajorized`, and deleting it would lose the
infinite-sequence theory the operator-ideal work depends on.

The `StandardSymmetricIdeal` row is the opposite — it must **not** move until
§13.2 phase C/D settles which symmetric-ideal family is canonical, or the two
efforts will produce a third parallel stack.


## Declaration-level deletion / adapter rows (from the signature audit §13)

The adversarial-review audit `dev/tauceti-signature-polish-todo.md` (baseline
`543b46f`) already classifies specific declarations. Fold these into the matrix:

| Local declaration | Class | Canonical action | Adapter / deletion |
| --- | --- | --- | --- |
| ForMathlib approximation-number copies | Exact duplicate | delete after imports point to ForTauCeti | **DONE** (Wave 1, `f73d9e7`) |
| `operatorAbs` | Wrapper (square special case of rectangular modulus) | delete definition; canonical `ContinuousLinearMap.modulus` | temporary compat in `DavisKahan/Interop/TauCeti`; delete after A4 |
| `rectangularOperatorModulus` | Parallel | rename → `ContinuousLinearMap.modulus`; unify with `operatorAbs` | — |
| `specSubspace` (+ its lemmas) | Wrapper (misnamed coordinate span) | rename/relocate → `OrthonormalBasis.spanIndices` | deprecated local alias only if needed |
| `ClosedOperator` (+ SameDomain, …) | Parallel | demote to adapter over `LinearPMap` | `DavisKahan/Interop/TauCeti`; delete from generic production (Wave 2) |
| `RectangularSymmetricIdealFamily` | Parallel (free-data gauge off carrier) | **DONE 2026-07-27** — canonical `TauCeti.OperatorIdealFamily` / `SymmetricOperatorIdealFamily` (single `ℝ≥0∞` gauge; carrier = its finiteness domain) in `ForTauCeti/Analysis/OperatorIdeal/Family/` | **2026-07-28** — `KyFanDominantIdealFamily`, the structure the whole ideal-valued sin-Θ development is parameterized over, now *stores* the canonical family; `SymmetricOperatorIdealFamily.toRectangular` survives only as its derived real-valued view. Two canonical instances exist: `operatorNormFamily` and `kyFanSymmetricIdealFamily`. Remaining: 106 direct type-position uses in 30 production modules (23 inside the concurrently-claimed U1 lane), then delete the adapter and the legacy structure |
| `GenuinePairwiseSpectrumGap` | Spectra-dependent bridge wrapper | raw `LinearPMap.GenuinePairwiseSpectrumGap` owns the proof; replace it with a canonical spectrum/set-distance predicate only after the required Spectra API is ported | bundled wrapper has seven source/audit consumers; delete after their raw-partial-map migration |
| `finiteMean` / `appendFin` | **Reclassified 2026-07-27 (§8.1): only `appendFin` was a duplicate** | `appendFin` **DELETED** — it was exactly `Fin.snoc`. `finiteMean` **KEPT**: `Finset.expect` needs `Module ℚ≥0 E`, which does not synthesize for a `𝕜`-inner-product space, and `Finset.centroid` is affine with `Classical.arbitrary` junk on the empty family, whereas `finiteMean_append` is deliberately stated to hold *at* `n = 0`. `centeredScatter` retyped to `E →L[𝕜] E` | no upstream adapter |
| `exists_two_sided_inverse_of_spectrum_gap` | **DONE 2026-07-27 (§9.1)** | split into `TauCeti.isUnit_of_forall_le_abs` + `TauCeti.IsSelfAdjoint.norm_ringInverse_le` over the canonical `Ring.inverse` (the sketched names were `isUnit_of_abs_spectrum_ge` / `norm_inv_le…`). Invertibility needs **neither** self-adjointness **nor** a C\*-algebra, so it is stated at `[Ring A] [Algebra ℝ A]` outside the `IsSelfAdjoint` namespace. Its sibling `norm_le_of_spectrum_subset_Icc` became the iff `norm_le_iff_spectrum_subset_Icc` | — |

**Note on the Wave-1 green-restoration repair — half resolved 2026-07-27.**
Repointing `UnboundedGenuineSpectrum`/`Sharpness` onto `TauCeti.operatorAbs` and
`TauCeti.IsSelfAdjoint.exists_two_sided_inverse_of_spectrum_gap` was recorded as a
**green-restoration stopgap, not a final state**, with both identifiers named as
convergence targets. That prediction has now come true for one of the two:

- **Gap-inverse: settled (§9.1).** The redesign landed, and
  `DavisKahan/TanTheta/UnboundedGenuineSpectrum` was repointed with it — as were the other
  three consumers, 8 call sites across 4 files. Nothing here is a stopgap any more.
- **`operatorAbs`: still a stopgap.** §7 made `ContinuousLinearMap.modulus` canonical but
  left `operatorAbs` as a reducible `abbrev` in a documented shim, so
  `DavisKahan/Sources/DavisKahan1970/SineTheta/Sharpness` still rides the alias. That
  repoint, and deleting the alias, remain open — see backlog §13's adapter-retirement row.

## Roadmap-level review questions (from the signature audit Appendix B)

Each drafted `ForTauCetiRoadmap/` area must answer the audit's Appendix-B review
questions for its cluster (index convention, codomain, namespace, canonical
modulus name, redundant CFC lemmas, the exact Courant–Fischer equality, bundled
`SelfAdjointOperator` vs `LinearPMap` properties, minimal PVM/Borel slice, the
single Hilbert–Schmidt object, symmetric-ideal extensionality, HZ prerequisite
placement, excluded paper aliases). The approximation-number area answers its
share in its "Open representation decisions" section.

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

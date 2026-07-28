# U1 execution contract: migrate unbounded operators to `LinearPMap`

Status: **OPEN / UNCLAIMED, released 2026-07-28** (previously claimed by
jon (toothbrush)). The canonical layer is built and the consumer migration is
partly done; see "Release state" below for exactly what is left and what is
already contractible.

This document is an implementation contract. It replaces the previous habit of
calling the closed-operator convergence problem "design-stage" after the
representation decision had already been forced by Mathlib and Tau Ceti.

## Decision

The foundational unbounded-operator object is:

```lean
A : E →ₗ.[𝕜] F
```

Closedness, dense domain, symmetry, and self-adjointness are properties of `A`.
Tau Ceti's semigroup generators already use `LinearPMap`; Spectra's
self-adjoint-operator representation is also based on `LinearPMap`. The local
DKPS `ClosedOperator` bundle must therefore become a temporary downstream
adapter and ultimately disappear from generic production signatures.

This decision is not reopened during implementation. A later reviewer may
change names or request a thin convenience bundle, but the property API remains
canonical and the bundle may not own independent domain/action data.

## Why this lane is critical

Keeping the old bundle makes every later extraction expensive:

- reducing restrictions must translate between domain representations;
- closed Sylvester equations cannot compose directly with Tau Ceti semigroup
  generators;
- Spectra bridges carry redundant wrappers;
- unbounded Davis--Kahan theorems expose a repository-local object;
- every green theorem added to the old API increases migration cost.

A green build is required after each slice, but a green build routed through the
old foundation is not completion.

## Claimed scope

Owned by this lane:

- new dependency-clean `ForTauCeti/Analysis/OperatorTheory/LinearPMap/**` modules;
- `DavisKahan/SpectralTheory/ClosedOperator/**`;
- new `DavisKahan/Interop/TauCeti/ClosedOperator.lean` adapter;
- direct production consumers migrated in dependency order, beginning with
  reducing-subspace and closed-Sylvester modules;
- documentation and manifests needed to record the migration.

Explicitly excluded:

- approximation-number §§5.1–5.4;
- `Challenge/` and `comparator/*.json` except if a declaration rename genuinely
  requires the standard drift gate;
- Spectra PVM/Borel functional calculus;
- real-spectrum bridge proofs and spectral-cutoff construction;
- real/complex closed-operator complexification in the first slice;
- unrelated source-facing theorem redesign.

## Baseline facts

At claim time the bundled core lives in:

```text
DavisKahan/SpectralTheory/ClosedOperator/Basic.lean
DavisKahan/SpectralTheory/ClosedOperator/BoundedRealization.lean
DavisKahan/SpectralTheory/ClosedOperator/Complex.lean
DavisKahan/SpectralTheory/ClosedOperator/Complexification.lean
```

`Basic.lean` already exposes `toLinearPMap`; this is the migration seam, not the
final abstraction. Direct importers include reducing restrictions, closed
Sylvester equations, genuine-spectrum estimates, and Spectra interoperability.
Record the exact current consumer count before the first implementation commit
and after every phase.

## Live inventory and migration log

The 2026-07-28 production census found no `ClosedOperator` reference in
`ForTauCeti`: its reusable closedness, domain, extension, graph-norm, and
Sylvester APIs are already the dependency-clean
`TauCeti.LinearPMap` declarations in
`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/{Closed,Sylvester}.lean`.
The remaining non-experimental references divide as follows:

| Family | Classification | Canonical implementation | Remaining bundle boundary / deletion condition |
| --- | --- | --- | --- |
| domain, extension, graph-norm, semibound, bounded perturbation, and closed-Sylvester algebra | missing reusable result, now migrated | `TauCeti.LinearPMap` in `ForTauCeti`, including raw `addBounded` on the original domain | `ClosedOperator` declarations are compatibility facades; the new `DavisKahan/Interop/TauCeti/ClosedOperator.lean` is the explicit downstream boundary, and the pairwise family has already moved its import there |
| pairwise spectral separation and homogeneous uniqueness | Spectra-dependent downstream result | `LinearPMap.GenuinePairwiseSpectrumGap` and `linearPMapSylvester_*` in `DavisKahan/Sylvester` | `GenuinePairwiseSpectrumGap` remains only for seven source/audit consumers until their paper data records accept raw partial maps; it is reducible to the canonical predicate and its three old uniqueness theorems delegate to the raw proofs |
| one-unbounded/one-bounded equation and Neumann estimate | generic downstream result | `LinearPMap.UnboundedBoundedSylvesterEquation` embeds the bounded right block without a `ClosedOperator`; `linearPMapSylvester_mem_and_gauge_le_of_unbounded_bound_inverse` takes raw partial maps and equations, and the bounded `GenuineSpectrum` consumer now calls it directly | the historical theorem remains for source-facing callers; migrate those before deleting the bundle-shaped entry point |
| shifted-inverse predicates and interval/exterior gauge estimate | production consumer migrated | `LinearPMap.{Left,TwoSided}ShiftedInverseBound`, raw `addBounded`, raw Sylvester equations, the raw Neumann theorem, `linearPMap_norm_shift_apply_le_of_form_bounds`, both raw `linearPMap_norm_sylvester_le_of_{intervalExterior,exteriorInterval}` estimates, `linearPMap_exists_bounded_shift_extension`, and `linearPMap_mem_and_gauge_le_of_exteriorLeft_intervalRight` now own the implementation | `ShiftedInverse` and `ShiftedInverseGauge` preserve historical names only as compatibility facades; migrate their source-facing callers before contracting those bundle-shaped entry points |
| PVM, spectral restriction, cutoff, real-spectrum, and complexification bridges | Spectra/PVM boundary | none yet; depends on Spectra spectral-calculus APIs | retain downstream and list the exact Spectra import at each bridge; not a reason to retain the bundle in unrelated Sylvester or Riccati mathematics |
| reducing restrictions and Riccati transport | production consumers still needing migration | `LinearPMap.InvariantSubspace`, `ReducesSubspace` (including orthogonal-complement closure), and `reducingRestriction` now own the complete restriction core: domain/action/map, density/closedness, adjoint-domain, symmetry, and self-adjointness; raw graph rotation exposes its pullback, exact domain, unitary equivalence, and reduction transport over `UnboundedBlockDataPMap`; historical closed-operator theorems delegate to it | migrate the remaining Riccati and sine-theta consumers to raw partial-map inputs; bundled constructions must be replaced rather than wrapped permanently |
| Riccati transport pullback | generic downstream result | `LinearPMap.pullbackDomain`, `pullbackDomainToOriginal`, `pullbackLinearMap`, `pullback`, density/closedness, and `UnitaryEquivalent` own the raw construction and transport proof; `UnboundedTransport` and the historical Riccati relation delegate | migrate Riccati data records and direct consumers to raw partial-map inputs |
| Riccati block data and direct sum | generic downstream result | `UnboundedBlockDataPMap` stores partial maps with explicit density, closed-graph, and self-adjointness properties; `UnboundedBlockData.toPMap` is the compatibility conversion. `LinearPMap.directSumDomain`, coordinate maps, component action, `directSum`, density, graph closedness, `unboundedOffDiagonalCouplingPMap`, and `unboundedBlockOperatorPMapCore` (with direct domain and coordinate-action lemmas) own the raw construction. `unboundedBlockOperatorCore_toLinearPMap` states the bundled core's canonical raw view, while its remaining package carries closedness | migrate graph reduction and selected-graph records to `UnboundedBlockDataPMap`, then contract the closedness-only facade |
| Riccati graph reduction | production consumer migrated | `unboundedBlockGraph_invariantPMapData_iff_strongRiccatiPMapCore` proves the raw-data invariance equivalence over `UnboundedBlockDataPMap`; the historical theorem delegates to it | migrate selected-graph records and continue reducing bundled graph-domain helpers to documented facades |
| selected reducing graph handoff | production consumer migrated | `ContractiveReducingGraphSelectionPMap` and its existential handoff store raw `LinearPMap.ReducesSubspace` and derive `StrongSolvesRiccatiPMap`; `UnboundedSelectedGraphBridge` now takes raw block data at its ambient-angular continuation endpoint, `UnboundedPublic` exposes matching raw aggregate and complex diagonalization endpoints, and the raw graph-rotation diagonal representative carries its reduction and unitary-equivalence conclusions; closed coordinate restrictions remain an explicitly documented closed-output adapter | migrate remaining source-facing diagonalization callers to the raw record, then contract historical graph-domain helpers not needed by the closed-output adapter |
| unbounded sine-theta residual data | production consumer migration in progress | `UnboundedSinThetaDataPMap` now stores the three raw partial maps together with explicit density and closed-graph hypotheses; `UnboundedSinThetaData.toPMap` and the genuine interval/all-gap predicate views supply the canonical route for source facades. The natural complex isometric and generalized all-gap consumers, and the canonical `FiniteIntervalGeneralSinThetaProblem.{result,complementaryBlock_result}` source records, now call raw endpoints through those views; raw operator-norm and ideal-gauge endpoints (including raw Spectra resolvent-gap discharges), raw generalized/exact/isometric interval-exterior and all-gap endpoints, and the long `linearPMap_mem_and_gauge_le_of_boundedLeft_exteriorRight` Neumann proof are stated directly over `LinearPMap` domains and actions | the historical residual and Neumann entry points are source-facing compatibility wrappers. The raw interval/exterior and all-gap endpoints package only at the documented Spectra bounded-realization/resolvent boundary. `generalizedSinTheta_unbounded_{,exact_}of_genuineIntervalExteriorGap` now have **no production caller outside their own defining module**, so they are contractible once the `Sources/**` and `Real/**` records move; migrate the remaining interval/gauge callers through their raw views |
| Sylvester bounded realization transfer | production consumer migrated | `linearPMapSylvesterEquation_boundedRealization` transfers a raw Sylvester equation using explicit closed-graph and dense-domain properties; the bundled theorem delegates to it, and `ShiftedInverseGauge` calls the raw theorem directly | migrate remaining shifted-inverse callers to raw partial-map hypotheses and contract their bundle-only entry points |

The pairwise canonical form cannot move into `ForTauCeti` yet: it depends on
`Spectra.Resolvent.spectrum` and the separated-intertwiner theorem.  Its exact
blocker is therefore Spectra's spectrum/intertwiner API, not any missing
`LinearPMap` domain machinery.  The next U1 slice is the remaining closed
Sylvester estimates, followed by reducing restrictions and Riccati inputs.

## Release state (2026-07-28) — read before reclaiming

The lane is **released mid-migration, not finished**.  Everything below is
measured, not estimated; re-measure before trusting it.

**Gate U1.4, first command: met in substance.**  `grep -R "ClosedOperator"
ForTauCeti --include='*.lean'` returns 3 hits and all 3 are prose — two
provenance lines in `LinearPMap/Closed.lean` and one docstring sentence in
`LinearPMap/Sylvester.lean`.  No `ForTauCeti` declaration references the bundle.

**Gate U1.4, second command: not met.**  171 type-position uses of
`ClosedOperator` survive in production, across 18 modules outside
`DavisKahan/SpectralTheory/ClosedOperator/**` and `DavisKahan/Experimental/**`:

| module | uses | classification |
| --- | --- | --- |
| `Riccati/UnboundedCore.lean` | 32 | un-migrated |
| `SpectralTheory/ReducingSubspace/Restriction.lean` | 23 | documented facade |
| `Sylvester/ClosedSylvesterEquation.lean` | 18 | documented facade |
| `Sources/DavisKahan1970/SineTheta/CommonCore.lean` | 17 | un-migrated |
| `SinTheta/Natural/Reducing.lean` | 14 | un-migrated |
| `Riccati/UnboundedTransport.lean` | 13 | un-migrated |
| `SinTheta/Natural/Examples.lean` | 10 | un-migrated |
| `Sylvester/PairwiseSpectrumGap.lean` | 8 | un-migrated |
| `Sources/DavisKahan1970/Sylvester/HilbertSchmidtPairwise.lean` | 8 | un-migrated (complexification-blocked) |
| `Sylvester/PairwiseHomogeneousUniqueness.lean` | 6 | un-migrated |
| `Sources/DavisKahan1970/Sylvester/PaperHilbertSchmidt.lean` | 6 | un-migrated |
| `Sources/DavisKahan1970/Sylvester/HilbertSchmidtDefectFirst.lean` | 4 | un-migrated |
| `Sources/DavisKahan1970/SineTheta/{CommonDomainTheorems,CommonCoreTheorems}.lean` | 3 + 3 | un-migrated |
| `Riccati/UnboundedBasic.lean` | 3 | un-migrated |
| `Sylvester/Unbounded/{Neumann,Equation}.lean`, `ReducingSubspace/RestrictionExtras.lean` | 1 each | un-migrated |

So **41 of the 171 are already compatibility facades over raw proofs** — those
are deletions, not proofs.  The other 130 are genuine records and source-facing
data structures that still quantify over the bundle.

**Contractible right now, no new mathematics:**

- `generalizedSinTheta_unbounded_{,exact_}of_genuineIntervalExteriorGap` have no
  production caller outside `SinTheta/Unbounded/IntervalExterior.lean` itself.
- The `Restriction.lean` and `ClosedSylvesterEquation.lean` facade blocks, once
  their remaining callers move.

**Riccati sub-analysis (edward, 2026-07-28) — measured, not migrated.**  The
table above lists `Riccati/UnboundedCore` as the largest un-migrated module at
32 (re-measured: 34 occurrences).  That count overstates the work, and the
blocker is not where the count suggests:

- **8 of the declarations are pure facades**, not records:
  `closedOperatorDirectSumDomain{,Fst,Snd,FstLinearMap,SndLinearMap}`,
  `closedOperatorDirectSumLinearMap`, `unboundedBlockOperatorPMapCore`,
  `unboundedBlockOperatorCorePMap`.  Every one already *delegates* to
  `TauCeti.LinearPMap.*` through `A.toLinearPMap`; there is no mathematics in
  them to migrate, only callers to move.
- **The whole `closedOperatorDirectSum*` family has exactly 2 production
  consumer sites**, both in `Riccati/UnboundedReduction.lean`.  The other 9 are
  in `DavisKahan/Experimental/InfiniteDimensional/Riccati/**`.
- `UnboundedBlockData` itself has 4 production consumers
  (`Riccati/{UnboundedBasic,UnboundedCore,UnboundedExistence,UnboundedReduction}`),
  6 Experimental ones, and 1 in the `FinishTanTwoTheta/` scratch tree.

So the production side of this cluster is **two call sites away** from letting
the `closedOperatorDirectSum*` facade be deleted outright.  What actually blocks
the deletion is `Experimental/**`, which this lane's count *excludes* but which
still has to compile for anyone who builds it — so deleting the facade is a
decision about Experimental, not about Riccati, and it should be taken together
with a policy call on whether Experimental migrates or is allowed to keep a
documented compatibility layer.  Recording that here rather than half-migrating:
a partial sweep would leave `UnboundedReduction` on the raw API and Experimental
on the bundle, i.e. exactly the mid-development conversion boundary the phase-C
ordering note warns about.

`Riccati/UnboundedTransport.lean` (17) is in the same shape: all of it is the
`ClosedOperator.pullback` facade over `TauCeti.LinearPMap.pullback*`.

**Out of this lane's declared scope; needs its own claim.**  `Interop/Spectra/**`
(6 modules, ~130 `ClosedOperator` occurrences, none in type position — they sit
at the PVM/Borel/real-spectrum/cutoff boundary that "Explicitly excluded" names)
and `OperatorIdeal/ComplexificationApproximation.lean`.
`Interop/TauCeti/ClosedOperator.lean` is the adapter and is deleted last by
construction.

**Ordering constraint inherited from the ideal-family lane.** §13.2 phase C
(restating the ~25 ideal-parameterized sin-Θ theorems over
`TauCeti.SymmetricOperatorIdealFamily`) and phase D (deleting
`RectangularSymmetricIdealFamily` and its adapter) were both deferred to
whoever holds `DavisKahan/Sylvester/**` — that is, to this lane.  With U1
released they are unblocked, and phase C should be taken **root-outward from
`Sylvester/Bounded.lean`, as one sweep**, not leaf-inward: migrated piecemeal it
leaves an `ENNReal.toReal` conversion boundary in the middle of the sin-Θ
development.  See the `jon (namek)` sin-Θ row in `dev/LANES.md`.

## Phase U1.0: declaration inventory

Before moving proofs, classify every public declaration from the bundled core:

1. exact Mathlib/Tau Ceti duplicate — delete/reuse;
2. missing reusable `LinearPMap` declaration — move to `ForTauCeti`;
3. temporary compatibility theorem — place in the adapter;
4. Davis--Kahan-specific theorem — keep downstream over canonical inputs;
5. Spectra-dependent theorem — isolate behind a narrow downstream bridge.

The inventory must include at least:

- application and coercion lemmas;
- domain equality and extension;
- `MapsDomainTo`;
- bounded extensions;
- bounded full-domain embedding;
- symmetry and self-adjointness;
- graph norm and completeness facts;
- relative boundedness;
- domain restriction and bounded perturbation;
- bounded realization and spectral-bound consumers.

Do not begin by renaming all declarations. First decide which declarations
survive.

## Phase U1.1: canonical dependency-clean core

Create final-namespace declarations in a module tree such as:

```text
ForTauCeti/Analysis/OperatorTheory/LinearPMap/Basic.lean
ForTauCeti/Analysis/OperatorTheory/LinearPMap/Domain.lean
ForTauCeti/Analysis/OperatorTheory/LinearPMap/BoundedExtension.lean
ForTauCeti/Analysis/OperatorTheory/LinearPMap/GraphNorm.lean
ForTauCeti/Analysis/OperatorTheory/LinearPMap/Perturbation.lean
```

The exact split follows dependency closure and Tau Ceti's file-size/module-style
rules. These files may import only Mathlib, Tau Ceti, and `ForTauCeti`.

Rules:

- inspect pinned Mathlib before defining any predicate;
- reuse `LinearPMap.domain`, application, graph, adjoint, and full-domain
  constructions directly;
- use predicates or propositions rather than records when no data is carried;
- keep source and target types independent unless self-adjointness requires a
  common Hilbert space;
- keep scalar assumptions at the weakest level actually used;
- state characteristic lemmas so downstream code need not unfold definitions.

The first compilable slice should cover `SameDomain`, `Extends`, `MapsDomainTo`,
and bounded-map full-domain embedding because these unblock most mechanical
consumer migration without Spectra.

## Phase U1.2: compatibility adapter

Add:

```text
DavisKahan/Interop/TauCeti/ClosedOperator.lean
```

The historical `ClosedOperator` API may temporarily remain available through
this file, but:

- its canonical mathematical content must be delegated to `LinearPMap`;
- every compatibility declaration must be documented as temporary;
- no new generic theorem may be proved only for the adapter;
- `ForTauCeti` may not import the adapter;
- the adapter's direct consumer count must decrease over time.

Do not duplicate proofs solely to keep both APIs looking equally rich. Prove the
canonical theorem once and derive the adapter theorem.

## Phase U1.3: consumer migration order

Migrate in this order:

1. local closed-operator utility consumers;
2. reducing subspace and restriction machinery;
3. closed Sylvester equation data and algebra;
4. unbounded Sylvester estimates and graph/Riccati inputs;
5. paper-facing unbounded perturbation endpoints;
6. Spectra interoperability modules that can consume a raw `LinearPMap` without
   porting the spectral calculus itself.

For each module:

- change fundamental inputs to `LinearPMap` plus explicit properties;
- preserve theorem conclusions and proof strength;
- retain an old-signature corollary only when it serves a real source-facing
  compatibility purpose;
- build the focused target immediately;
- record newly exposed missing lemmas in the canonical layer, not as local
  one-off workarounds.

## Phase U1.4: deletion and proof of completion

The migration is complete only when searches demonstrate:

```bash
grep -R "ClosedOperator" ForTauCeti --include='*.lean'
grep -R "DavisKahan.SpectralTheory.ClosedOperator" DavisKahan --include='*.lean'
```

The first command must be empty. Results from the second must be confined to the
explicit adapter, source compatibility wrappers, and documented Spectra bridges.
No generic production theorem may fundamentally quantify over the bundle.

Delete obsolete bundle modules when their final consumers disappear. Do not keep
an alias indefinitely merely because deletion causes a larger diff.

## Build and audit gates

After every implementation commit:

```bash
scripts/lake_build_report.py --fail-fast <focused-target>
python3 scripts/check_dependency_layers.py
git diff --check
```

At phase boundaries:

```bash
scripts/lake_build_report.py --fail-fast ForTauCeti
scripts/lake_build_report.py --fail-fast DavisKahan.All
lake build
python3 scripts/check_davis_kahan_1970_source_census.py
```

Run `lake build Challenge` and `scripts/check_declaration_name_drift.py` whenever
public declaration names change. Never claim compile success without Lean output.

## Commit discipline

Recommended sequence:

1. `ARCH inventory ClosedOperator to LinearPMap migration`
2. `API add canonical LinearPMap domain and extension layer`
3. `ARCH add temporary ClosedOperator compatibility adapter`
4. focused consumer-migration commits by mathematical cluster;
5. `REFACTOR remove ClosedOperator from generic production`.

Do not combine new perturbation theorems with this lane. The value of U1 is that
existing mathematics becomes natively composable with Tau Ceti.

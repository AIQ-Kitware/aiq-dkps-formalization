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
| reducing restrictions and Riccati transport | production consumers migrated | `LinearPMap.InvariantSubspace`, `ReducesSubspace` (including orthogonal-complement closure), and `reducingRestriction` now own the complete restriction core: domain/action/map, density/closedness, adjoint-domain, symmetry, and self-adjointness; raw graph rotation exposes its pullback, exact domain, unitary equivalence, and reduction transport over `UnboundedBlockData`; historical closed-operator theorems delegate to it | the Riccati half is done — see the Riccati row below; the remaining sine-theta consumers are the open half |
| Riccati transport pullback | **complete** | `LinearPMap.pullbackDomain`, `pullbackDomainToOriginal`, `pullbackLinearMap`, `pullback`, density/closedness, and `UnitaryEquivalent` own the construction and the transport proof outright | `DavisKahan/Riccati/UnboundedTransport.lean` was **deleted** — it was 120 lines of facade with no production consumer at all |
| Riccati block data and direct sum | **complete** | `UnboundedBlockData` stores partial maps with explicit density, closed-graph and self-adjointness properties, plus `isSymmetric0`/`isSymmetric1` for the estimates that consume symmetry rather than self-adjointness.  `LinearPMap.directSumDomain`, coordinate maps, component action, `directSum`, density and graph closedness own the direct sum; `unboundedOffDiagonalCoupling` and `unboundedBlockOperatorCore` own the block core | the `closedOperatorDirectSum*` facade family and the bundled core are **deleted**; `UnboundedCore.lean` went 279 → 100 lines |
| Riccati graph reduction | **complete** | `unboundedBlockGraph_invariant_iff_strongRiccatiCore` proves the invariance equivalence over the canonical record; there is no second spelling left to delegate to it | nothing outstanding |
| selected reducing graph handoff | **complete** | `ContractiveReducingGraphSelection` stores raw `LinearPMap.ReducesSubspace` and derives `StrongSolvesRiccati`; `UnboundedSelectedGraphBridge`, `UnboundedPublic` and `Unbounded` expose only raw endpoints, and the coordinate restrictions are `LinearPMap`s with density and closedness as separate theorems | nothing outstanding — the closed-output adapter that used to be documented here no longer exists |
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

**Gate U1.4, second command: not met — and the figure it was stated with is not
reproducible.**  The previous revision of this section said "171 type-position
uses across 18 modules" and gave a per-module table, but **never stated the
command that produced either number**, so nobody could check the gate they were
being held to.  Both are re-stated here with their measurement.

Raw occurrence count, which anyone can reproduce:

```sh
grep -rc ClosedOperator --include='*.lean' DavisKahan/ \
  | grep -v 'DavisKahan/SpectralTheory/ClosedOperator/' \
  | grep -v 'DavisKahan/Experimental/' | grep -v ':0$'
```

**744 occurrences across 77 modules** (2026-07-28, after the Riccati
sweep).  This counts every mention, including docstrings and provenance prose,
so it is an upper bound rather than the type-position count; it is recorded
because it is checkable, whereas "171" was not.  Modules at 10 or more:

| module (under `DavisKahan/`) | occurrences |
| --- | --- |
| `Interop/Spectra/RealSpectralRestriction.lean` | 104 |
| `SinTheta/Natural/Bounded.lean` | 52 |
| `Sources/DavisKahan1970/SineTheta/Symmetric.lean` | 42 |
| `Sylvester/ClosedSylvesterEquation.lean` | 37 |
| `SpectralTheory/ReducingSubspace/Restriction.lean` | 27 |
| `SinTheta/Natural/Reducing.lean` | 27 |
| `SinTheta/Natural/Examples.lean` | 25 |
| `Sources/DavisKahan1970/SineTheta/CommonCore.lean` | 22 |
| `Sylvester/Unbounded/OrderedCutoff.lean` | 19 |
| `Sources/DavisKahan1970/SineTheta/CommonDomain.lean` | 19 |
| `Sources/DavisKahan1970/Sylvester/HilbertSchmidtPairwise.lean` | 16 |
| `SinTheta/Unbounded/Core.lean` | 16 |
| `Interop/Spectra/SpectralRestrictionOperator.lean` | 15 |
| `Sylvester/Unbounded/OrderedFromCutoffs.lean` | 13 |
| `Interop/Spectra/SpectralRestriction.lean` | 13 |
| `Interop/Spectra/BoundedPerturbationSinTheta.lean` | 13 |
| `SinTheta/Natural/GapConvenience.lean` | 12 |
| `Interop/Spectra/UnitaryConjugation.lean` | 12 |
| `Sylvester/ShiftedInverse.lean` | 10 |
| `Sylvester/PairwiseSpectrumGap.lean` | 10 |
| `SinTheta/Specializations.lean` | 10 |
| `Interop/Spectra/BoundedTruncation.lean` | 10 |

**The Riccati cluster is closed and is no longer in this table.**  The previous
revision listed `Riccati/UnboundedCore` (32), `Riccati/UnboundedTransport` (13)
and `Riccati/UnboundedBasic` (3) as the largest un-migrated block.  All three are
now **0**: `UnboundedTransport.lean` no longer exists, and
`grep -R ClosedOperator DavisKahan/Riccati` returns nothing — in the declarations
*and* in the import graph, since `UnboundedBasic` now imports
`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean` directly rather
than reaching the bundle through `SpectralTheory/ReducingSubspace/Restriction`.

Two entries above are still **documented facades** rather than genuine records —
`SpectralTheory/ReducingSubspace/Restriction.lean` and
`Sylvester/ClosedSylvesterEquation.lean` — i.e. deletions once their callers
move, not proofs.  `Interop/Spectra/**` (led by `RealSpectralRestriction.lean`)
sits at the PVM/Borel/real-spectrum boundary that "Explicitly excluded" names and
is not this lane's to migrate.

**Contractible right now, no new mathematics:**

- `generalizedSinTheta_unbounded_exact_of_genuineIntervalExteriorGap` —
  **done 2026-07-28 (edward, aiq-gpu): deleted.**  It was not merely
  caller-free outside its module, it was **dead in the whole repository**,
  including inside its own module: the raw
  `linearPMap_generalizedSinTheta_unbounded_exact_of_genuineIntervalExteriorGap`
  is proved from the *raw* non-exact theorem, never from the bundled one.
- The `Restriction.lean` and `ClosedSylvesterEquation.lean` facade blocks, once
  their remaining callers move.

**The gap predicates are now canonical — and they were the keystone (edward,
aiq-gpu, 2026-07-28).**  `UnboundedSylvesterGap` and
`UnboundedIntervalExteriorGap` (`DavisKahan/Sylvester/Gap.lean`) are stated over
`LinearPMap`; the bundled spellings survive as reducible `abbrev`s at
`A.toLinearPMap`, so **none of the 27 consumer modules changed**.

Why this one mattered more than its size (67 lines) suggests: it is what
*blocked* the rest of the unbounded sin-Θ cluster.  `SinTheta/Natural/Reducing.lean`
— U1's second-largest un-migrated record at 14 type-position uses — carries a
`spectral_gap : UnboundedSylvesterGap A₀ Λ₁ gap` field, so retyping its two
problem structures over `LinearPMap` without first retyping the gap would have
forced `.toClosed` round-trips *at the gap field*, reintroducing the bundle in
the middle of the record that was supposed to leave it.  The same field blocks
`Sources/**/SineTheta/{CommonCore,CommonDomain,Symmetric,Theorem61Universal}`
(U1's 17-use entry).  **Those five records can now each migrate independently**;
that is the point of this change.

The restatement cost no mathematics.  Every component was *already* a reducible
facade over the canonical layer — `ClosedOperator.realSpectrum`
(`ClosedOperator/Basic.lean:469`) and `SemiboundedBelow`/`SemiboundedAbove`
(`ClosedSylvesterEquation.lean:42,47`) — so the raw and bundled predicates are
definitionally equal and `cases`/`rcases` see the canonical constructors
directly.

**Two gotchas for whoever repeats this shape.**

1. **`cases` survives a reducible `abbrev`; `rw` does not.**  Demoting the
   bundled predicate to an `abbrev` left every `cases hgap with | intervalExterior
   ... =>` working untouched, and the three constructor `alias`es kept the
   `UnboundedSylvesterGap.«ctor»` references resolving.  But four `rw`s in
   `SpectralTheory/ClosedOperator/Complexification.lean` broke: `rw` matches on
   the head symbol, and the goal's head became `LinearPMap.realSpectrum …
   toLinearPMap` where the rewrite lemma still says `ClosedOperator.realSpectrum`.
   Reducibility does not help — keyed matching has already failed by then.  Fix
   is to bind the hypothesis at the facade type first (`have hlamA : lam ∈
   (complexify A).realSpectrum := hlam`, which typechecks by defeq), making the
   conversion boundary explicit at the one place it matters.
2. **`lake build Challenge` fails spuriously on a cold cache.**  It reported 47
   errors, 23 of them `failed to open file … .ir: Too many open files` — file-
   descriptor exhaustion from cold-cache parallelism, not proof breakage, and
   the paths in the message are stale absolute paths from another machine.  The
   soft `ulimit -n` is already 1048576, so raising it is not the fix; simply
   **re-running with the warm cache passes** (8827 jobs, 0 errors).  Do not read
   a first-run `Challenge` failure as a regression without checking whether every
   error is `Too many open files`.

**Scan: bundled twins superseded by a `linearPMap_` version (edward, aiq-gpu,
2026-07-28).**  Both deletions this lane made were the same shape — a bundled
declaration whose `linearPMap_` twin had taken over every caller — so it is worth
running as a check rather than noticing by accident.  Pair up `X` with
`linearPMap_X` across `DavisKahan/**` (excluding `Experimental/**`), then count
references to the bundled `X`.  There are **12 such pairs**; two came back with
zero references and **one of those was wrong**.

- `exists_bounded_shift_extension` (`Sylvester/ShiftedInverseGauge.lean`) — truly
  dead, **deleted**.  Every caller, including the rest of its own module, uses
  `linearPMap_exists_bounded_shift_extension`.
- `mem_and_gauge_le_of_exteriorLeft_intervalRight` — **false positive, do not
  delete.**  It is called from `Sources/DavisKahan1970/FullPartIII.lean` through
  its *fully qualified* name
  `DavisKahan.Experimental.ExactSinTheta.mem_and_gauge_le_of_exteriorLeft_intervalRight`.

**The blind spot, because it is easy to re-introduce.**  A reference scan that
ignores matches preceded by `.` — a natural way to avoid unrelated dot-notation —
also hides every *qualified* reference, and qualified references are exactly how
`Sources/**` reaches into `Experimental` namespaces.  Deleting on that signal
would have broken a paper-facing module.  Always grep the bare name including
dotted occurrences before believing a zero.

**Correction — `generalizedSinTheta_unbounded_of_genuineIntervalExteriorGap` is
NOT contractible, and was previously listed here as if it were.**  "No
production caller outside its own module" is true of it and is also not the
relevant test: the raw endpoint
`linearPMap_generalizedSinTheta_unbounded_of_genuineIntervalExteriorGap` is
proved by `apply`ing the bundled theorem at `D.toClosed`, so the module depends
on it internally.  That delegation exists because the Spectra Sylvester lemmas
underneath it —
`SpectraBridge.unbounded_sylvester_mem_and_gauge_le_of_spectra_intervalLeft_exteriorRight`
and its `exteriorLeft_intervalRight` twin — still take bundled `ClosedOperator`
arguments.  Contracting the endpoint therefore requires raw `SpectraBridge`
lemmas, i.e. work inside `Interop/Spectra/**`, which this lane **explicitly
excludes**.  It is blocked on a boundary the lane does not own, not merely
un-done, and should not be picked up as a quick win.

**Riccati cluster (edward, aiq-gpu, 2026-07-28) — MIGRATED AND DELETED.**  The
table above listed `Riccati/UnboundedCore` (32), `Riccati/UnboundedTransport`
(13) and `Riccati/UnboundedBasic` (3) as un-migrated.  All three are now at
**zero**: `grep -R ClosedOperator DavisKahan/Riccati` returns nothing.

What the earlier measurement got wrong, and it is worth recording because the
same shape recurs elsewhere in this lane: the release note concluded that the
`closedOperatorDirectSum*` facade was "two production call sites from
deletion", with `Experimental/**` as the only blocker and therefore a *policy*
question.  Reading the tree showed the blocker was structural instead.  The
bundled core is consumed by a **complete parallel bundled stack five Experimental
modules deep** — `UnboundedRotationTransport` → `UnboundedReductionTransport` →
`UnboundedDiagonalRestrictions` → `UnboundedPublic` → `Unbounded` — ending at the
public endpoint `complex_unbounded_blockDiagonalization`, plus
`FinishTanTwoTheta/DavisKahan/Unbounded.lean`.  Every level carried both a raw
and a bundled spelling of the same theorem.  Deleting the facade bottom-up would
have stranded exactly the mid-development conversion boundary the phase-C
ordering note warns about, which is why the two earlier attempts stopped.

**The sweep therefore ran top-down** — `FinishTanTwoTheta` first, then
`Unbounded`, `UnboundedPublic`, the diagonal/coordinate restrictions, the two
transport modules, and finally the production core — and the facade deletions
fell out at the end with nothing left pointing at them.

Three things worth knowing for the next module that has this shape:

- **The `ClosedOperator` bundle was hiding hypotheses that the mathematics does
  not use.**  `UnboundedCoordinateRestrictions` (274 lines) took a
  `ClosedOperator` throughout, i.e. assumed a dense domain and a closed graph,
  but every one of its declarations uses only `D.domain` and `D.toFun`.  Retyped
  over `LinearPMap` it needs *neither* hypothesis, and the two places that
  genuinely need them — the coordinate restrictions' own density and closed
  graph — now take them as named arguments and say so.  Weakening the
  hypotheses was not an extra goal of the migration; it was a consequence of it.
- **Three declarations were sitting in a `namespace ClosedOperator` and had
  nothing to do with closed operators.**
  `intertwines_orthogonal_projection_of_intertwines_projection`,
  `map_mem_of_intertwines_projection` and
  `symm_map_mem_of_intertwines_projection` are pure orthogonal-projection facts.
  They survive the deletion of the namespace and are now visible at
  `DavisKahanExt` level, where they read as what they are.  They are also
  plausible `ForTauCeti` material for whoever takes a projection lane.
- **Two coordinate restrictions lost an argument.**
  `unboundedBlockDiagonalRestriction0/1` used to take the reduction proof
  `hred`, because the bundled constructor needed it to fill `dense_domain` and
  `closed_graph`.  The `LinearPMap` version is definable without it, so `hred`
  moved to the theorems that actually use it and the two restrictions are now
  functions of `H` and `X` alone.

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

# U1 execution contract: migrate unbounded operators to `LinearPMap`

Status: **ACTIVE / CLAIMED by jon (toothbrush), 2026-07-28**.

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
| one-unbounded/one-bounded Neumann estimate | generic downstream result | `linearPMapSylvester_mem_and_gauge_le_of_unbounded_bound_inverse` takes raw `LinearPMap` and `LinearPMap.SylvesterEquation`; the bounded `GenuineSpectrum` consumer now calls it directly | the historical theorem remains for `ShiftedInverseGauge` and source-facing callers; migrate those before deleting the bundle-shaped entry point |
| PVM, spectral restriction, cutoff, real-spectrum, and complexification bridges | Spectra/PVM boundary | none yet; depends on Spectra spectral-calculus APIs | retain downstream and list the exact Spectra import at each bridge; not a reason to retain the bundle in unrelated Sylvester or Riccati mathematics |
| reducing restrictions and Riccati transport | production consumers still needing migration | `TauCeti.LinearPMap` closed/domain API | convert after the closed-Sylvester family; their current bundled constructions must be replaced rather than wrapped permanently |

The pairwise canonical form cannot move into `ForTauCeti` yet: it depends on
`Spectra.Resolvent.spectrum` and the separated-intertwiner theorem.  Its exact
blocker is therefore Spectra's spectrum/intertwiner API, not any missing
`LinearPMap` domain machinery.  The next U1 slice is the remaining closed
Sylvester estimates, followed by reducing restrictions and Riccati inputs.

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

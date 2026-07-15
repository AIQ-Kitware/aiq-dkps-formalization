# Spectra integration survey and collaboration plan

Date: 2026-07-14

Audited upstream:

- repository: `https://github.com/adambornemann-glitch/Spectra`
- audited commit: `8dbaaf6728d1342ae16acf79fd7eef7c59b37e63`
- license: Apache-2.0 in the inspected source modules and repository license
- upstream toolchain at the audited commit: `leanprover/lean4:v4.31.0-rc1`
- DKPS toolchain during this audit: `leanprover/lean4:v4.32.0-rc1`

This document supersedes any earlier description of selected Mathlib declarations
as vendored tools.  Mathlib is already a direct dependency of this repository;
its Banach, closed-range, `LinearPMap`, anti-Lipschitz, and near-identity inverse
APIs must be imported directly.  They are upstream capabilities, not third-party
vendors.

## Decision

During active collaboration, track Spectra as a Git submodule at
`external/Spectra`.  Do not copy selected Spectra files into `vendor/lean/` and
do not import the root `Spectra` module.

The submodule serves two purposes:

1. a reproducible checkout for narrow DKPS import experiments; and
2. a normal Git worktree from which general operator-theory improvements can be
   committed, pushed to a fork, and proposed upstream.

Once the required APIs have merged upstream and the joint development phase has
stabilized, replace the submodule path dependency with a normal Lake Git
dependency pinned to an upstream commit.

## Why a submodule instead of copied files

Copying creates a permanent maintenance fork at exactly the layer we do not want
to own.  Spectra is actively developing the spectral theorem, PVMs, resolvents,
unbounded self-adjoint operators, polar decomposition, trace class, and
Hilbert--Schmidt theory.  Manual snapshots would make every upstream correction
a local port and would obscure which changes should become upstream PRs.

A submodule preserves:

- exact source history and license;
- an ordinary branch and PR workflow;
- a reproducible parent-repository gitlink;
- clean separation between upstream operator theory and DKPS-specific theorems;
- the option to switch later to a normal pinned Lake dependency.

The committed `.gitmodules` URL should remain the public upstream URL so every
clone can initialize it.  A local remote named `fork` is used for contribution
branches.

## Audited Spectra capability map

### Strong candidates for direct use

The following areas were inspected and are materially relevant.

#### Projection-valued measures

`Spectra/ProjValMeasure/Basic.lean` defines a real-line PVM with projection
algebra and diagonal scalar measures.  It proves idempotence, self-adjointness,
finite additivity, norm bounds, and extensionality.  The core imports Mathlib
rather than the full Spectra root.

`Spectra/ProjValMeasure/Map.lean` provides measurable pushforward.

#### Self-adjoint and unbounded operators

`Spectra/Operator/SelfAdjoint.lean` packages a possibly unbounded self-adjoint
`LinearPMap` and derives density and symmetry.

`Spectra/Operator/Bounded.lean` connects this representation to bounded
self-adjoint continuous linear maps through Hellinger--Toeplitz and also proves
closed-graph infrastructure for `LinearPMap`.

#### Spectral theorem and spectral projections

The spectral theorem stack constructs a PVM for a self-adjoint operator and
connects it to the resolvent.  The inspected files include:

- `Spectra/SpectralTheory/ResolventForm.lean`
- `Spectra/SpectralTheory/Measure/PVM.lean`
- `Spectra/SpectralTheory/Algebra.lean`
- `Spectra/SpectralTheory/Measure/GeneratorLink.lean`
- `Spectra/SpectralTheory/Spectrum.lean`
- `Spectra/SpectralTheory/Eigenspace.lean`

The projection algebra includes complements, intersections, commutation,
disjoint unions, scalar-measure identities, finite-interval approximation,
domain localization, energy bounds, and spectral-gap/resolvent bridges.

#### Unbounded functional calculus

The calculus constructs `LinearPMap` operators on their natural square-integrable
domains through bounded truncations.  Later modules provide mixed
bounded/unbounded product laws and self-adjointness of real-symbol calculi once
density is available.

#### Bounded polar decomposition

`Spectra/QuantumMechanics/Channels/PolarDecomp.lean` constructs a genuine
infinite-dimensional bounded polar decomposition.  The associated
`TraceClass/PartialIsometry.lean` proves contraction and initial-space
identities.

#### Trace class and Hilbert--Schmidt

The `Spectra/QuantumMechanics/Channels/TraceClass/` tree contains predicates,
norms, ideal closure, trace-class completeness, Hilbert--Schmidt basis
independence, and sharp Schatten-one/two product bounds.

### Adjacent spectral-theorem projects considered

The 2026-07-15 related-work follow-up compared the selected Spectra path with two
additional Apache-2.0 projects. Neither comparison changes the integration
decision.

#### `abenenson/compact-spectral`

Audited commit: `72cd62dbdd4c397d26fc0c5777d60fea2211e938`.

This project gives an independent, proof-complete compact self-adjoint spectral
theorem over `RCLike`. Its reusable seams include weak compactness, Rayleigh
extremum attainment, finite-dimensional large-eigenvalue spaces, cutoff
projectors, and finite-rank approximation. It does not provide a PVM spectral
calculus, the all-index compact Courant--Fischer theorem, or Davis--Kahan.

For DKPS it is a useful compact-operator proof quarry, not the preferred
operator-theory dependency. Its main endpoint overlaps current Mathlib and the
compact eigenbasis already assembled in Spectra, while Spectra additionally
provides the PVM and unbounded self-adjoint infrastructure required by the
long-term DK roadmap.

#### `oliver-butterley/SpectralThm`

Audited commit: `4f15a87cd8eb1c27730373a9c64c1b8ee7d51a7a`.

This project targets the bounded normal-operator spectral theorem through the
continuous functional calculus, complex Riesz--Markov--Kakutani measures, and a
resolution of the identity. That architecture is directly relevant to the
experimental bounded Hilbert-space DK branch. However, its principal measure
bounds, resolution axioms, and reconstruction theorem still contain explicit
`sorry`s at the audited commit.

It should be monitored as an independent design comparison, especially for the
bounded-normal and RMK route, but it is not currently a production dependency.
Spectra remains the selected collaboration target because its PVM and
self-adjoint spectral theorem are already proved and extend to the unbounded
operator setting.

### Important missing APIs

Spectra does not currently replace the Davis--Kahan development.

No inspected module supplies:

- the acute-projection graph-subspace theorem;
- operator angles between arbitrary closed subspaces;
- Sylvester separation estimates in Davis--Kahan form;
- the sine, tangent, double-angle, or direct-rotation theorem families;
- Section 8 spectral-subspace continuation and branch selection;
- a Ky Fan hierarchy, approximation-number abstraction, or general symmetric
  unitary-invariant norm ideal.

The immediate graph-subspace theorem remains DKPS work, using Mathlib directly.

## Ownership boundary

### Belongs in Spectra or eventually Mathlib

- range subspaces of PVM projections;
- closedness and orthogonal-projection instances for those ranges;
- identification of a PVM value with the star projection onto its range;
- complement, monotonicity, intersection, and disjointness laws for PVM ranges;
- domain preservation and reducing-subspace lemmas for spectral projections;
- general graph-subspace geometry not mentioning Davis--Kahan;
- invertible/surjective refinements of bounded polar decomposition;
- reusable operator-ideal infrastructure.

### Belongs in DKPS

- source-faithful Davis--Kahan theorem statements;
- coercive and Sylvester perturbation estimates;
- operator-angle and angular-operator interfaces specialized to the paper;
- the four theorem families and their equality/sharpness content;
- Section 8 perturbation continuation and canonical branch selection;
- bridges to the four DKPS papers;
- real-scalar and weaker-foundation finite alternatives.

A thin `DavisKahan` bridge may translate Spectra declarations into local
paper-facing names, but should not duplicate general operator theory.

## Integration stages

### Stage 0: collaboration checkout

Run:

```bash
scripts/bootstrap_spectra_submodule.sh --create-fork
```

This records the public upstream as the submodule URL, checks out the audited
commit, creates a named compatibility branch, and configures a `fork` remote.
It does not enable the Lake dependency by default.

### Stage 1: toolchain and Mathlib compatibility

Port the Spectra checkout from Lean 4.31 to the root Lean 4.32 pin on the
submodule branch.  Keep this branch mechanical: toolchain, Mathlib alignment,
and compatibility fixes only.

Do not hide a dependency conflict by changing DKPS back to an older Mathlib.
The target is a Spectra branch that builds against the same root dependency
resolution.

### Stage 2: narrow import spike

After pins agree:

```bash
python3 scripts/enable_spectra_lake_dependency.py
scripts/spectra_import_smoke.sh
```

The initial smoke imports are deliberately narrow:

- `Spectra.ProjValMeasure.Basic`
- `Spectra.Operator.Bounded`
- `Spectra.QuantumMechanics.Channels.PolarDecomp`

Do not import `Spectra` at the root.  Its dependency cone includes many unrelated
physics and analysis developments.

### Stage 3: first upstream contribution

The best first PR is a small PVM range-subspace layer, for example:

```text
Spectra/ProjValMeasure/Subspace.lean
```

Candidate declarations:

```text
ProjValMeasure.rangeSubspace
ProjValMeasure.rangeSubspace_isClosed
ProjValMeasure.rangeSubspace_hasOrthogonalProjection
ProjValMeasure.proj_eq_starProjection_rangeSubspace
ProjValMeasure.rangeSubspace_compl
ProjValMeasure.rangeSubspace_mono
ProjValMeasure.rangeSubspace_inter
ProjValMeasure.rangeSubspace_orthogonal_of_disjoint
```

This should depend only on the PVM core and Mathlib projection modules.  It is
useful to Spectra independently of Davis--Kahan.

### Stage 4: spectral reducing subspaces

A later focused PR should connect the self-adjoint spectral PVM to closed
reducing subspaces, with explicit domain preservation for unbounded operators.
Bounded convenience wrappers should accept a self-adjoint continuous linear map
and hide the `LinearPMap` conversion.

### Stage 5: DKPS bridge

Only after the upstream API is stable should DKPS add a narrow bridge module.
The bridge should expose the exact subspace and form-bound interfaces required by
the paper, while preserving the independent `RCLike` bounded/coercive and
finite-dimensional branches.

### Stage 6: retire the submodule

When upstream support is merged and simultaneous editing is no longer routine,
replace the path dependency with a Git dependency pinned to an upstream commit
and remove the submodule from the parent repository.

## Contribution workflow

The bootstrap script leaves Spectra on a named branch rather than detached
`HEAD`.  Work and commit inside the submodule first:

```bash
cd external/Spectra
git status
git switch dkps-lean-4.32
# edit and test
git add .
git commit -m "Add PVM range subspace API"
git push -u fork dkps-lean-4.32
```

Then return to the parent and record the tested gitlink:

```bash
cd ../..
git add .gitmodules external/Spectra
git commit -m "Pin Spectra collaboration checkout"
```

A theorem that depends on Spectra must report the exact parent gitlink and must
be rebuilt after either the DKPS tree or submodule pointer changes.

## Trust and quality notes

Spectra enables strict Lean options and has compile-time `assert_no_sorry`
checks for advertised results.  This is meaningful evidence, but it is not a
substitute for building the exact imported modules at the pinned commit and
running a local axiom audit on the declarations DKPS uses.

One inspected file, `AxiomCheck.lean`, had an MIT header while the surrounding
repository and source modules used Apache-2.0.  This appears to be a header
inconsistency worth reporting upstream; the repository license remains the
authoritative license for dependency use.

## Rejected approaches

- Do not vendor snapshots of the existing Mathlib dependency.
- Do not copy a hand-selected Spectra subtree into DKPS as the production path.
- Do not add the root `Spectra` import.
- Do not enable a path dependency while the toolchain mismatch is unresolved
  and then treat the resulting build failures as DKPS proof failures.
- Do not write DKPS-specific theorem names or paper structure into general
  Spectra modules.

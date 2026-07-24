# Tau Ceti extraction cluster classification (Tier 1–3)

Companion to `dev/tauceti/mathematical-declaration-inventory.md` and the
machine-readable `dev/tauceti/extraction-manifest.json`. For each reusable
cluster this records ownership, the intended final Tau Ceti path, the dependency
closure, a provenance class, a status, current Davis–Kahan consumers, and the
ordered upstream PR position. The aim is that the *next* PR begins with
implementation, not rediscovery.

Status vocabulary: `ready` (dependency-clean, portable now) · `staged`
(already lifted into `ForTauCeti`) · `needs-api-refactor` · `blocked-on-tauceti`
· `blocked-on-mathlib` · `blocked-on-spectra-removal` · `davis-kahan-specific`.

Ownership classes: `mathlib` · `tauceti` · `davis-kahan` · `spectra-bridge` ·
`source-wrapper` · `experimental`.

---

## PR 1 — approximation numbers  (STAGED, this campaign)

| Cluster | Ownership | Final Tau Ceti path | Status |
| --- | --- | --- | --- |
| rectangular approximation-number foundation | `tauceti` | `TauCeti/Analysis/OperatorIdeal/ApproximationNumber/{Basic,Adjoint,FiniteDimensional,MinMax,OperatorModulus}` + `TauCeti/Analysis/InnerProductSpace/CourantFischer` | `staged` |

* **Closure**: Mathlib only. `Basic`→Mathlib; `Adjoint`→Basic; `CourantFischer`→Mathlib;
  `FiniteDimensional`,`MinMax`→Basic+CourantFischer; `OperatorModulus`(clean part)→Mathlib.
* **Provenance**: copied from `ForMathlib/Analysis/Normed/Operator/ApproximationNumber*`
  and `ForMathlib/Analysis/InnerProductSpace/CourantFischer` (Kitware, Apache 2.0;
  adapted from Mathlib PR #32126); `OperatorModulus` clean part from
  `DavisKahan/OperatorIdeal/ApproximationNumbers/OperatorModulus.lean`.
* **Consumers**: `DavisKahan.OperatorIdeal.ApproximationNumbers.Core`,
  `…/ScalarGeneric`, `…/Real`, `…/BlockSum`.
* **Deferred (blocked-on-spectra-removal)**: approximation-number *invariance under
  the source modulus* (`sameApproximationSingularValues_rectangularOperatorModulus`)
  routes through `SpectraBridge.lt_approximationNumber_iff_exists_finiteDimensional_lowerBound`.
  It ships in a later PR once a Mathlib-only infinite-dimensional min–max is proved
  (the `≥` half already exists Spectra-free in `MinMax.lean`; only the existence of the
  witnessing subspace — the `≤` half — needs Spectra today).

---

## Tier 1 — broadly reusable functional analysis

### 1a. Rectangular symmetric ideal families
* **Home**: `DavisKahan/OperatorIdeal/UnitarilyInvariant/RectangularFamily.lean`.
* **Ownership**: `tauceti`. **Final**: `TauCeti/Analysis/OperatorIdeal/SymmetricIdeal/…`.
* **Closure**: approximation-number foundation (PR 1) + Mathlib. No Spectra bridge.
* **Status**: `blocked-on-tauceti` (needs PR 1 merged) → then `ready`.
* **PR order**: **PR 2** (with Hilbert–Schmidt equivalences).
* **Consumers**: `…/ApproximationNumbers/ScalarGeneric`, sine-theta UI-norm layer.

### 1b. Orthogonal block sums / column reconstruction
* **Home**: `DavisKahan/OperatorIdeal/ApproximationNumbers/BlockSum.lean`,
  `DavisKahan/Alternative/OperatorIdeal/HilbertSchmidt/ColumnExpansion.lean`.
* **Ownership**: `tauceti`. **Final**: `TauCeti/Analysis/OperatorIdeal/ApproximationNumber/BlockSum.lean`.
* **Status**: `needs-api-refactor` + partially `blocked-on-spectra-removal`.
  `BlockSum.lean` imports `DavisKahan.Interop.Spectra.ApproximationNumberMinMax`
  and `DavisKahan.Sources…SingularValueTransport` (a source facade — a backwards
  dependency). Exact orthogonal block-sum merge formulas whose current proof
  depends on Spectra are excluded from an early PR (campaign §9.2).
* **Blocker (precise)**: `SpectraBridge.lt_approximationNumber_iff_exists_finiteDimensional_lowerBound`
  and the `Sources…SingularValueTransport` import.
* **PR order**: after PR 1/2, once the Spectra-free min–max lands.

### 1c. Reusable Hilbert–Schmidt identities
* **Home**: `ForMathlib/Analysis/InnerProductSpace/` orthogonal-series modules,
  `DavisKahan/Alternative/OperatorIdeal/HilbertSchmidt/`.
* **Ownership**: split `mathlib`/`tauceti`. **Final**: `TauCeti/Analysis/OperatorIdeal/HilbertSchmidt/…`.
* **Status**: `ready` for the Mathlib-only orthogonal-series parts; the
  H–S tensor/Schatten parts are `blocked-on-spectra-removal`
  (import `Spectra.Spaces.Tensor.HilbertSchmidt`).
* **PR order**: **PR 2/PR 3** (Hilbert–Schmidt & square-summable singular values).

### 1d. Closed operators & bounded extensions
* **Home**: `DavisKahan/SpectralTheory/ClosedOperator/`.
* **Ownership**: `tauceti`. **Final**: `TauCeti/Analysis/Operator/Closed/…`.
* **Status**: `blocked-on-tauceti` — must reconcile with the existing Tau Ceti
  `OneParameterSemigroups` roadmap before integration (do not create a parallel
  unbounded-generator theory). Some proofs are `blocked-on-spectra-removal`
  (`Interop/Spectra/ClosedOperator.lean`, `BoundedFromSpectrum.lean`).
* **PR order**: **PR 3** (after semigroup-roadmap coordination).

### 1e. Reducing restrictions / reducing subspaces
* **Home**: `DavisKahan/SpectralTheory/ReducingSubspace/`.
* **Ownership**: `tauceti`. **Final**: `TauCeti/Analysis/Operator/SpectralSubspace/…`.
* **Status**: `needs-api-refactor` (some routes via `Interop/Spectra/SpectralRestriction*`).
* **PR order**: PR 3 cluster.

---

## Tier 2 — general spectral / operator-equation theory

### 2a. Closed Sylvester equations
* **Home**: `DavisKahan/Sylvester/ClosedSylvesterEquation.lean`, `DavisKahan/Sylvester/Unbounded/`.
* **Ownership**: `tauceti`. **Final**: `TauCeti/Analysis/Operator/Sylvester/…`.
* **Status**: `blocked-on-spectra-removal` for the unbounded/resolvent inputs; the
  bounded algebraic core is closer to `ready`.
* **PR order**: **PR 4**.

### 2b. Pairwise spectral separation
* **Home**: `DavisKahan/Sylvester/PairwiseSpectrumGap.lean`,
  `…/PairwiseHomogeneousUniqueness.lean`.
* **Ownership**: `tauceti`. **Status**: `blocked-on-spectra-removal`
  (`GenuinePairwiseSpectrumGap` uses Spectra bridges).
* **PR order**: PR 4 cluster.

### 2c. Finite-dimensional Sylvester multipliers
* **Home**: `DavisKahan/FiniteDimensional/Sylvester/`.
* **Ownership**: `tauceti`. **Status**: `ready` (finite-dim, algebraic over `RCLike`).
* **PR order**: PR 4 (finite core first).

---

## Tier 3 — subspace geometry & perturbation theory

### 3a. Directed-angle / projection geometry
* **Home**: `DavisKahan/Geometry/Angle/`.
* **Ownership**: `tauceti` (generic) with `davis-kahan` wrappers kept downstream.
* **Final**: `TauCeti/Analysis/InnerProductSpace/OperatorAngle/…`.
* **Status**: `needs-api-refactor` — keep directed vs symmetric angles distinct;
  strip paper terminology from the generic layer.
* **PR order**: **PR 5** (operator angles & graph subspaces).

### 3b. Frame / trial-map factorization
* **Home**: `DavisKahan/SinTheta/FrameFactorization*.lean`, `…/Residual/TrialMap.lean`.
* **Ownership**: mixed `tauceti`/`davis-kahan`. **Status**: `needs-api-refactor`.
* **PR order**: PR 5 cluster.

### 3c. Graph subspace / Riccati infrastructure
* **Home**: `DavisKahan/DoubleAngle/`, `TanTheta/`, `TanTwoTheta/`, `Riccati/`.
* **Ownership**: `tauceti` for the generic graph/Riccati core; spectral
  perturbation theorems remain distinguishable from literal source wrappers.
* **Status**: `blocked-on-spectra-removal` / `needs-api-refactor`; many proved
  bodies are trapped behind `Experimental` boundaries (see the 33-item queue in
  `part-iii-production-extraction-queue.md`).
* **PR order**: later PRs (H: double-angle/tangent/Riccati).

---

## Tier 4–5 — stay in Davis–Kahan (do not extract)

* Finite Part III source facade `DavisKahan/Sources/DavisKahan1970/PartIII.lean`;
  literal Section 1–9 correspondence; paper theorem aliases; Prop 4.4
  counterexample; sharpness/equality source models; census/completion audits.
* Ownership `source-wrapper` / `davis-kahan`. These own paper numbering,
  historical terminology, and source-specific records; they must **not**
  determine the names or placement of generic Tau Ceti infrastructure. A thin
  `DavisKahan/Interop/TauCeti/` adapter layer translates general Tau Ceti APIs
  back into Davis–Kahan paper terminology where definitional equality does not
  suffice.

---

## Ordered upstream PR sequence (dependency closure)

1. **PR 1 — approximation numbers** *(staged this campaign)*: Basic, Adjoint,
   FiniteDimensional, MinMax, CourantFischer, OperatorModulus (clean part). No DK
   theorem; no Spectra.
2. **PR 2 — rectangular symmetric ideal families + Hilbert–Schmidt equivalences.**
3. **PR 3 — closed operators + reducing restrictions** (after `OneParameterSemigroups`
   coordination).
4. **PR 4 — Sylvester equations** (finite core first; unbounded after Spectra-free
   resolvent inputs exist).
5. **PR 5 — operator angles + graph subspaces.**
6. **PR 6 — finite Davis–Kahan Part III** (per `finite-dimensional-part-iii-audit.md`).
7. **PR 7 — unbounded sine-theta + source correspondence.**
8. Later — double-angle / tangent / Riccati / direct-rotation / continuation.

Every blocked cluster above names its exact blocker (a Spectra bridge
declaration, a source-facade import, or a Tau Ceti roadmap coordination point),
so no obstacle is left implicit.

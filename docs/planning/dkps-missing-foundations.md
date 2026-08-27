# Missing foundations for full paper-faithful generality (DKPS chain)

**Written 2026-08-27.** Derived from the `gaps` tables and non-`compiled_exact` rows of
`dev/{acharyya-2024,acharyya-2025,helm-2025,quench-2026}-full-source-census.json` and the
companion result-semantic reviews. Every claim below cites the gap id or row it comes
from, so it can be rechecked rather than trusted.

This answers one question: *what mathematical foundation is missing, such that its absence
is what forces an extra hypothesis or leaves a source result unrepresented?* Packaging
chores are listed separately at the end; they are not foundations.

## Current state, by paper

| paper | rows | not represented | stronger hypotheses | specialization | role replaced |
|---|---:|---:|---:|---:|---:|
| Acharyya 2024 | 14 | 3 | 3 | 5 | 0 |
| Acharyya 2025 | 18 | 1 | 0 | 0 | 11 |
| Helm 2025 | 8 | 0 | 5 | 0 | 0 |
| Quench 2026 | 11 | 0 | 4 | 0 | 1 |

Acharyya 2025's eleven `compiled_role_replaced` rows are the paper's internal proof
lemmas R1–R6 and L1–L5, discharged by a different route. That is a legitimate disposition,
not a foundation gap, and it is not counted below.

## F1 — Continuum model space with a measure, and L^p MDS theory

**Blocks:** `A24-R3` and `A24-L2` (headline) unrepresented, `A24-T5` specialization,
`A25-P1` unrepresented. Gaps `continuous-mds-lp`, `riemannian-proposition`.

The source introduces a compact model space, a model distribution `P`, continuous raw
stress as an integral functional, and an `mds(phi)` map, then states Lemma 2 and Theorem 5
as `L^p(P x P)` convergence. The package documents that its growing-model result is only a
countable family of finite per-stage statements and does not model the continuum
distribution or the integral at all. `grep` finds no `MemLp`/`eLpNorm` anywhere in
`Acharyya2024`; the `Lp` hits in `ForTauCeti` are operator-ideal symmetric gauges and
unrelated.

This is the largest single gap and it is upstream of others: the Quench replicate exponent
`(n+1)^(4+d)` is what it is because uniformity over an *infinite* model class is bought
with a union bound over a perspective net of size `(n+1)^d`
(`replicate-schedule-exceeds-source-rate`). A genuine continuum treatment is the route that
could remove the net rather than shrink it.

## F2 — Raw-stress to classical-MDS bridge, or eigengap-free CMDS perturbation

**Blocks:** `Q26-EQ1` role-replaced; Helm's eigenvalue floor. Gaps
`dkps-definition-raw-stress-vs-cmds`, `spectral-vs-rawstress-bridge`.

Quench Eq. (1) defines the perspectives as a raw-stress minimizer while Theorem 1 imports a
classical-MDS concentration bound and the proof uses it for the same `psi-hat`; the two
estimators are not known to agree. Helm cites Acharyya 2024's **eigengap-free** raw-stress
consistency theorem, but the implemented bridge goes through classical spectral MDS and so
must assume a population eigenvalue floor.

**This is the highest hypothesis-removal value in the list.** The floor
(`PerspectiveNondegeneracy`, Acharyya 2025 Assumption 2) is an assumption neither Helm nor
Quench states, and it is present in both only because of this substitution. Either
direction closes it: connect raw-stress minimizers to CMDS configurations, or develop
subspace perturbation that does not need an absolute spectral gap.

### F2 splits: the floor is needed for rates, not for convergence (found 2026-08-27)

Reading `Acharyya2024.rawStress_mds_stability` settles part of this. Its hypotheses are
minimality of the estimates, a unique pair profile, and dissimilarity convergence — **no
spectral condition anywhere**. So the population eigenvalue floor is not intrinsic to DKPS
consistency; it enters only because a bridge routes through classical MDS.

But that theorem concludes convergence of *pairwise distances*, not of coordinates. The step
from one to the other is Acharyya 2024's Corollary 1, which the census records as the
unrepresented headline `A24-C1`. So F2 and F4 are the same blockage, and the exact form of the
missing lemma is now proved: `TauCeti.exists_rigidMotion_of_dist_eq` in
`ForTauCeti/Analysis/InnerProductSpace/Gram/Matrix.lean` — equal pairwise distances imply the
configurations differ by a rigid motion. Mathlib does not have this; it has `Congruent` and the
triangle criteria only.

**The split.** What each paper needs from the bridge is different:

- **Helm 2025 needs only convergence.** Its Theorem 1 and Theorem 2 conclusions are `Tendsto`
  statements with no rate. The eigengap-free raw-stress route is qualitative and therefore
  suffices, so Helm's floor is **avoidable**, modulo the approximate form of the rigidity lemma
  (distances converge ⇒ coordinates converge after alignment), which is a compactness argument
  over the isometry group and needs no spectral gap.
- **Quench 2026 needs rates.** Its capstones carry `entryRate` and `GrowingConfigControl` and
  conclude high-probability bounds at each stage. A *quantitative* Gram-to-configuration bound
  genuinely requires a spectral gap — eigenvector perturbation is unstable without one — so
  Quench's floor is likely **intrinsic**, not an artifact of the bridge.

That is a materially better picture than "remove the floor". The honest targets are: remove it
from Helm, and for Quench either justify it as necessary or replace it by a residual-gap
condition that the setting implies.

## F3 — Growing-sample (triangular-array) perturbation framework

**Blocks:** `A24-T4` specialization, `A24-T3` stronger hypotheses. Gaps
`growing-n-concentration`, `growing-query-rate-wiring`, `theorem1-rate-not-instantiated`.

Acharyya 2025's rate theorem is stated for a *fixed* collection of `n` models with the
asymptotics in the replicate index. Every downstream use needs `n`, `m`, `r` to vary
together with the target augmented into the matrix. Quench already built this privately —
`GrowingConfigControl`, `GrowingSpectralSubevents`, `GrowingConfigControl.of_tendsto` — and
those are the pieces the capstones actually consume, while the registered rate endpoint is
consumed by nothing.

The foundation work here is mostly *promotion*: lift the growing-stage certificates out of
`DkpsQuench2026` into `ForTauCeti` and restate the Acharyya rate theorem over them. That
would serve Acharyya 2024 Theorem 4, the Acharyya 2025 rate chain, and Quench at once.

## F4 — Rigid-motion existence and MDS identifiability

**Blocks:** `A24-C1` (headline) unrepresented, `A24-R1` specialization, `A24-T1`/`A24-T3`
stronger hypotheses. Gaps `rigid-alignment-corollary`, `affine-invariance-partial`,
`fixed-profile-uniqueness`.

Two related missing statements:

1. **Existence of the rigid motion.** The source upgrades pairwise-distance convergence to
   existence of orthogonal `W^(u)` and translations `a^(u)` with coordinate convergence.
   `rawStress_translate` proves only the translation half. `ForTauCeti` has the ingredients
   — `NearIsometry`, `AlignedBasis`, `IntertwiningUnitary`, `LinearIsometry` — but not the
   packaged "configurations with equal pairwise distances differ by a rigid motion".
2. **Identifiability.** Lean proves convergence to the minimizer *set* and recovers a fixed
   profile only under `RawStress.UniquePairProfile`. The source names a fixed limiting
   profile with no uniqueness premise.

## F5 — Regularity for risk functionals

**Blocks:** Helm's five `compiled_stronger_hypotheses` rows. Gaps
`stronger-analysis-hypotheses`, `label-compact-support`.

The paper states sequential/pointwise continuity; the Lean theorems use joint continuity,
compact range, and explicit estimator measurability, plus a `BoundedLabelSupport` that a
search of the retained prose and TeX could not locate in the source at all. The missing
foundation is enough measurability/domination infrastructure to get the risk limit from
sequential continuity alone.

Smaller than F1–F4 and confined to one paper, but it is five rows and one of the extra
hypotheses appears to have no source at all.

## Not foundations — packaging chores

- `t1-literal-finite-wrapper`: no single public theorem reproducing Acharyya 2025 Theorem
  1's displayed finite probability bound with the source constant 16 and
  `sum gamma_ij/(r m eps^2)`. The pieces are all compiled.
- `growing-query-rate-wiring`: the second-moment mechanism and the `gamma/r` estimate are
  both proved; they are fed to the growing-query theorem as an abstract hypothesis instead
  of being discharged in one theorem.
- `inherited-acharyya-v1-norm`, `v1-norm-inconsistency`, `tie-display-proof-mismatch`,
  `support-wording-repair`: source defects, already dispositioned.

## What TauCeti already provides (checked 2026-08-27)

`external/TauCeti` is a build input, so anything here is directly importable. Searched all
12,360 modules for each foundation.

**Materially changes F1.** TauCeti has the measure-theoretic layer the continuum MDS
treatment needs:

- `TauCeti/Probability/Process/EmpiricalMeasure.lean` — `empiricalPopulation`,
  `empiricalMeasure`, and crucially `integral_empiricalPopulation`:
  `∫ f d(empiricalPopulation x) = (card κ)⁻¹ • ∑ i, f (x i)`.
- `TauCeti/Probability/StrongLaw.lean` — `strong_law_ae_infinitePi`: averages along the
  coordinates of `Q^{⊗ℕ}` converge a.e. to `∫ f dQ`.
- `TauCeti/Probability/Exchangeability/ConditionallyIID/StrongLaw.lean` —
  `tendsto_integral_empiricalMeasure_ae` and friends.
- `TauCeti/MeasureTheory/OptimalTransport/` — Wasserstein cost and gluing.

`integral_empiricalPopulation` is the exact bridge: the paper's finite raw stress is a
double sum, which is `n²` times an integral against the empirical measure on each factor,
and the continuous raw stress is the same integral against `P`. So F1 is not "build the
continuum theory" — it is "define raw stress as an integral functional and connect the
finite case through TauCeti's empirical measure", with the strong law supplying the limit.
Substantially smaller than the gap text implies.

**Provides nothing for F2, F3, F4.** No Davis--Kahan, `sinTheta`, Procrustes, eigenvalue
perturbation, triangular arrays, covering numbers, or concentration inequalities. The
`Weyl` hits are representation-theoretic Weyl modules, unrelated. The spectral perturbation
layer is genuinely ours to build.

**Partial for F5.** Uniform integrability appears via `Probability/Martingale/Convergence`
(Mathlib's `UnifIntegrable`); nothing purpose-built for risk functionals.

## Suggested order

F2 first — it removes a stated-nowhere hypothesis from two papers and closes `Q26-EQ1`.
Then F3, which is largely promotion of code that already exists and unblocks three rows.
F4 next; it closes the one unrepresented headline. F1 is the deepest and the only one that
could remove the Quench net cost, but it is a new development rather than a repair. F5 is
independent and can be done whenever.

Per `AGENTS.md` and standing direction: do not add `DkpsQuench2026` theorems that neither
dispatch an assumption nor weaken a hypothesis. Foundation work belongs in `ForTauCeti`.

---

## Status after the 2026-08-27 pass

The table at the top of this document is stale. Current statuses across the four application
censuses:

| paper | rows | not represented | stronger hypotheses | specialization | source repair |
|---|---:|---:|---:|---:|---:|
| Acharyya 2024 | 15 | 0 | 0 | 5 | 5 |
| Acharyya 2025 | 19 | 0 | 0 | 0 | 3 |
| Helm 2025 | 12 | 0 | 0 | 0 | 2 |
| Quench 2026 | 14 | 0 | 4 | 0 | 3 |

**No row is unrepresented, and only Quench still carries hypotheses beyond its source.**

### What closed

- **F2/F4, eigengap-free distance-to-coordinates.** `TauCeti.exists_delta_forall_exists_rigidMotion`
  is uniform approximate rigidity — one modulus for *every* pair of configurations, which is what
  a random target needs. `TauCeti.alignmentError` / `TauCeti.alignedConfig` package it and
  `TauCeti.tendsto_measure_alignmentError_gt` moves it to convergence in probability.
  Helm's Equation (3) is now derived with no spectral hypothesis at all
  (`alignmentConsistency_of_pairwiseDist`). Acharyya 2024's Corollary 1 has both modes.
- **F1, continuum MDS.** `Acharyya2024.ContinuousMDS` defines the source's double-integral raw
  stress and the minimizer set, with `continuousRawStress_empiricalPopulation` tying it to the
  finite raw stress through TauCeti's empirical measure. Lemma 2's `L^p` conclusion is proved
  for the empirical model distribution, along the full sequence and uniformly in `p`.
- **F5, regularity for risk functionals.** Not needed as posed. Assumption 2 as printed holds the
  labels fixed and moves only the embeddings; Assumption 4's gloss holds the label fixed. Both
  suffice: the continuous-mapping step compares configurations carrying identical labels
  (`tendstoInMeasure_comp_of_continuous_fst`), and the measurability joint continuity was
  supplying comes from Carathéodory (`stronglyMeasurable_combined_loss_of_printed`).
  `Theorem1_printed` runs on the printed readings and does not use Assumption 3.

### What is left

- **The perspective net (was F1's real cost).** Quench's compact-infinite route needs
  `NetReplicateRate`: `r n / (n+1)^(2 + entropyPower) → ∞`. The finite route now runs at the
  source's `r = ω(n³)` exactly. The gap between them is the net, so closing it means a continuum
  treatment, not constant-tuning.
- **F3, triangular arrays.** Unchanged: Acharyya 2024's Theorems 2 and 4 are still specializations
  because the growing-`m` assembly is not built. `growing-n-concentration`.
- **Population law in Lemma 2 / Theorem 5.** The `L^p` result holds against the empirical model
  measure; the population case is what the source attributes to the cited literature.
- **Quench's remaining excess** is the explicit sampling and measurability interface, not the
  eigenvalue floor and not the replicate schedule. The floor is the paper's own "under technical
  assumptions" named — Quench imports Acharyya 2025 Theorem 2 with that phrase, and its
  Assumption 2 is the floor.

### Source defects found, all machine-checked

- Acharyya 2024 Corollary 1 is **false as printed**: the aligning rotation cannot sit outside the
  probability (`not_exists_deterministic_rigidMotion_of_pairDist_exact`).
- Acharyya 2024 Theorem 1's fixed limiting profile is **not available** without a uniqueness
  premise (`no_fixed_limiting_profile`); `UniquePairProfile` is a repair, not an added assumption.
- Acharyya 2024 Remark 1's invariance is **rigid, not affine** (`rawStress_not_affine_invariant`).
- Acharyya 2025 Proposition 1 is **false as printed**: its hypothesis constrains the ambient
  manifold, its conclusion the placement of the models within it
  (`no_eigenvalue_floor_for_const_selection`).
- Helm 2025 Theorem 1 is **not provable as stated** without an envelope for the loss
  (`prob_convergence_not_enough_for_expectations`), and its Theorem 3 reference has no referent.

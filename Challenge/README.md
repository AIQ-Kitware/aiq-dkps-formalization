# DKPS formalization - challenge manifest

`Challenge/` is a comparator and regression surface for reusable results that
were isolated during the formalization. The directory names `MathlibCandidate`
and `MathlibPending` are historical: the direct Mathlib submission track is
closed, and reusable mathematics is now packaged in `ForTauCeti` for Tau Ceti.
The challenge files remain useful because they freeze theorem statements,
exercise dependency boundaries, and support comparator/axiom checks.

```
Challenge/
  MathlibCandidate/  - historical candidate statement/conformance surfaces
  MathlibPending/    - additional statement/conformance and leaderboard surfaces
```

The DKPS paper libraries are not comparator challenges. Their paper-specific
vocabulary and source fidelity must be reviewed through their source maps,
censuses, and ordinary Lean builds rather than inferred from comparator success.

Principles:

- **Challenge holes are immutable.** The open proofs in every
  `Conformance.lean` are intentional comparator placeholders, not repository
  proof debt. Never fill them. Implement the theorem in the ordinary library
  module and let the paired `Leaderboard.lean` plus Comparator verify statement
  equality and permitted dependencies. This follows Comparator's challenge /
  solution model: <https://github.com/leanprover/comparator>.
- **Leaf theorems only.** Each challenge lists only the *leaf* (top-level) theorems
  — those not used to prove any other listed theorem. `#print axioms` on a leaf
  transitively certifies its entire proof tree, so the supporting lemmas need not
  be listed. This is the same "expose only the entry point" rule a comparator
  reviewer asked for.
- **Axiom gate.** Every listed theorem is verified to depend only on
  `propext, Classical.choice, Quot.sound` — no `sorryAx`, no custom axioms.
- **No false dependency arrows.** The reusable contributions are *independent*
  results. They were *motivated* by the DKPS work but are not owned by any
  paper, so this manifest does not link candidates to papers as dependencies.

Any Mathlib gap/readiness claims below are historical observations from the 2026-06-14 audit, not a current submission queue.

---

## Family 1 - `MathlibCandidate/` (historical candidate surfaces)

These three theorem surfaces were the small opening set used by the historical Mathlib-readiness audit. Keep them for comparator/regression value; current reusable-library work targets Tau Ceti.

| # | Challenge | Leaf theorem(s) | Destination | Why it clears the bar |
|---|---|---|---|---|
| 01 | GramRigidity | `Matrix.gram_eq_gram_iff_exists_linearIsometryEquiv_map_eq` | `Analysis/InnerProductSpace/GramMatrix.lean` | canonical Gram-rigidity surface |
| 02 | CourantFischerWeyl | `abs_eigenvalues_sub_le_opNorm` (k-th eigenvalue min–max + Weyl perturbation) | new `Analysis/InnerProductSpace/CourantFischer.lean` | Mathlib has only Rayleigh + the extremal eigenvalue; **Weyl & k-th min–max absent**. Canonical |
| 03 | DavisKahan | `sum_norm_sub_starProjection_span_sq_le`, `sum_cross_norm_inner_eigenvectorBasis_sq_le_of_rank_floor` | new `Analysis/InnerProductSpace/DavisKahan.lean` | sin-Θ theorem **absent**. Canonical |

---

## Family 2 - `MathlibPending/` (historical pending surfaces)

These surfaces record results that were not in the historical opening set. Their old `pending` label is provenance only; it does not describe an active Mathlib promotion workflow.

### Advertising-level Davis--Kahan results

This subsection is intentionally selective. A theorem appears here only when it
is a recognizable literature endpoint or a genuinely reusable majorization
result—not because it was difficult to formalize or useful internally. Routine
corollaries, conditional harmonic reductions, notation bridges, and local
transport lemmas are deliberately excluded.

| Challenge | Leaf theorem(s) | Why it clears the advertising bar |
|---|---|---|
| DavisKahanSharp | `DavisKahanTheory.sinAngleOperator_perturbation_le` | sharp full-space sin-Theta theorem for every unitarily invariant norm, obtained by coupling both directed blocks without a factor-two loss |
| DavisKahanSinTheta | `DavisKahanTheory.partIII_sinTheta_uiNorm` | the source-faithful Part III sin Theta theorem for every unitarily invariant norm |
| DavisKahanSinTwoTheta | `DavisKahanTheory.partIII_sinTwoTheta_uiNorm` | the source-faithful Part III sin 2Theta theorem for every unitarily invariant norm |
| DavisKahanTanTheta | `DavisKahanTheory.partIII_tanTheta_vector` | the pole-free per-vector Part III tan Theta theorem, with no unnecessary dimension-comparison hypothesis |
| DavisKahanTanTwoTheta | `DavisKahanTheory.partIII_tanTwoTheta_opNorm` | the sharp operator-norm Part III tan 2Theta theorem with strict quarter-turn avoidance |
| DavisKahanProjectorDifference | `DavisKahanTheory.projector_difference_opNorm` | the sharp factor-one finite projector-difference theorem under two-sided gaps, with no rank hypothesis |
| DavisKahanSylvesterPiOverTwo | `DavisKahanTheory.uiNorm_sylvester_le_of_spectralDistance`, `DavisKahanTheory.sylvester_hasFiniteUnitaryOrbitCertificate_of_spectralDistance` | the arbitrary-disjoint-spectrum Bhatia--Davis--McIntosh bound for every rectangular UI norm and the exact solution-specific finite orbit certificate at mass pi/2 |
| Davis1963Rotation | `rotation_add_displacement_le_hilbertSchmidt` | Davis's sharpened 1963 total-rotation theorem: eigenvalue motion and eigenvector rotation share one Frobenius perturbation budget |
| YuWangSamworth | `sqrt_sum_cross_le_of_population_gap` | the exact population-gap Frobenius sin-Theta theorem used in modern statistical perturbation theory |

`RectangularFanDominance/Leaderboard.lean` separately audits the rectangular
Ky Fan/orbit-majorization machinery. It is advertising-level mathematics, but
leaderboard-only because its vocabulary and implementation still cohabit one
large staging module. It is retained as a regression surface rather than as an
active promotion task.

`ApproximationNumbers/Leaderboard.lean` audits the infinite-dimensional
approximation-number localization, strong-cutoff convergence, and finite Ky Fan
triangle endpoints over both real and complex Hilbert spaces. It is leaderboard-only because the underlying approximation-number vocabulary
remains project-staged. It is retained as a regression surface rather than as
an active promotion task.

The legacy `DavisKahanPartIII` aggregate was **removed on 2026-07-30**: it pinned exactly the four theorems the four dedicated Davis--Kahan
challenges pin and nothing else, so five directories and five comparator
configurations were maintained for four theorems, and the comparator ran each of
those proofs twice.  The focused configurations above are now the only
advertising surfaces.

The four theorems themselves are unaffected -- they are `alias`es in
`DavisKahan/Sources/DavisKahan1970/PartIII.lean`, the stable source-facing import
surface for the finite Part III results, which each of the four dedicated
challenges imports directly.  **That module, not the deleted challenge, is what
to point at for the exact paper form of the Davis--Kahan proofs.**  The canonical spectral-projector wrapper is printed by the projector
leaderboard but is not a second challenge leaf because it is a direct corollary
of the reducing-subspace theorem.

### Other pending results

| Challenge | Leaf theorem(s) | Why pending |
|---|---|---|
| Berge | `continuous_iInf_of_isCompact`, `upperHemicontinuousAt_isMinOn`, `exists_modulus_isMinOn` | likely proven in **too narrow a form** for a canonical Mathlib `Topology` contribution; needs generalization to holistic, reusable shape before it's maintainer-quality |
| RankFactorization | `Matrix.rank_le_iff_exists_eq_mul` | matrix form absent but must be related to abstract `rank_le_iff_exists_linearMap`; confirm framing/value |
| RankPsdRealization | `Matrix.posSemidef_and_rank_le_iff_exists_conjTranspose_mul_self`, `Matrix.eigenvalues₀_eq_zero_of_le` | plain `posSemidef_conjTranspose_mul_self` already exists — only the rank-**control** is novel; confirm it's worth a PR |
| RestrictCoverMeasurable | `measurable_of_iUnion_restrict` | clean countable analogue, but minor; confirm worth standing alone |
| SampleMeanMSE | `integral_norm_sq_average_sub_of_iid`, `integral_norm_sq_average_sub_le_of_bound` | vector-valued (scalar variance exists); confirm not trivially derivable |
| NearIsometry | `LinearMap.exists_linearIsometryEquiv_norm_sub_le`, `ContinuousLinearMap.exists_linearIsometryEquiv_norm_sub_le` | quantitative polar factor; niche |
| CfcMeasurable | `measurable_cfc_comp`, `measurableSet_exists_mem_le` | involved proof; destination unsettled |
| MatrixConcentration | `measure_forall_eigenvalues₀_ge_ge` (+ entrywise→operator helpers) | elementary route gives **loose `n`/`n²` constants**; Mathlib would want a matrix-Bernstein sharpening |
| SpectralFunctionMeasurable | `Matrix.measurable_specTransform` | novel, but **deliberately unused** by the final discharge; no settled home. Its (matrix-valued measurability) statement is not cleanly Mathlib-only expressible, so it carries an **axiom-audit `Leaderboard` only** — no Mathlib-only `Conformance`/comparator config |
| ProbabilityQoL | `one_sub_measure_compl_le`, `meas_gt_le_ofReal_integral_sq_div_sq` | **too small** to stand alone |
| TendstoInMeasure | `tendstoInMeasure_of_tendsto_measure_dist_le_rate` | verify it is substantive vs. a thin wrapper |

---

## DKPS papers — the repo's end states (documented, not comparator challenges)

These are the four fully-formalized papers all the upstream work was in service of.
They are **not** comparator challenges (see the rationale in the intro). Each was
verified clean — `#print axioms = {propext, Classical.choice, Quot.sound}`, no
`sorryAx`, no custom axioms (checked 2026-06-14). Headline statements and any
"beyond the paper" assumptions are documented in each library's `README.md`.

| Paper | Main theorem(s) | Axiom status |
|---|---|---|
| Acharyya2024 | `Consistency.fixed_models_fixed_queries_consistency_of_uniqueProfile`, `…fixed_models_growing_queries_consistency_of_uniqueProfile`, `…growing_models_growing_queries_perStage_consistency_of_uniqueProfile` (and `…_of_sample_limit_uniqueProfile`) | clean ✓ |
| Acharyya2025 | `RateChain.tendsto_endToEndRate_zero` (+ `tendsto_configBound_comp_zero`) | clean ✓ |
| DkpsQuench2026 | `QueryEfficiency.finiteAllQueries`, `QueryEfficiency.infiniteAllQueries` | clean ✓ |
| Helm2025 | `DKPS.Theorem1`, `DKPS.Theorem2_bayes` (+ `alignmentConsistency_of_highProb_configError`) | clean ✓ |

---

## Replaces

This manifest supersedes the old `Challenge/Gram`, `Challenge/PsdGram`,
`Challenge/Spectral`, and `Challenge/Inventory/*` challenges (including the
69-theorem aggregate), which mixed headline results with their supporting lemmas.

# DKPS formalization - challenge manifest

`Challenge/` is a comparator, regression, and mathematical-exhibition surface.
The direct Mathlib submission track is closed; reusable mathematics is packaged
in `ForTauCeti` for Tau Ceti, while source-specific formalizations may have
dedicated challenge suites of their own.  The challenge files freeze theorem
statements, exercise dependency boundaries, and support comparator/axiom checks.

```
Challenge/
  DavisKahan1970/    - source-oriented exhibition of the 1970 formalization
  MathlibCandidate/  - historical candidate statement/conformance surfaces
  <Name>/            - neutral comparator/regression challenge packages
```

The obsolete `MathlibPending` layer has been removed.  Challenges that used to
live there are ordinary `Challenge/<Name>/` packages now; their value is
regression, dependency isolation, or mathematical exhibition, not a claim about
Mathlib submission status.

The four DKPS application-paper libraries are not comparator challenges. Their
paper-specific vocabulary and source fidelity must be reviewed through their source
maps, censuses, and ordinary Lean builds rather than inferred from comparator success.
Davis--Kahan 1970 is intentionally different: its dedicated challenge is an
exhibition/regression surface for the source formalization, not a Mathlib queue.

Principles:

- **Challenge holes are immutable.** The open proofs in every
  `Conformance.lean` are intentional comparator placeholders, not repository
  proof debt. Never fill them. Implement the theorem in the ordinary library
  module and let the paired `Leaderboard.lean` plus Comparator verify statement
  equality and permitted dependencies. This follows Comparator's challenge /
  solution model: <https://github.com/leanprover/comparator>.
- **Recognizable endpoints, not graph leaves.** A challenge may expose a theorem
  that later source results reuse.  Davis--Kahan's headline inequalities are
  valuable precisely because they are useful downstream.  Selection is based on
  mathematical recognizability, source fidelity, and exhibition value rather than
  terminal position in the repository proof DAG.
- **Axiom gate.** Every listed theorem is verified to depend only on
  `propext, Classical.choice, Quot.sound` — no `sorryAx`, no custom axioms.
- **No false dependency arrows.** The reusable contributions are *independent*
  results. They were *motivated* by the DKPS work but are not owned by any
  paper, so this manifest does not link candidates to papers as dependencies.

Any Mathlib gap/readiness claims below are historical observations from the 2026-06-14 audit, not a current submission queue.

---

## Family 1 - `MathlibCandidate/` (historical candidate surfaces)

These three theorem surfaces were the small opening set used by the historical Mathlib-readiness audit. Keep them for comparator/regression value; current reusable-library work targets Tau Ceti.

| # | Challenge | Exhibited theorem(s) | Destination | Why it clears the bar |
|---|---|---|---|---|
| 01 | GramRigidity | `Matrix.gram_eq_gram_iff_exists_linearIsometryEquiv_map_eq` | `Analysis/InnerProductSpace/GramMatrix.lean` | canonical Gram-rigidity surface |
| 02 | CourantFischerWeyl | `abs_eigenvalues_sub_le_opNorm` (k-th eigenvalue min–max + Weyl perturbation) | new `Analysis/InnerProductSpace/CourantFischer.lean` | Mathlib has only Rayleigh + the extremal eigenvalue; **Weyl & k-th min–max absent**. Canonical |
| 03 | DavisKahan | `sum_norm_sub_starProjection_span_sq_le`, `sum_cross_norm_inner_eigenvectorBasis_sq_le_of_rank_floor` | new `Analysis/InnerProductSpace/DavisKahan.lean` | sin-Θ theorem **absent**. Canonical |

---

## Davis--Kahan 1970 source exhibition

`Challenge/DavisKahan1970/` replaces the six separate historical split
Davis--Kahan comparator directories.  One conformance module now
shows the formalization as a coherent source-facing body rather than a collection
of putative Mathlib submissions.

The comparator includes the four classical trigonometric theorem families at
the strongest source-facing surfaces that can be stated independently of their
proof modules, plus two particularly useful exhibition results:

| Surface | Comparator target(s) | Purpose |
|---|---|---|
| sin Theta | finite residual/UI specialization, finite perturbation/UI specialization, arbitrary-Hilbert source-UI symmetric theorem | shows the low-dependency headline specialization plus the later Proposition 6.1-level generality; the finite/ambient entries must not be mistaken for one literal Section 2 statement |
| tan Theta | finite source-shaped Ritz result, arbitrary-Hilbert directed spectral theorem, corrected ambient theorem under crossed-defect condition (3.5), **literal Section 2 pole-counterexample target** | preserves the directed/ambient distinction while making the apparent infinite-dimensional source-scope defect executable instead of silently adding (3.5) |
| sin 2Theta | finite UI specialization, arbitrary-Hilbert directed residual theorem, arbitrary-Hilbert ambient theorem | exposes both printed geometries at source UI-norm scope |
| tan 2Theta | finite sharp operator-norm theorem, branch-free infrastructure, **exact directed residual Section 2 inequality**, **exact ambient Section 2 inequality**, **public pole-exclusion target**, and **unbounded arbitrary-UI directed target** | both bounded arbitrary-UI conclusions are now green from the printed hypotheses; the signature-visible pole/domain certificate and source-shaped unbounded arbitrary-UI assembly remain intentionally red |
| projector distance | `DavisKahanTheory.projectorDifference_restrictionSpectra_opNorm` | canonical modern projector/subspace-distance presentation on an arbitrary complex Hilbert space |
| false Proposition 4.4 | `DavisKahanTheory.proposition4_4_counterexample` | exhibits source fidelity by formally refuting a false printed claim instead of silently dropping it |

The leaderboard also audits the definitive generalized sine Theorem 6.1 over
both scalar fields, real-Hilbert counterparts of the corrected tangent and
double-angle endpoints, the two-dimensional/direct-sum sharpness package and
first-order asymptotics, the bilateral-shift separation of dimension conditions
(1.5) and (3.5), the direct formal negation of Proposition 4.4, Section 8 branch
selection, and source-numbered Section 9 equation (9.7).  These are exhibition
sentinels rather than additional comparator holes.

Three source-fidelity targets are deliberately present in
`comparator/davis-kahan-1970.json` without matching leaderboard declarations:
the literal Section 2 ambient `tan Theta` pole counterexample, a public
pole-exclusion theorem for the bounded exact `tan 2Theta` results, and the
unbounded directed arbitrary-UI `tan 2Theta` source wrapper.  The bounded
directed residual and ambient arbitrary-UI `tan 2Theta` conclusions are both
now green from the printed hypotheses.  Thus `lake build
Challenge` remains a useful compile check while
`scripts/check_comparator_signatures.py comparator/davis-kahan-1970.json` stays
red exactly where the source treatment is not yet complete.  Do not weaken the
challenges merely to make the comparator green.

## Other comparator and exhibition challenges

The remaining top-level challenge packages are older, mostly reusable theorem
surfaces retained for regression and dependency checks.  They have no `pending`
status in the repository.

| Challenge | Exhibited theorem(s) | Historical context |
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

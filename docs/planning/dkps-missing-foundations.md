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

## Suggested order

F2 first — it removes a stated-nowhere hypothesis from two papers and closes `Q26-EQ1`.
Then F3, which is largely promotion of code that already exists and unblocks three rows.
F4 next; it closes the one unrepresented headline. F1 is the deepest and the only one that
could remove the Quench net cost, but it is a new development rather than a repair. F5 is
independent and can be done whenever.

Per `AGENTS.md` and standing direction: do not add `DkpsQuench2026` theorems that neither
dispatch an assumption nor weaken a hypothesis. Foundation work belongs in `ForTauCeti`.

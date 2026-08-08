# Davis--Kahan 1970 completion campaign: triage list

Working notes for the "finish the source formalization to 100%" campaign.
**This file is the durable state.** Update it as items move. It exists so the
campaign survives context compaction: read it first, trust it over memory,
but verify its claims against the build before acting on them.

Baseline for this campaign: `65724ef9`.

## Authorities

* `AGENTS.md`, `ForTauCeti/README.md`, `docs/planning/davis-kahan-full-paper-goal.md`
* `dev/davis-kahan-1970-full-source-census.json` (authoritative row status; contains
  stale narrative -- reread the source and grep the whole repo before believing a
  `next_action`)
* `prose/distilled_literature/DavisKahan1970_part_III.tex` and siblings (the
  maintained transcription)

### Roadmap location -- RESOLVED, and it is not where a first look suggests

The `OperatorTheory` roadmap family **exists** at commit `824a78d`, but **not** on
`TauCetiRoadmap/main` and **not** in the `/home/joncrall-agent/TauCetiRoadmap`
checkout. It is on branch `hilbert-space-operator-theory` of the remote backing
`/home/joncrall-agent/TCR-minimal`. To read it:

```
git -C /home/joncrall-agent/TCR-minimal worktree add <tmpdir> 824a78d --detach
ls <tmpdir>/TauCetiRoadmap/OperatorTheory/
```

Nine roadmaps: `PolarDecomposition`, `OrthogonalGeometry`, `Majorization`,
`PrincipalAngles`, `SelfAdjointSpectralTheory`, `OperatorIdeals`,
`SpectralSubspacePerturbation`, `MatrixSpectralStatistics`.

A sibling branch `hilbert-space-operator-theory-minimal` (`b1c9231`, the checked-out
state of `TCR-minimal`) carries a *cut-down* successor named
`HilbertSpaceOperatorTheory` with four roadmaps. Do not mistake it for the family the
campaign brief names.

**Known roadmap/API mismatch.** `SpectralSubspacePerturbation` Part C asks only for
"the sharp `tan 2θ` ... with the quarter-turn conclusion, under *ordered* internal
separation" -- i.e. the **selected-branch** theorem. That is not the printed Section 2
`tan 2Θ` theorem, which selects no branch. The branch-free theorem proved in this
campaign is strictly stronger than the roadmap's stated target. The roadmap should
say so.

### Placement rule actually used

The repo's enforced layering is `Mathlib -> TauCeti -> DavisKahan`, staged through
`ForTauCeti/`, and `scripts/check_dependency_layers.py` enforces it. The roadmap's
ownership boundaries map onto existing `ForTauCeti/Analysis/...` directories; there
is no `ForTauCeti/OperatorTheory/` tree and this campaign does not create one.

| roadmap owner | actual directory |
|---|---|
| Majorization (UI norms, Ky Fan, Fan dominance) | `ForTauCeti/Analysis/InnerProductSpace/RectangularUnitarilyInvariantSeminorm/`, `.../KyFan.lean` |
| OperatorIdeals (approximation numbers, gauges) | `ForTauCeti/Analysis/OperatorIdeal/` |
| PrincipalAngles | `ForTauCeti/Analysis/InnerProductSpace/PrincipalAngles.lean`, `.../SinTheta/` |
| PolarDecomposition | `ForTauCeti/Analysis/InnerProductSpace/Polar/`, `OperatorModulus.lean` |
| SelfAdjointSpectralTheory | `ForTauCeti/Analysis/InnerProductSpace/LinearPMap/`, `.../Spectral/`, `.../ProjValMeasure/` |
| SpectralSubspacePerturbation | `ForTauCeti/Analysis/InnerProductSpace/Sylvester/`, `DavisKahan/DoubleAngle/`, `DavisKahan/SinTheta/` |
| paper numbering / Section 9 / counterexamples | `DavisKahan/Sources/DavisKahan1970/` |

## Standing constraints

* Never run concurrent `lake build`s (one shared `.lake`).
* `warningAsError`: deprecations, unused simp args, unused section variables are
  hard errors. `omit [Inst] in` goes **before** the docstring.
* Do not pipe `lake build` into `tail` without `set -o pipefail`.
* Probe files go in `$CLAUDE_JOB_DIR/tmp`, never the repo root.
* `#print axioms` every new capstone; accept only
  `[propext, Classical.choice, Quot.sound]`.

## Known baseline gate failures (pre-existing, NOT introduced here)

1. `check_library_structure.py` -- 16 Experimental aggregate modules flagged by
   rule 3.
2. `check_dependency_layers.py` -- 6 `GENERIC_IMPORTS_SOURCE` findings, all
   `DavisKahan/SpectralTheory/FormMethod/Beam{Section9,Spectrum}.lean` importing
   `DavisKahan/Sources/DavisKahan1970/Section9/*`.
3. `check_davis_kahan_frontier.py` reports **"Lean: not available"** and cannot
   score any node, because `dev/davis-kahan-1970-frontier.json` points 13 manifest
   nodes at `DavisKahan/Experimental/Frontier/Section9Analytic.lean`, deleted at
   `95bbd5ea`. Running `--write-report` therefore **overwrites the committed report
   with all-`?` rows** -- do not run it with `--write-report` until T0 is done.

## Triage list

Status: `TODO` / `WIP` / `DONE` / `BLOCKED`.
Re-rank after each item. Hardest open mathematics first, except where a cheap
prerequisite unblocks auditing.

### T0 `TODO` -- repair the frontier manifest (prerequisite, cheap)

`dev/davis-kahan-1970-frontier.json`: re-point the 13 `s9-*` nodes off the deleted
`Section9Analytic` module onto the real declarations (`beamOperator`,
`beamSinTheta_le`, `beamSinTwoTheta_lt`, `beamSinTwoThetaSum_lt`,
`realSpectrum_beamOperator_subset_gap`, `beamRitz_matrix`,
`beamResidualGram_matrix`, `beamFiniteDataCertificate`, ...). Also map the three
unmapped rows `DK-6-appendix`, `DK-6.1-lem`, `DK-6.1-prop`. Then
`--write-report` becomes safe and the whole frontier is scoreable again.

### T1 `WIP` -- Section 9 equation (9.3): second residual approximation number

Row `DK-9.1-9.4` (`partial_or_wrapper_missing` / `proved_conditional`).
(9.1), (9.2), (9.4) are already genuine operator theorems. Only (9.3) remains.

**Already proved and pushed** (`80e2940a`, in `BeamSection9.lean`):
`beamResidual`, `beamTrialVecOne/Two`, `beamTrialVec_orthonormal`,
`beamTrialVec_span_eq_top`, `exists_beamTrialVec_repr`, `beamResidual_gram`,
`beamGramTopCoefficient`, `beamGram_orthogonal_direction`.

**Remaining, purely mechanical:**
1. `beamGramTopVector := phi1 + c . phi2`, `c = -(sqrt 75 + sqrt 76)`.
2. `beamResidualRankOne eps := (innerSL C w).smulRight ((1+c^2)^-1 . R w)`;
   `rank <= 1` via `range <= span {v}` and `rank_span_le`.
3. `(R - K)(a.phi1 + b.phi2) = ((c a - b)/(1+c^2)) . R (c.phi1 - phi2)`.
4. `||R z0||^2 = (1+c^2) * residualGramEigenvalueLow eps` from
   `beamGram_orthogonal_direction`.
5. Cauchy--Schwarz `|c a - b|^2 <= (1+c^2)(|a|^2+|b|^2)`, giving
   `||R - K|| <= residualBottomSingularValue eps`, hence
   `a_1(R) <= residualBottomSingularValue eps` by
   `ContinuousLinearMap.approximationNumber_le_norm_sub`.
6. `a_0 + a_1 <= residualKyFanTwo eps` (`a_0` is
   `norm_beamPerturbation_comp_trialIncl_le`), then
   `sinTheta_unbounded_gauge_of_spectrum_gap` at `beamKyFanTwo` with the (9.1)
   data gives (9.3).

**Tactic obstacles hit on the first attempt (not mathematical):**
* plain `simp` rewrites `<x,x>` to `||x||^2` via `inner_self_eq_norm_sq_to_K`
  *before* the sesquilinear expansion -- use `simp only` with an explicit list, or
  expand with `norm_sub_sq`;
* `exact_mod_cast` on `(r : C)^2 = (s : C)` needs
  `rw [inner_self_eq_norm_sq_to_K (K := C), <- Complex.ofReal_pow]` then
  `Complex.ofReal_inj.mp`;
* `inner_smul_left/right` need `simp only`, and `inner_conj_symm` needs its
  arguments given explicitly or the `K` metavariable blocks the rewrite;
* `innerSL_apply` is not a lemma name here; `beamResidualRankOne_apply` by `rfl`
  works instead.

If an Eckart--Young / rank-one approximation fact falls out generically, its owner
is `OperatorIdeals` (`ForTauCeti/Analysis/OperatorIdeal/`), not Section 9.

### T2 `TODO` -- Section 9 equation (9.8), Weinberger comparison

Row `DK-9.8`. Its recorded blocker (`alpha_3 > 500` missing; then
`free-beam-closed-operator`) is **stale**: `realSpectrum_beamOperator_subset_sharp`
and `beamFiniteDataCertificate` exist. Determine what is actually absent, connect
the compiled arrowhead/Weinberger algebra to the genuine beam spectral theorem, and
derive printed (9.8). Do not prove another root bound; do not instantiate a dead
`third_eigenvalue` field.

### T3 `TODO` -- Section 9 equations (9.5)--(9.7)

Row `DK-9.5-9.7`. Exact radical arithmetic already compiles; this is theorem
instantiation against `beamRitz_matrix` / `beamResidualGram_matrix` /
`beamOperator`, replacing certificate-field uses. Use the *correct* tan 2Theta
surface -- the branch-free one where applicable, not an obsolete selected-branch
wrapper.

### T4 `TODO` -- Section 9 equations (9.9)--(9.11), rank-one resolvent order

Row `DK-9.9-9.11`. Hardest remaining Section 9 mathematics. `Section9/SchurComplement.lean`
and `Section9/RankOneCorrection.lean` already carry (9.9) as a block map, (9.10)--(9.11)
as the Schur reduction, the shifted diagonal/off-diagonal rank-one correction, the
`sqrt 3 / 30` coefficient and the final radical combination. What is missing is the
**operator-order resolvent sandwich** and the identification with the actual individual
eigenvector/angle quantities. Do not manufacture another certificate record. If a
generic "resolvent order comparison under a positive rank-one perturbation" emerges,
its owner is `SelfAdjointSpectralTheory`.

### T5 `TODO` -- full `sin 2Theta` source scope

Row `S2-sin-two-theta`. Three distinct sub-problems; do not conflate.
* **A.** real + arbitrary dimension + every source UI norm. Should be a *transport*
  problem for the directed `Theta_0` half, via `complexifySubmoduleEquiv`,
  `approximationSingularValue_complexify`,
  `PaperUnitaryInvariantNorm.gauge_complexify`, `FormTransport`. Do **not** transport
  a scalar-specific `KyFanDominantIdealFamily`; instantiate the complex result at each
  Ky Fan level and finish with the `RCLike`-generic dominance machinery.
* **B.** Do **not** identify `Theta_0` with ambient `Theta`. The census warns that in
  the 2D one-angle model the directed block carries `sin 2theta` once while
  `sinTwoAngleOperatorC` carries it twice. Verify, with a compiled counterexample if
  useful, and certify the two conclusions separately.
* **C.** the unequal-dimension extension asserted in the last sentence of Section 8
  (`dim X(E_0) < dim X(F_0)`), which is proof debt for the **sin** theorem, not for
  Section 8. Reuse the lower-rank tangent / trial-map machinery of Theorem 6.3.

### T6 `TODO` -- real-scalar / Appendix cluster

Rows `S2-tan-theta`, `DK-6.1-lem`, `DK-6.1-prop`, `DK-6.3-thm`, `DK-6-appendix`.
Fresh whole-repo audit **before** proving anything: much is already done. Expect exact
real-scalar wrappers via `complexifySubmoduleEquiv` on `theorem63Compression` /
`theorem63Residual`, returning through
`PaperUnitaryInvariantNorm.mul_gauge_le_of_all_mul_kyFan_le` and `gauge_complexify`.
If mathematics is present and only the row is stale, fix the row.

### T7 `TODO` -- `tan 2Theta`: infinite-dimensional trial subspace, branch-free

Row `S2-tan-two-theta`, the one axis still open after `05bc5fc0`.
The branch-free chain reaches an arbitrary Hilbert space through the finite-carrier
compression `M = U + T''U`, which needs `[FiniteDimensional k U]` to reach the
intrinsic singular-system layer. The selected-branch endpoints remove that via the
Riccati/approximation-number route (`sharp_transformed_prefix`, uniform stable pairs).
The branch-free analogue needs `2 X |I - X*X|^-1` -- the **modulus** of `I - X*X`, not
`I - X*X` itself -- with invertibility from the quantitative form of
`singularValue_ne_one`. Do **not** recover it from the contractive Riccati API and do
**not** route it through Theorem 8.1.

### T8 `TODO` -- Section 9 infinite-residual example

Row `DK-9-infinite-residual-counterexample` (`compiled_specialization`). If the printed
example is genuinely an abstract operator example and the current theorem is only a
coordinate-sequence specialization, lift it with a short operator wrapper (diagonal /
unbounded realization in the canonical `SelfAdjointSpectralTheory` / `OperatorIdeals`
vocabulary). Do not overbuild.

### T9 `TODO` -- exactness / source-surface sweep

Only after the mathematics above. Rows `S1-block-residual`, `S1-ui-norms`,
`DK-3.1-thm`, `DK-3.2-prop`, `DK-6.3-thm` and any other still marked
`compiled_general_infrastructure` / `compiled_specialization` whose actual source
theorem is present at full scope. Search the whole repo, inspect elaborated
signatures, add a thin source-facing declaration only when necessary, otherwise
correct the census. Remove stale blockers when evidence supports it. Do not invent
mathematics to justify a stale label.

### T10 `TODO` -- final full-paper audit

Reread Sections 1--10 and build a fresh source checklist: every numbered/displayed
theorem, every construction treated as source content, sharpness/equality claims,
scope statements, unbounded appendices, the Section 9 numerical example, explicit
counterexamples, open questions. Check the census against that audit rather than
checking the census against itself. Then rerun every build and gate.

## Rows that are NOT proof debt (do not convert to fake `compiled_exact`)

* `DK-4.4-prop` -- `refuted_as_transcribed`
* `DK-10.1` -- `resolved_by_modern_development`; the remaining generality is the
  paper's own open question
* `DK-10.2` / `DK-10.3` / `DK-10.4` -- `not_a_completion_obligation`

## Completed in this campaign

### `05bc5fc0` -- the unrestricted, branch-free `tan 2Theta` theorem

Closed the branch axis and the scalar axis of `S2-tan-two-theta`. Endpoint
`TauCeti.DavisKahan1970.tanTwoTheta_branchFree_paperUINorm`: every
`PaperUnitaryInvariantNorm`, `[RCLike k]`, `[CompleteSpace E]`, no
`[FiniteDimensional k E]`, no branch hypothesis and no branch conclusion.
Route: cleared (7.6) (`paired_singularVector_gap_inequality`), `cos 2theta_j != 0`
from the gap (`singularValue_ne_one`), sign choice as a rephasing carried by the new
`sum_abs_le_rectangularKyFanSum_of_orthonormal`. Ky Fan root proved over an arbitrary
finite index set because `t -> 2t/|1-t^2|` is not monotone across the quarter turn.
Row remains `compiled_specialization` for the `[FiniteDimensional k U]` axis alone
(-> T7).

### `80e2940a` -- Section 9 (9.3) scaffolding

See T1.

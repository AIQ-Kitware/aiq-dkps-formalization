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

### T1 `DONE` -- Section 9 equation (9.3): second residual approximation number

Row `DK-9.1-9.4` (`partial_or_wrapper_missing` / `proved_conditional`).
(9.1), (9.2), (9.4) are already genuine operator theorems. Only (9.3) remains.

**Already proved and pushed** (`80e2940a`, in `BeamSection9.lean`):
`beamResidual`, `beamTrialVecOne/Two`, `beamTrialVec_orthonormal`,
`beamTrialVec_span_eq_top`, `exists_beamTrialVec_repr`, `beamResidual_gram`,
`beamGramTopCoefficient`, `beamGram_orthogonal_direction`.

**DONE.** `beamSinThetaSum_le : beamSinThetaSum eps <= residualKyFanTwo eps / 500`,
axiom-clean, in the default build. All four of (9.1)--(9.4) are now derived from
`beamOperator` with no certificate field in any statement, so row `DK-9.1-9.4` is
`compiled_exact` / `proved_in_build` with no blocker.

Chain: `beamResidualRankOne` (rank <= 1 via `range <= span {v}` + `rank_span_le`)
-> `beamResidual_sub_rankOne_apply` (the error is *exactly* `((c a - b)/(1+c^2))`
times the residual of `c phi_1 - phi_2`) -> `beamResidual_orthogonal_norm_sq`
-> `norm_beamResidual_sub_rankOne_le` (Cauchy--Schwarz; sharp Eckart--Young step)
-> `approximationSingularValue_one_beamResidual_le` -> `kyFanTwo_beamResidual_le`
-> `beamSinThetaSum_le` via `sinTheta_unbounded_gauge_of_spectrum_gap` at
`beamKyFanTwo`.

**Lean lesson worth keeping.** On a `Submodule`'s induced inner-product space,
`rw`/`simp` with `inner_smul_left`, `inner_smul_right` and
`inner_self_eq_norm_sq_to_K` silently fail to match, while `inner_add_left` /
`inner_add_right` succeed. Push the computation to the ambient space with
`Submodule.coe_inner` (FORWARD direction: submodule-inner = ambient-inner of the
coercions) and it all works. Plain `simp` is also wrong: it rewrites `<x,x>` to
`||x||^2` before the sesquilinear expansion. Radical identities of this shape are
for `linear_combination` with explicit coefficients, not `nlinarith`.

If an Eckart--Young / rank-one approximation fact falls out generically, its owner
is `OperatorIdeals` (`ForTauCeti/Analysis/OperatorIdeal/`), not Section 9.

### T2 `WIP` -- Section 9 (9.5)--(9.7): the perturbed spectral gap  **[RE-RANKED UP]**

Row `DK-9.5-9.7`. **The brief's claim that this is "theorem instantiation, not new
analysis" is WRONG, and it is now the gate on all three remaining Section 9 rows.**

The consuming endpoint exists and is strong enough:
`TauCeti.DavisKahan.Experimental.ExactTanTheta.theorem6_3_unbounded_ideal_directedTangent`
gives `delta * N.gauge tanTheta <= N.gauge D.residual` for every Fan-dominant
unitary-invariant ideal, tangent representative exhibited. Instantiating it at
`delta = 500 - ritzHigh eps`, `alpha = ritzHigh eps`, residual norm
`orthogonalResidualSingularValue eps = |eps| sqrt 15/15` reproduces
`tangentThetaExactBound eps` exactly.

Its blocking hypothesis is `specProjection hA (Ioo alpha (alpha+delta)) = 0`: a genuine
spectral gap **for the perturbed operator**. (9.1)/(9.2)/(9.4) never needed one -- they
are stated against a spectral *set*, so the restriction's spectrum is inside it by
construction and `beamHigh_spectrum_avoids` is free. A tangent bound cannot use that
trick: it needs both spectra separated.

The gap is true, by Rayleigh--Ritz: `beamPerturbation eps` is positive
(`0 <= eps t <= eps`), so eigenvalues only increase and the third stays above 500 by
`realSpectrum_beamOperator_subset_sharp`, while the two low ones are at most the Ritz
values. Formalizing it needs a min--max/Rayleigh--Ritz upper bound for the second
eigenvalue of an unbounded self-adjoint operator plus spectral monotonicity under a
positive bounded perturbation. **Owner: `SelfAdjointSpectralTheory`
(`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/`), not Section 9.**

**Part (a) is DONE** (`norm_beamRitzResidual_le`, `beamRitz_form_le`,
`beamResidual_inner_trial`; axiom-clean, default build). The residual norm was obtained
without computing the projection: `Submodule.starProjection_minimal` + `ciInf_le` against
the explicit competitor `ritzLow eps * a * phi_1 + ritzHigh eps * b * phi_2`, whose Gram
form collapses to `(eps^2/30)|a-b|^2`. The one non-ring input is `sqrt 3 ^ 2 = 3`, given
to `linear_combination` with coefficient `-(eps^2/36)(|a|^2+|b|^2)`.

**Part (b) is all that remains**, and it is the single fact gating every remaining
Section 9 row: assemble `UnboundedTrialBlock (beamPerturbed eps) beamTrial` from part
(a) (its `operator_apply`/`residual_apply` fields are the projection identities, with
`A.toLinearMap` on the trial reducing to `beamPerturbation eps` by
`beamOperator_apply_trial`), then prove

    specProjection (beamPerturbed eps) (Ioo (ritzHigh eps) 500) = 0.

**Proof plan, and why it is not short.** Write `P_c` for `specProjection (Iic c)` of
`beamPerturbed eps`. The statement is `rank P_500 <= 2` and `rank P_{ritzHigh} >= 2`,
since then `P_(Ioo alpha 500) = P_500 - P_alpha` has rank 0.

* `rank P_500 <= 2`: for `y` orthogonal to `beamTrial` in the domain,
  `re<(A + eps t)y, y> >= re<A y, y> >= 500.5 ||y||^2` (the perturbation is positive and
  `beamSpecProjection_lowSet_eq_singleton` collapses the low projection of `beamOperator`
  onto the kernel). A 3-dimensional subspace with form `<= 500` would meet
  `beamTrial^perp` nontrivially. Contradiction.
* `rank P_{ritzHigh} >= 2`: from `beamRitz_form_le`, but the naive argument only yields
  equality rather than a contradiction, so it needs the STRICT form: a vector whose
  spectral mass lies entirely in `(ritzHigh, inf)` cannot have mean exactly `ritzHigh`
  unless it is zero.

The two vector-local energy bounds this needs already exist:
`TauCeti.ApproximationNumber.le_re_inner_of_specProjection_Iic_apply_eq_zero` and
`re_inner_le_of_specProjection_Ici_apply_eq_zero`
(`ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/GramSpectralRank.lean`). What is
missing is the **rank/dimension counting** that converts a form bound on a
finite-dimensional subspace into a lower bound on the rank of a spectral projection of an
*unbounded* operator, plus monotonicity of that rank under a positive bounded
perturbation. `GramSpectralRank.lean` has exactly this pattern
(`natCast_succ_le_rank_gramProjection_Ici_of_lt_approximationNumber`,
`rank_gramProjection_Ioi_le_natCast_of_approximationNumber_lt`) but only for the Gram
operator of a bounded map; it is the template to generalize.

**Owner: `SelfAdjointSpectralTheory` (`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/`).**
This is a genuine new development, not a wrapper -- budget accordingly.

Original part (a) description, for reference:
build `UnboundedTrialBlock (beamPerturbed eps) beamTrial` with the Ritz compression
(`beamRitz_matrix` gives `hCompression` at `alpha = ritzHigh eps` immediately) and the
Rayleigh--Ritz residual `(1 - P_Z) . H|_Z`, whose Gram is
`orthogonalResidualGram eps = (eps^2/30) [[1,-1],[-1,1]]` and whose norm is exactly
`orthogonalResidualSingularValue eps` (for `x = a phi_1 + b phi_2`,
`||Rx||^2 = k|a-b|^2 <= 2k||x||^2`, `sqrt(2k) = |eps|/sqrt 15`). Needs the orthonormal
expansion `starProjection x = <phi_1,x> phi_1 + <phi_2,x> phi_2`, which follows from
`beamTrialVec_span_eq_top`.

### T3 `BLOCKED` -- Section 9 equation (9.8), Weinberger comparison

Row `DK-9.8`. `equation_9_8_lower` / `equation_9_8_upper` are proved but CONDITIONAL on
`tanPhi <= weinbergerLower/UpperTangentExactBound eps`.
`weinbergerUpperTangentExactBound` is *definitionally* `tangentThetaExactBound`, so the
upper line is downstream of T2 and inherits its blocker exactly. The lower line
additionally needs certified low roots of `weinbergerComparisonMatrix eps`, fed through
the already-proved `tangent_sq_le_of_weinberger_sine_sq`.

The recorded `alpha_3 > 500` blocker IS stale -- `realSpectrum_beamOperator_subset_sharp`
supplies it -- but the row is not mechanical. Do not attempt before T2.

### T4 `BLOCKED` -- Section 9 equations (9.9)--(9.11)

Row `DK-9.9-9.11`. The scalar geometry is complete: `SchurComplement.lean` has (9.9) as a
block map and (9.10)-(9.11) as the Schur reduction over arbitrary modules,
`RankOneCorrection.lean` has the `sqrt 3 / 30` coefficient, and
`combined_individual_coefficient` proves the Euclidean combination is exactly
`sqrt 7 / 10`. But `individual_angle_le_exact_envelope` is conditional on the same
tangent quantities T2 must supply, so this row is downstream of T2 as well.

Its own hard content is the operator-order resolvent sandwich identifying the Schur
reduction with the actual eigenvectors of `beamPerturbed eps`. If a generic resolvent
order comparison under a positive rank-one perturbation emerges, its owner is
`SelfAdjointSpectralTheory`. Do not manufacture another certificate record.

**Re-ranking note.** The brief ranked (9.9)-(9.11) as the hardest Section 9 item and
(9.5)-(9.7) as near-trivial. The dependency runs the other way: all three remaining
Section 9 rows are gated on the single perturbed-spectral-gap fact in T2.

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

### T6 `TODO` -- real-scalar / Appendix cluster  **[SCOPED, with a measured finding]**

Rows `S2-tan-theta`, `DK-6.1-lem`, `DK-6.1-prop`, `DK-6.3-thm`, `DK-6-appendix`.

The audit already in the census is CORRECT and was re-verified: the gap on these rows is
**real scalars at infinite dimension**, and it is genuine, not a stale label. Every
declaration on them is `InnerProductSpace ℂ` only; the one scalar-generic declaration on
`S2-tan-theta` (`partIII_tanTheta_ritzResidual_uiNorm`) carries `[FiniteDimensional]`.
`DK-6.3-thm` has `scope_gap: None` and no blocker -- its residue is
`S2-unbounded-scope`'s, not its own. `DK-6-appendix` is half closed already: the SINE
portion has real endpoints (`Theorem6_1_real_commonDomain` etc.), only the tangent
cutoff / Fan passage is still complex-only.

**MEASURED FINDING 2026-08-07 (Opus 5).** The complexification transport the campaign
brief recommends is probably the wrong route for `DK-6.1-lem`/`DK-6.1-prop`. Lemma 6.1
is complex-only *by habit, not by mathematics*: all three of its imports
(`OperatorIdeal/ApproximationNumbers/BlockSum`,
`SineTheta/Norms/SubspaceSingularTransport`, `SineTheta/ProjectionBlocks`) are already
`{𝕜 : Type u} [RCLike 𝕜]`-generic, and its own content -- `paperProjectionBlock`,
`paperBlockCompression`, Ky Fan gauges, `PaperUnitaryInvariantNorm.extendedGauge` -- is
projection algebra with nothing complex-specific in it.

A direct `ℂ → RCLike 𝕜` generalization of
`DavisKahan/Sources/DavisKahan1970/SineTheta/Lemma61.lean` was ATTEMPTED and REVERTED.
It got most of the way: only three failure sites, none of them mathematical.

1. `Lemma61.lean:158` -- `(deterministic) timeout at whnf`, 200000 heartbeats. This is
   the instance-diamond trap the file's own docstring warns about; the file installs
   `local instance instCompleteSpaceCoeOfHasOrthogonalProjectionLemma61` precisely
   because of it, and that instance has to be generalized in step with the variable
   block or elaboration falls back on unfolding `Submodule` algebra structures.
2/3. `Lemma61.lean:317` and `:327` -- a rewrite with the
   `kyFanApproximationGauge _ (continuousOrthogonalBlockSum _ _)` lemma stops matching,
   almost certainly an instance/implicit-`𝕜` mismatch needing an explicit `(𝕜 := 𝕜)`.

So the next attempt should generalize the local instance first, supply `(𝕜 := 𝕜)` at the
two block-sum rewrites, and raise `maxHeartbeats` locally if the timeout survives. If
that lands, `DK-6.1-lem` and `DK-6.1-prop` close **without any complexification
transport at all**, which is strictly better than the brief's route. Do the same
genericity check on the appendix tangent passage before reaching for
`complexifySubmoduleEquiv`.

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

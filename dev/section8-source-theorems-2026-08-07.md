# Section 8 from the printed hypotheses — what landed, what did not

Author: Claude Opus 5, 2026-08-07.  Base: `91d91305`.

## The bug this campaign started from

`dev/davis-kahan-1970-full-source-census.json` called **DK-8.1-thm** and
**DK-8.2-thm** `compiled_exact` with `next_action: "Nothing outstanding."`
while the production file they point at,
`DavisKahan/Sources/DavisKahan1970/Section8/SourceSurface.lean`, said in its own
module docstring that neither full theorem was promoted.

The source file was right.  `theorem8_1_selectedBranch_and_spectralRepulsion`
is an `alias` for `theorem81CoreConclusion`, whose hypotheses include a
`SpectralContinuationWitness`, a contour-smallness constant `hsmall`, and the
spectral orientation `h0`/`h1` — all of which the paper *proves*.
`theorem8_2_perturbationHalfGap_selectedBranch` requires a
`PerturbationHalfGapBridge`, whose field `contour_selects_quarter_branch` is
the conclusion.

**A declaration compiling says nothing about whether its hypotheses are the
printed ones.**  That is the lesson worth carrying forward.

## What is now proved

### Promotion out of the donor lane

`isQuarterAcute_of_paper_form_gap_infinite` and
`paperFaithful_tanTwoTheta_uiNorm` — the dimension-free branch selection and
the unrestricted bounded UI-norm `tan 2Theta` theorem — lived in the
non-default `FinishTanTwoTheta` lane.  They now live in
`DavisKahan/InfiniteDimensional/TanTwoTheta/` and are covered by `lake build`.
Nothing was restated; only the namespace changed, and the lane keeps its old
names as aliases.  (The lane's own `PROOF_OBLIGATIONS.md` records that this
exact failure mode — proved but unguarded, broken by an unrelated refactor —
already happened once, on 2026-07-30.)

### Full spectral repulsion

`TauCeti.DavisKahan.realSpectrum_add_offDiagonal_subset_exterior_of_form_gap`

The bounded development had only *eigenvalue* repulsion.  In an arbitrary
Hilbert space that is strictly weaker than the source claim, because the
spectrum need not be a point spectrum.  The proof here is dimension-free
J-coercivity: reflection through the source subspace makes the centred operator
coercive by `min (lam - a) (b - lam)`, a fully off-diagonal self-adjoint `H`
becomes skew-adjoint after reflection and so contributes nothing to the real
part, and the reflection is its own inverse.

### Sharp form bounds on a spectral subspace with a gap

`DavisKahan/SpectralTheory/SpectralGapFormBounds.lean`

`re_inner_le_of_mem_boundedSelfAdjointSpectralSubspace_Iic` and its complement
companion.  **Sharpness is the point.**  The pre-existing band estimate
`norm_comp_boundedPVM_proj_sub_smul_le` loses a factor of two, which is fatal:
these bounds feed straight into the ordered-gap hypotheses of the quarter-angle
theorem, and a lossy bound would not close the gap at all.

The proof exists because of the gap itself: on the spectrum the indicator of
`Iic alpha` *is* continuous, so `boundedSelfAdjointSpectralProjection_Iic_eq_cfcHom`
identifies the spectral projection with a *continuous* functional calculus, and
`(alpha - t) chi(t) >= 0` holds pointwise on the spectrum.

### Theorem 8.1

`DavisKahan/Sources/DavisKahan1970/Section8/SourceTheorem81.lean`

* `theorem8_1_canonicalBranch` — existence.  Hypotheses: `A` self-adjoint,
  `P` reduces `A`, the `P` block below `alpha`, the `Pᗮ` block above
  `alpha + delta`, `H` self-adjoint and fully off-diagonal.  Nothing else.
  Conclusions: full spectral repulsion, the canonical branch `Q` as a genuine
  spectral subspace, both sharp form bounds, both restricted-spectrum
  containments, and `IsQuarterAcute P Q` — *strictly* inside the quarter turn,
  which is stronger than the printed closed `Theta <= pi/4`.
* `theorem8_1_eq_canonicalBranch_of_maximalAngle_le` — uniqueness.  Any
  reducing subspace of `A + H` satisfying the printed **closed** condition
  equals `Q`.
* `theorem8_1_maximalAngle_le_iff_spectrumIn` — the printed characterization,
  both directions.
* `theorem8_1_upperCompressionRepulsion_canonicalBranch` and its lower
  companion (in `DavisKahan/Frontier/Section8.lean`) — part (i), instantiated
  at the canonical branch, so no data record appears in the hypotheses.

Uniqueness is the paper's argument.  A reducing projection commutes with
`A + H`, hence with the branch projection — `Commute.cfcHom` applies precisely
because the gap made that projection a continuous calculus.  So a vector of `M`
outside `Q` projects into `M ∩ Qᗮ`, where the strict quarter-angle bound for
`Q` and the closed one for `M` contradict each other.

Supporting: `realSpectrum_subset_Iic_of_re_inner_le` and its `Ici` companion,
the converse of the existing spectral-order bridge, proved by coercivity rather
than by functional calculus (which avoids needing an `ℝ`-CFC instance on the
operator algebra of a subspace).

### Corollary 3.1

`corollary3_1_compact_defectBlock_angleList_classification`

The compiled corollary assumed `P Q P` compact; the paper assumes the defect
block `P (I - Q) P` compact.  These are **incomparable** in infinite dimension:
`P(I-Q)P` compact says the principal angles accumulate only at `0`, `PQP`
compact says they accumulate only at `pi/2`, and neither implies the other
unless `P` is itself compact.

The repair is exact because `P (I - Q) P = P P_{Vᗮ} P`: the defect block of
`(U, V)` *is* the cosine block of `(U, Vᗮ)`.  Two elementary new lemmas —
complementing the second subspace preserves pair-equivalence, and merely
permutes the four elementary Halmos summands — reduce the printed statement to
the compiled one at `(U, Vᗮ)`.  The classifying list is correspondingly
`sin^2 theta_j`; since `theta ↦ sin^2 theta` is strictly monotone on
`[0, pi/2]`, equality of these lists is equivalent to equality of the printed
angle lists, so this is exact and not a reparametrised weakening.

## What did NOT land, with the recipe

### Theorem 8.1 parts (ii) and (iii)

(ii) ordered eigenvalue inequalities — should follow from the two compression
inequalities above via `LinearMap.IsSymmetric.eigenvalue_mono`
(`ForTauCeti/Analysis/InnerProductSpace/CourantFischer.lean`).

(iii) the printed inequality is for **every symmetric gauge**.  Route it
through the existing FiniteSymmetricGauge / majorization / Ky Fan layer.
Replacing it with the operator norm would be a weakening, not a proof.

### Theorem 8.2 — both alternatives

The census row `DK-8.2-thm` carries the full recipe verified against the
available infrastructure.  In outline:

* path `B(t) = A + H - t H` on `[0,1]`, `t = 0` perturbed, `t = 1` unperturbed;
* fixed circle centred at `(alpha+beta)/2` of radius `(alpha-beta+delta)/2`,
  real intersections `beta - delta/2` and `alpha + delta/2`;
* contour invertibility for every `t` by **Neumann perturbation of the initial
  resolvent** — base distance `>= delta/2` gives resolvent norm `<= 2/delta`,
  and `||tH|| <= ||H|| < delta/2`.  This is what replaces the non-source global
  projection-Lipschitz hypothesis `hquant`;
* `circleRieszProjection_eq_boundedSelfAdjointSpectralProjection` identifies
  `Q(t)`, `continuous_circleRieszProjection_path` makes
  `f(t) = subspaceGap (Q t) (Q 0)` continuous;
* no crossing of `sqrt 2 / 2` from `sinTwoTheta_spectrum_operator`: at a
  crossing, `delta <= d * ||sin 2Theta|| <= 2 t ||H|| < delta`.

**The one genuinely missing lemma** is
`||sinTwoAngleOperatorC U V|| = 1` when `subspaceGap U V = sqrt 2 / 2`.  The
graph-coordinate route is `gap = ||X|| / sqrt(1 + ||X||^2)`, so the quarter gap
is exactly `||X|| = 1`.

The residual alternative then needs Krein's self-adjoint contractive
completion, `exists_selfAdjoint_completion_eq_norm_restriction`, via the Julia
operator `L J_A L*` with `Gamma` obtained from the existing
`ContinuousLinearMap.exists_contraction_of_gram_eq`
(`ForTauCeti/Analysis/InnerProductSpace/Polar/GramContraction.lean`) applied to
`D = sqrt(I - A^2)` and the column `(B, sqrt(D^2 - B*B))`.  After that,
`A' := A + H - H'` leaves `A + H`, its spectral subspaces and the residual
unchanged while making `||H'|| = ||R||`, reducing the residual alternative to
the perturbation one.

`PerturbationHalfGapBridge` and `ResidualHalfGapBridge` may survive as internal
conveniences.  They must **not** appear in the source-facing statement.

### Section 9

Unchanged by this campaign; see
`dev/section9-free-beam-campaign-2026-08-07.md`.  Four rows remain:
(9.3), (9.5)--(9.7), (9.8), (9.9)--(9.11).

## Gates at the end of this campaign

* `lake build FinishTanTwoTheta` — 8941 jobs, green.
* `lake build` — 9465 jobs, green.
* census — CLEAN 48/48; declaration probe 200/200.
* `check_library_structure.py` — rule 3 reports 16 violations, **unchanged from
  the baseline**.  It is the standing worklist of `Experimental/` modules that
  no longer carry an admission and ought to move out; nothing in this campaign
  added to it.

Every new capstone is axiom-clean: `[propext, Classical.choice, Quot.sound]`.

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

**Superseded 2026-08-07 by the printed proof.**  The recipe first recorded here
— fixed circle, contour invertibility by Neumann perturbation of the initial
resolvent, and a missing `||sinTwoAngleOperatorC U V|| = 1` lemma at the quarter
gap — was a *reconstruction* made without the source.  With the transcription in
hand it is clear that it is strictly harder than what Davis and Kahan do, and
that the "one genuinely missing lemma" is not needed at all.  Recorded here
because a plausible reconstruction that survives an infrastructure check still
is not the source argument.

Two things the reconstruction also got wrong:

* the printed hypotheses include **`spectrum(A_0) ⊆ [beta - delta/2, alpha +
  delta/2]`** in addition to `||H||_1 < delta/2` or `||R||_1 < delta/2`.  That
  is what makes `[beta - delta/2, alpha + delta/2]` the right interval for the
  projector along the path;
* `||.||_1` is the **bound (operator) norm** throughout, not a general
  unitarily-invariant norm.

The printed proof is a connectedness bootstrap:

1. `gamma := ||H||_1 < delta/2`, and `A(s) := A + H - s H` for `s ∈ [0,1]`, so
   `A(0) = A + H` and `A(1) = A` — the path runs *from* the perturbed operator,
   the opposite orientation to the reconstruction;
2. `spectrum(A(0))` misses `(beta - delta, beta)` and `(alpha, alpha + delta)`,
   so a bound-norm-`gamma` perturbation leaves `A(s)` missing
   `(beta - delta + gamma, beta - gamma)` and `(alpha + gamma, alpha + delta -
   gamma)`, both nonempty since `gamma < delta/2`;
3. `Q(s)` := spectral projector of `A(s)` for `[beta - delta/2, alpha +
   delta/2]`, norm-continuous, so `theta(s) := arcsin ||Q(s) - Q(0)||_1` is
   continuous with `theta(0) = 0`;
4. `beta <= A_0 <= alpha` gives `P = P Q(1)`, hence `theta(1) >= Theta`;
5. call `s` *close* when `theta(s) <= pi/4`.  For close `s`, the sin2theta
   theorem applied to `Q(s)` against `Q(0)` gives
   `theta(s) <= (1/2) arcsin(2 s gamma/delta) <= (pi/2)(s gamma/delta) <
   (pi/2)(gamma/delta) < pi/4`, the middle step by concavity of `arcsin`.

The bound in (5) is **strict and uniform in `s`**, so the close set is open;
continuity of `theta` makes it closed; `0` is close; `[0,1]` is connected.  So
every `s` is close and `theta(1) < pi/4`.

That needs no new geometry lemma — only norm-continuity of the spectral
projector along the path, the existing sin2theta theorem, and concavity of
`arcsin`.

The residual alternative is unchanged: without altering `A_1 + H_1`, `R` or the
`Lambda_j` one may change `H_1`, and a theorem of Krein supplies a choice with
`||H||_1 = ||R||_1`, reducing it to the perturbation case.  In Lean that is
`exists_selfAdjoint_completion_eq_norm_restriction` via the Julia operator
`L J_A L*` with `Gamma` from the existing
`ContinuousLinearMap.exists_contraction_of_gram_eq`
(`ForTauCeti/Analysis/InnerProductSpace/Polar/GramContraction.lean`).

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

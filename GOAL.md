# Outstanding work

This file contains only live work. Completed campaigns belong in Git history, and
paper-completion status belongs in the maintained source censuses and result
inventories. Read `AGENTS.md` before starting work.

Submission packaging and Challenge maintenance are intentionally **not** tracked here. The standalone
submission repositories under `submodules/` own their Challenge/Solution files,
metadata, submission checks, and submission-specific planning. This repository is
the source of truth for the mathematics: if submission preparation exposes a
mathematical, proof, or public-API defect, fix and validate it here first, then
refresh the standalone repository mechanically.

---

## Acharyya 2025

- **`A25-T1`** — **done 2026-09-05.**
  `GrowingResponse.prob_cmdsEntrywiseClose_ge_of_secondMoment` is the corrected finite bound
  as one declaration: the paper's own Chebyshev-plus-union probability
  `1 - n σ²/η²`, delivering entrywise closeness of the classical-MDS matrices at
  `cmdsEntrywiseRate n m (responseDistBound m (B + η)) η`. The dissimilarity bound the
  printed theorem omits is carried by `B`, a bound on the *population* response norms only;
  the sample responses are controlled on the event itself. The printed form stays refuted by
  `Theorem1Scale.prob_entrywiseClose_lt_paper_bound`.
- **`A25-C1`** — **done 2026-09-05.**
  `PaperRate.highProb_operatorNormClose_paperDeltaScale` states the corollary at the literal
  source scale: with high probability the two classical-MDS matrices are operator-norm close
  at `paperOperatorScale m R ((n³/r)^(1/2−δ))`, which is `16 R/m` times the printed scale and
  independent of `n`, with the paper's own constant `16` in it. It carries the dissimilarity
  bound `R` that Theorem 1 needs and the printed corollary omits, so the row moved from
  `compiled_by_composition` to `compiled_source_repair`.
- **`A25-P1`** — **done, 2026-09-05.** The printed compact-Riemannian condition does not
  force the nondegeneracy the argument needs, and no condition on the ambient space can:
  a constant placement satisfies every such condition and has population matrix `0`.
  The repair replaces it by `SpreadPlacement`, an explicit condition on the *placement*
  asking that `d` of the recentred model positions be mutually orthogonal with squared
  norm at least `α`. `proposition1_repair_of_spreadPlacement` derives Assumption 1's
  vanishing eigenvalue tail beyond index `d` and both bounds of Assumption 2 from it.
  It is registered as a repair, not as the printed proposition. The missing mathematical
  ingredient was the classical-MDS identity `classicalMDSMatrix_dist_eq_inner_centered`
  — the doubly centred squared-distance matrix of a Euclidean placement is the Gram
  matrix of its recentred points — which the tree did not have.
- **`A25-PA1`-`PA6`, `L1`-`L5`** — optional source-fidelity wrappers, role-replaced by
  cleaner perturbation machinery. Lowest priority; add them only when they improve
  the paper-facing API for a reader.

---

## Helm 2025

- **`H25-EQ2`** — **done 2026-09-05.**
  `AcharyyaBridge.highProb_entrywiseClose_responseDist_of_tendsto` states the displayed limit
  in the in-probability sense this development uses: uniform response-mean convergence in
  probability gives, for every tolerance, entrywise closeness of the sample and population
  dissimilarity matrices at every late enough stage. The finite step was already compiled at
  rate `2η/m`; what this adds is that the rate vanishes.
- **`H25-BRIDGE`** — fiber `Acharyya2024.rawStress_mds_stability` over the latent
  sample to discharge the bridge's distance-convergence hypothesis. If it works, the
  Helm bridge weakens accordingly. **Not the `_set` form**, which this file named until
  2026-09-05: that one concludes an existential over the minimizer set, which is not the
  shape of the bridge's `hdist`. The right one carries `huniq : RawStress.UniquePairProfile`.
  Note also that the bridge's conclusion is qualitative in a second way the Helm census
  used to leave out: the estimator it delivers is `TauCeti.alignedConfig` applied to the
  **true latents**, so the alignment lives inside the estimator and the isometry
  quantified outside the probability is the identity. Acharyya 2024's
  `not_exists_deterministic_rigidMotion_of_pairDist_exact` machine-checks that the
  outside-the-probability shape is not available; transferring it to Helm's setting is a
  restatement, not an application, and is the other half of this item.

**Preserve** the uniform-integrability / dominated-loss repair and the evidence that
convergence in probability alone does not give expected-risk convergence.

---

## Quench 2026

- **`Q26-T2A` / `T2B` / `RAW-FIN` / `RAW-INF` — remove the finite perspective net on
  the compact-infinite route.** The finite route already runs at the source rate; the
  infinite route carries an extra finite perspective net, and Acharyya 2024 now has a
  continuum/population-law route that may replace it. Do not force this past a real
  compactness or measurability obstruction; if it fails, name the precise missing
  theorem.
- **`Q26-T1`** — inherited embedding concentration. Either generalize the rate theorem
  to a growing sample with an augmented target, or keep the divergence explicit.
  Check first whether the strengthened Acharyya 2024 machinery closes it.

**Preserve** the tie-averaged nearest-neighbour estimator, the correction of the false
all-compact-subsets assumption, and the adjudicated `1/m` normalization with its two
invariance theorems.

---

## Yu--Wang--Samworth 2015

The source census is complete; do not open a broad YWS proof campaign.

- **Current-state API/source review — done 2026-09-05.** It found no wrong mathematics and
  six ledger defects, all repaired: the equation (1) row cited a Theorem 2 index-block
  specialization as its compiled witness; the three Theorem 3 rows and one Theorem 2 row
  pinned narrower or frame-producing forms rather than the source-shaped ones; the whole
  `Rectangular/SourceTheorem3.lean` surface was invisible to every ledger while the
  standalone submission repository already cited it; the grounding contract guarded only
  one of the three machine-checked refutations; the stated reason equation (1) has no
  wrapper was wrong; and eight sentences across the module headers, `README.md`,
  `GROUNDING.md`, `ELEGANCE_AUDIT.md`, `CitationSurface.lean` and the distilled source
  were stale.
- **`YWS-T1-eq1` — done 2026-09-05.** Equation (1) was the one displayed result of this
  paper with no literal wrapper. `yuWangSamworth_equation1_opNorm_le` is now that wrapper:
  a population unit eigenvector at `λ_j`, a sample eigenvector at `λ̂_j`, the mixed
  exterior separation, constant 1, operator norm. `equation1_gap_of_interval_position`
  supplies its `δ` from the printed two-neighbour minimum. It is registered
  `compiled_corrected`, for two hypotheses the printed display omits: the sample side is
  given as an orthonormal eigenbasis, because Theorem 1's separation constrains the
  spectrum on `span{v̂_j}ᗮ` and one eigenvector does not determine that; and the
  interval-position condition `λ̂_{j+1} ≤ λ_j ≤ λ̂_{j−1}` is stated explicitly. **The
  obstruction this file used to name was not real.** It is not simplicity of `λ̂_j`: a
  repeated `λ̂_j` equals a neighbour, so `|λ̂_j − λ_j|` is already one of the two printed
  terms.

- **Rectangular rank-one, printed hypothesis — done 2026-09-05.** The four rank-one
  singular-vector corollaries all took `CorrespondingRightSingularBlock` /
  `CorrespondingLeftSingularBlock`, which pin both singular vectors to Mathlib's chosen
  Gram eigenbases, and the census called that `compiled_generalized`. The symmetric side
  had been repaired on 2026-08-13; the rectangular side had not.
  `yuWangSamworth_{right,left}SingularVector_frame_le` and their
  `_opNormCoefficient_` siblings carry the printed hypothesis instead — an arbitrary
  orthonormal pair at the same sorted Gram index, separated from the rest of the
  population Gram spectrum, with no condition on the sample spectrum — at the same
  coefficient.

**Preserve** the corrected Equation (4), which is false as printed, and the corrected
rank-boundary convention.

---

## Davis--Kahan 1970

- **`DK-S8-UNBOUNDED`** — lift Section 8 to unbounded ambient scope. Every registered
  Section 8 declaration takes bounded `A H : E →L[𝕜] E`, while Theorem 8.1 opens
  "Assume the hypotheses of the tan 2θ theorem" and Theorem 8.2 "Add to the hypotheses
  of the sin 2θ theorem" — hypotheses this repository certifies at unbounded scope. The
  rows now disclose that, with the source evidence for reading Section 8 at the paper's
  main bounded setting and the competing reading stated in full
  (`nonlocal_source_interpretation.operator_scope_reading`). **The lift would make the
  reading moot, which is why it is worth doing.**

  **Scoped 2026-09-05. Both halves are blocked, on two different missing
  foundations, and 8.1's is much the smaller.** Nothing under `Section8/` mentions
  `→ₗ.[𝕜]` or an unbounded spectral subspace today.

  **8.1's statement is writable now and its consumer is already waiting.**
  `Section7IdealBounds.section7_tanTwoTheta_ideal` is the unbounded Section 7 tangent
  theorem and it takes `hquarter : IsQuarterAcute (selfAdjointSpectralSubspace A hA B hB)
  (selfAdjointSpectralSubspace (addBounded A E) (addBounded_isSelfAdjoint A hA E hE) S hS)`
  as a *hypothesis*. Discharging that under the printed spectral orientation is exactly
  what Theorem 8.1 does, and `Theorem81.lean` already proves
  `maximalAngle U V < π/4 ↔ IsQuarterAcute U V`. So the target signature is fixed by an
  existing unbounded consumer rather than invented. Every foundation it needs exists:
  `TauCeti.LinearPMap.specRange` / `selfAdjointSpectralSubspace` is the unbounded
  `canonicalLowBranch`, with `reducesSubspace_specRange`, `specRange_compl`,
  `specRestrict` and `isSelfAdjoint_specRestrict`; `addBounded_isSelfAdjoint` gives
  `A + H` self-adjoint; and
  `ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralFormBounds.lean` is the
  spectrum-to-form bridge the `iff` needs in both directions
  (`le_re_inner_of_specProjection_Iio_eq_zero`,
  `re_inner_le_of_specProjection_Ioi_eq_zero`).
  `theorem8_1_canonicalBranch` takes only form bounds on `P` and `Pᗮ` plus oddness of
  `H`, all of which restrict to `x : A.domain` in the vocabulary `SectionTwoUsage.lean`
  already uses.

  **What blocks 8.1 is its proof, not its statement, and the wall is one step.**
  Two of the four ingredients lift and two do not. The branch and its form bounds lift:
  `boundedSelfAdjointSpectralSubspace_reduces` becomes `reducesSubspace_specRange`, and
  `re_inner_le_of_mem_boundedSelfAdjointSpectralSubspace_Iic` and its dual become the
  `SpectralFormBounds` pair above. The other two are stated for `A H : E →L[ℂ] E`:
  `realSpectrum_add_offDiagonal_subset_exterior_of_form_gap`
  (`InfiniteDimensional/TanTwoTheta/OffDiagonalSpectralRepulsion.lean`) and, the real
  obstruction, `isQuarterAcute_of_orderedFormGap`
  (`InfiniteDimensional/TanTwoTheta/QuarterAcuteFormGap.lean`). That one reaches
  `IsQuarterAcute` from coercivity of the bounded composites `J ∘L (A − c)` and
  `K ∘L (A + H − c)`, and `ForTauCeti/Analysis/InnerProductSpace/CoerciveUnit.lean` is
  `E →L[𝕜] E` throughout. **The precise missing theorem for 8.1 is therefore
  invertibility of a coercive unbounded operator of the form `J(A − c)` on `dom A`, with
  `A` self-adjoint and `J` a reflection** — a Lax--Milgram-shaped statement, and a
  bounded, well-understood piece of analysis. Prove that first; everything else in 8.1
  is restating hypotheses over `dom A`.

  **8.2's homotopy is bounded-specific in its Lean form — this is the answer to the
  question this entry used to ask.** `Section8/Smallness.lean` reduces both printed
  alternatives to `selectedBranchProjectionLipschitzConstant C.contour V C.margin <
  √2/2` for a `SpectralContinuationWitness A V s`, and
  `Theorem82Branch.theorem8_2_perturbationHalfGap_complex` runs the path `A0 + t•E`
  through it. That whole stack under `DavisKahan/InfiniteDimensional/SinTheta/Continuation/`
  is stated for `A V : H →L[ℂ] H`: `operatorPath A V t = A + t•V`, `SpectralSeparatingContour`,
  and contour/Riesz-projection estimates. The mathematics does carry over — a bounded
  perturbation of a self-adjoint operator is self-adjoint on the same domain, and the
  resolvent bound `‖(z − T)⁻¹‖ ≤ 1/dist(z, σ(T))` holds unbounded — but the Lean
  foundation does not exist: **the precise missing theorems are contour-integral Riesz
  projections and resolvent norm bounds for `LinearPMap`**, which neither Mathlib nor
  this repository has. `DavisKahan.SpectralTheory.CircleRieszProjection` is bounded.
  That is a strictly larger gap than 8.1's: an unbounded coercive inverse is a standard
  argument, an unbounded holomorphic functional calculus along a homotopy is not.

  Parts (ii) and (iii) stay as printed — the source restricts them to finite dimensions
  itself. Keep the bounded theorems as specializations.

- **`DK-HR-NAMING`** — **closed 2026-09-05**, except one sub-item declined with a recorded
  reason. `SineTheta/Presentation.lean` and `Section2TanThetaPerturbation.lean` declare into
  `TauCeti.DavisKahan1970`; the six case twins are gone; sixty-one source-facing declarations
  use the lowercase `theoremN_M_*` form; the six registered witnesses outside the paper
  namespace are reachable under it; `UnboundedTrialBlock` is `BoundedCompressionTrialBlock`;
  the six unqualified clause aliases are deprecated in favour of the `_directed_`/`_ambient_`
  names and the `SectionTwo.lean` docstring is a table rather than a diary; and eleven
  proof-structure entries left the two double-angle rows. F6.7 -- deleting
  `proposition4_2_compact_nonacute` for its unused `_J` binder -- is declined on `DK-4.2-prop`,
  because that binder is the Section 4 setup the row's own accepted reading says the
  proposition is printed under.

- **`DK-HR-TANGENT-POLE`** — **closed 2026-09-05.** No registered tangent endpoint concludes
  on a totalised functional calculus without a conjunct in the same type excluding the pole.
  The directed clause's canonical witnesses derive their exclusion; the eight ambient `tan Θ`
  endpoints stated under (3.5) conclude `HasDefinedAmbientTangent`; and both ambient `tan 2Θ`
  endpoints conclude `∀ t ∈ spectrum ℝ (angleOperator…), Real.cos (2 * t) ≠ 0`. The real side
  needed one new lemma, `cos_two_ne_zero_of_isUnit_diagonalPart_reflection_sq_real`, proved by
  complexification through `spectrum_complexify`.

---

## Cross-paper coherence

Do one pass after the per-paper work for places where a stronger theorem landed without
all consumers moving:

- Does Acharyya 2025 consume the strongest YWS population-gap theorem, or an older
  specialization?
- Are obsolete eigengap or perturbation assumptions still sitting on source-facing
  capstones after the YWS integration?
- Does Quench consume the strongest current Acharyya 2024 result rather than a
  fixed-sample specialization?
- Can Helm consume the improved Acharyya raw-stress bridge?
- Did any duplicate temporary theorem surface survive a stronger theorem landing?
- Are source-facing names and docstrings still accurate after the `ClosedOperator` to
  `LinearPMap` and continuum-probability migrations?

Do not over-abstract across papers merely because implementations look similar.
Paper-facing wrappers earn their place through source correspondence.

---

## Known non-blocking gate debt

Treat the current checker output as authoritative; do not copy mutable counts into this
file.

- `check_comparator_signatures` is **green, 2026-09-05**: 45 of 45 comparisons match across
  every config, three of them `SKIP` because the config declares them absent from the
  Leaderboard. It had been red with 8 differing on Davis--Kahan alone. Five causes, none a
  wrong theorem: the pre-flight ignored the config's own
  `expected_missing_solution_theorems`; a `local instance` name leaks into the elaborated
  type and 43 module-local copies of the complete-subspace instance made it unmatchable from
  a challenge module; `variable {𝕜 E : Type*}` puts `[RCLike 𝕜]` in a different telescope
  slot than two separate `variable` lines; two Conformance statements had not followed a
  library change; and `Set.restrict` became `Set.domRestrict` upstream on the library side
  only. **Never write a new module-local `CompleteSpace` instance** — use
  `TauCeti.CompleteSubspace.instCompleteSpaceCoeOfHasOrthogonalProjection`. Run
  `python3 scripts/check_comparator_signatures.py --no-build` after any rename, any
  `variable`-block edit, and any library signature change; without `--no-build` it re-runs a
  full build per invocation.

- the `per-declaration-expose` ratchet in `dev/policy/ratchet.yaml` tracks upstream
  API-design debt. Do not lower its maximum to
  make it green.
- **Suite state 2026-09-05: 29 passed, 3 failed, 0 unavailable, 0 skipped.** The three are
  the ones below. `check_comparator_signatures` moved out of this list that day.
- `check_tauceti_readiness` and `check_tauceti_roadmap_topics` include upstream-review
  and roadmap-placement state. Both currently report the same four unplaced modules,
  `ForTauCeti.Probability.{AverageError, ProductConvergence, RigidAlignment, VStatistic}`,
  plus six under `ForTauCeti.MeasureTheory`. Placing them is a roadmap edit, and the
  roadmap is read-only without an explicit request. An unavailable optional checkout is not a pass, and an
  upstream review backlog is not a reason to invent local placement work.
- If the roadmap checker still reports the `ApproximationNumber.GramSquare` to
  `ApproximationNumber.GramSpectralRank` forward-reference problem, treat that as a
  real ordering/design issue. Re-check the live roadmap before acting on this note.

---

## Presentation

Only after higher-value mathematical/source-facing work:

- `leanq` HTML dependency visualization. Preserve its package-first compound layout,
  summarized Mathlib boundary, hidden Mathlib-internal edges by default, and explicit
  initialization behavior.
- `doc-gen4` improvements are optional documentation infrastructure, not a substitute
  for source-facing theorem work.

---

## Standing rules

Do not weaken a theorem, hide a hypothesis inside a definition, or substitute an
implementation-specific surrogate for a recognizable mathematical notion to make a
checker or census green. Do not convert a documented source repair back into a claimed
exact theorem. Do not delete a counterexample that shows a printed statement false.

No `sorry` in production mathematics and no custom axioms. Prefer ordinary kernel-
checked proof routes over mechanisms that introduce extra proof axioms when an ordinary
proof is available.

Do not add a new `scripts/check_*.py` without a concrete invariant that is not already
enforced elsewhere.

Report status in terms of the mathematics. A green build certifies compilation and
declaration resolution, never source fidelity; the censuses and semantic reviews are
the authorities for source correspondence.

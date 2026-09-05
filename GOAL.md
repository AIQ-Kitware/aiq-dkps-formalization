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
- **`H25-BRIDGE`** — fiber `Acharyya2024.rawStress_mds_stability_set` over the latent
  sample to discharge the bridge's distance-convergence hypothesis. If it works, the
  Helm bridge weakens accordingly.

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
- **`YWS-T1-eq1`** — optional literal indexed Equation (1) wrapper. **The obstruction is not
  what this file said.** It is not simplicity of `λ̂_j`: a repeated `λ̂_j` equals `λ̂_{j−1}`
  or `λ̂_{j+1}`, so `|λ̂_j − λ_j|` is already one of the two terms in the printed minimum.
  The real side condition is the interval-position one, `λ̂_{j+1} ≤ λ_j ≤ λ̂_{j−1}`, under
  which the printed two-neighbour minimum is exactly the exterior separation and the
  wrapper is a direct instantiation of `yuWangSamworth_theorem1_opNorm_le`. If added,
  state that condition explicitly and classify the wrapper `compiled_corrected`; it is an
  added hypothesis the printed display omits.

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
  reading moot, which is why it is worth doing.** Targets:
  `theorem8_1_maximalAngle_le_iff_spectrumIn`, `theorem8_1_canonicalBranch`, part (i)
  (`theorem8_1_{upper,lower}CompressionRepulsion`), and
  `theorem8_2_branch_maximalAngle_lt_of_crossedDefects` plus the two retained sin 2θ
  bounds, at `A : E →ₗ.[𝕜] E` self-adjoint with bounded `H`, in the vocabulary the
  unbounded Section 2 endpoints already use (`TauCeti.LinearPMap.ReducesSubspace`,
  `IsOddFor`, form bounds on `dom A`, `FormBoundedSylvesterGap`, `specRange`). Parts
  (ii) and (iii) stay as printed — the source restricts them to finite dimensions
  itself. Keep the bounded theorems as specializations. Read `Section8/Theorem82Branch.lean`
  and `Section8/Smallness.lean` first: the 8.2 homotopy argument may be bounded-specific.
  This is real work — Section 8 is 6437 lines built on bounded `Reduces`, `SpectrumIn`
  and `canonicalLowBranch`.

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

- `check_comparator_signatures` is red on the Davis--Kahan config with **8 of 20 comparisons
  differing**, measured 2026-09-05 and unchanged by that day's repair pass. Two are
  `signature-right-unresolved` against `Challenge.DavisKahan1970.Leaderboard`
  (`tanTwoTheta_poleExclusion_exactPaper`,
  `tanTwoTheta_unbounded_directedResidual_symmetricNorming_exactPaper`); the rest are
  `signature-type-mismatch` on library declarations whose Conformance statement drifted. Run
  `python3 scripts/check_comparator_signatures.py --no-build comparator/davis-kahan-1970.json`
  for the current list; without `--no-build` it re-runs a full build per invocation. The gate
  runs in the suite, so a green suite is not available until these are repaired.

- the `per-declaration-expose` ratchet in `dev/policy/ratchet.yaml` tracks upstream
  API-design debt. Do not lower its maximum to
  make it green.
- `check_tauceti_readiness` and `check_tauceti_roadmap_topics` include upstream-review
  and roadmap-placement state. An unavailable optional checkout is not a pass, and an
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

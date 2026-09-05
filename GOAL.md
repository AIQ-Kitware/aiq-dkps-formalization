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

- **`A25-T1`** — state the corrected finite concentration bound as one theorem with
  the entrywise dissimilarity bound `R` explicit. The pieces are compiled and the
  counterexample showing `R` is necessary already exists; this is the honest
  source-facing endpoint, and the repair belongs in the name and docstring.
- **`A25-C1`** — one source-facing declaration for the spectral-norm `r = omega(n^3)`
  corollary, if it really is a single assembly step. Recognizability, not new
  mathematics.
- **`A25-P1`** — the printed compact-Riemannian condition does not force the
  nondegeneracy the argument needs. If a repair is wanted, formulate a meaningful
  spread condition and prove Assumptions 1 and 2 from it. **Label it a repair; it is
  not the printed proposition.** Lower priority than T1 and C1.
- **`A25-PA1`-`PA6`, `L1`-`L5`** — optional source-fidelity wrappers, role-replaced by
  cleaner perturbation machinery. Lowest priority; add them only when they improve
  the paper-facing API for a reader.

---

## Helm 2025

- **`H25-EQ2`** — expose one Helm-facing statement of the displayed
  sample-dissimilarity-to-population limit. It exists by composition, and it is also
  the input the eigengap-free bridge wants.
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

- Do one **current-state API/source review**: stale references after recent refactors,
  hidden added hypotheses, quantifier order, rank-boundary corners, and local
  implementation definitions leaking into public statements.
- **`YWS-T1-eq1`** — optional literal indexed Equation (1) wrapper. The source display
  omits the simplicity hypothesis needed to identify a single sample eigenvector line.
  If added, make that hypothesis explicit and classify it; do not manufacture an
  "exact" wrapper that hides it.

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

- **`DK-HR-NAMING`** — the naming and placement cleanup, item R6 of
  [`docs/planning/davis-kahan-1970-hostile-review-repair-goal.md`](docs/planning/davis-kahan-1970-hostile-review-repair-goal.md),
  is the one part of that contract still open. Eight sub-items: move
  `SineTheta/Presentation.lean` under `namespace TauCeti.DavisKahan1970`; resolve the six
  case-twin pairs on DK-6.1-prop, DK-6.1-thm and DK-6.2-thm; unify source-facing casing
  to the lowercase `theoremN_M_*` form; give `TauCeti.DavisKahan1970` homes to the
  registered witnesses declared outside the paper namespace; rename `UnboundedTrialBlock`
  to `BoundedCompressionTrialBlock` (its compression is bounded, and the current name has
  already misled one certificate); retire the unqualified `SectionTwo.{tanTheta,
  sinTwoTheta, tanTwoTheta}_{complex,real}` clause aliases in favour of the
  `_directed_`/`_ambient_` names; delete `Proposition4_2_compact_nonacute`; and prune
  `lean_declarations` on `S2-sin-two-theta` and `S2-tan-two-theta` to canonical witnesses
  plus explicitly-roled correspondence lemmas. Follow ground rule 3 of that contract for
  every rename — grep `Challenge/` and `comparator/*.json`, run
  `scripts/check_declaration_name_drift.py`, then `lake build Challenge`.

- **`DK-HR-TANGENT-POLE`** — the registered *canonical* tangent endpoints now carry their
  pole-exclusion conjunct, because the directed clause was re-registered on the `_exists_`
  form. The remaining item from F3 is the ambient family: add `HasDefinedAmbientTangent U V`
  (equivalently `‖sinAngleOperatorC U V‖ < 1`) to the conclusion of
  `tanTheta_ambient_bounded_symmetricNorming_{complex,real}_of_crossedDefects`,
  `tanTheta_ambient_unboundedRitz_symmetricNorming_{complex,real}`,
  `tanTheta_ambient_unboundedRitz_explicitCompatibility_symmetricNorming_{complex,real}` and
  `tanTheta_ambient_unboundedOperator_boundedRitz_symmetricNorming_{complex,real}`, and the
  `∀ t ∈ spectrum ℝ (angleOperatorC P V), Real.cos (2 * t) ≠ 0` conjunct to
  `tanTwoTheta_ambient_unbounded_symmetricNorming_{complex,real}`. Every conjunct is
  already proved inside the corresponding proof; this is plumbing, and it makes the
  `HasDefinedAmbientTangent` block comment's "non-vacuous corollary" claim a theorem
  rather than a proof-internal fact.

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

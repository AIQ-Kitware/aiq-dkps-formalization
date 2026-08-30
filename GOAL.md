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

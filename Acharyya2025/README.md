# Acharyya2025 — DKPS concentration (Lean formalization)

**Paper:** Aranyak Acharyya, Joshua Agterberg, Youngser Park, Carey E. Priebe.
*Concentration bounds on response-based vector embeddings of black-box
generative models.* arXiv:2511.08307. A markdown transcription is in
[`prose/`](prose/).

This library formalizes the **finite-sample / high-probability DKPS
concentration** result — the load-bearing hypothesis used downstream by the
`DkpsQuench2026` and `Helm2025` formalizations.

> **For the authors:** this README maps your Theorems 1–2 / Corollaries 1–2 /
> Assumptions 1–2 onto the Lean statements so you can check faithfulness without
> reading Lean proofs. Start with the [crosswalk](#paper--lean-crosswalk) and
> [where-to-start](#where-to-start).

---

## How to read these files (a 2-minute Lean primer for non-Lean readers)

A theorem in Lean looks like this:

```lean
/-- <plain-English description of what this claims> -/
theorem some_name
    (h1 : <hypothesis 1>)        -- <role of h1, tied to your paper>
    (h2 : <hypothesis 2>)        -- ...
    -- Conclusion: <plain-English statement of the claim>
    : <the conclusion> := by
  <proof — you can ignore everything after `:= by`>
```

- Everything **before** `:= by` is the *claim* (hypotheses, then the
  conclusion). Everything **after** `:= by` is the machine-checked *proof* —
  you can skip it.
- We annotated every statement: a `/-- … -/` description above each, inline
  `--` comments tying hypotheses to your Assumptions/Theorems, and a
  `-- Conclusion:` line marking the claim.
- Anything the Lean needs that your paper does **not** state explicitly is
  flagged **"extra (implicit) assumption beyond the paper."** See
  [Assumptions beyond the paper](#what-to-scrutinize-assumptions-beyond-the-paper).
- **Symbol glossary:** `∀` for all · `∃` there exists · `→` implies · `‖x‖`
  norm · `ℝ`/`ℕ` reals/naturals · `B`/`B̂` the true/sample (double-centered)
  CMDS matrix · `ψ`/`ψ̂` true/estimated perspectives · `W*` the aligning
  orthogonal map · `α`,`Λ` the eigenvalue floor / cap (your `C₁`, `C₂` from
  Assumption 2) · `IsHermitian`, `PosSemidef` symmetric / positive-semidefinite
  · `rank` matrix rank · `Tendsto f atTop (𝓝 0)` means `f → 0`.
- **Why the build status matters.** `lake build` succeeds with **0 `sorry`**
  and **0 `axiom`**: every statement is *proved true relative to its stated
  hypotheses*, so your review reduces to **do the hypotheses and conclusion
  match the paper?**

---

## Where to start

The result is assembled in layers; read them in this order:

1. **[`Bridge.lean`](Bridge.lean)** — `EntrywiseClose` and
   `entrywise_close_to_cmds_entrywise_close_of_bounded`: the **Theorem 1**
   content (the centered dissimilarity matrix `B̂` concentrates entrywise
   around `B`).
2. **[`ConfigPerturbation.lean`](ConfigPerturbation.lean)** —
   `exists_isometry_configFrobError_spectralConfig_le` and the explicit
   `configFrobBound`: the paper-facing **Frobenius deterministic core of
   Theorem 2** — an orthogonal `W*` with a Frobenius configuration error bound,
   via Weyl + Davis–Kahan.  The older `ConfigError` / `configBound` theorem is a
   compatibility corollary and pays an additional `√n` conversion.
3. **[`AlignedPipeline.lean`](AlignedPipeline.lean)** —
   `highProb_aligned_configFrobError_of_entrywise_close`: the paper-facing
   **high-probability Theorem 2** route (feed the Theorem-1 event through the
   Frobenius deterministic bound), alongside the legacy `ConfigError` route.
4. **[`RateChain.lean`](RateChain.lean)** — `endToEndFrobRate` /
   `endToEndFrobQuadraticRate` /
   `eventually_endToEndFrobRate_le_endToEndFrobQuadraticRate` /
   `highProb_aligned_configFrobError_endToEndFrobRate`: the paper-facing
   **Corollary 2** rate chain before the legacy `√n` conversion.  The sharpened
   spectral stage is now explicitly majorized by a degree-at-most-two
   polynomial in its operator perturbation. `endToEndRate` remains for the
   older `ConfigError` API.

---

## Paper → Lean crosswalk

| Paper result | Lean declaration | File |
|---|---|---|
| **Theorem 1** — covariance `Σ`; entrywise `B̂ − B` concentration | `EntrywiseClose`, `entrywise_close_to_cmds_entrywise_close_of_bounded` | `Bridge.lean` |
| **Corollary 1** — spectral-norm bound `‖B̂ − B‖` | `MatrixOperatorNormClose` (predicate shape) | `MathlibBridge.lean` |
| **Assumption 1** (`rank B = d`) | rank-`≤ d` hypotheses; `CMDSpectralAssumptions` | `ConfigPerturbation.lean`, `SpectralPipeline.lean` |
| **Assumption 2** (eigenvalue stability `λ_d > C₁`, `λ₁ < C₂`) | eigenvalue floor `α` / cap `Λ` hypotheses | `ConfigPerturbation.lean`, `MatrixPerturbation.lean` |
| **Theorem 2**, deterministic Frobenius core — `∃ W*∈O(d)` | `exists_isometry_configFrobError_spectralConfig_le`, `configFrobBound`; legacy `ConfigError` corollary | `ConfigPerturbation.lean` |
| **Theorem 2**, high-probability Frobenius form | `highProb_aligned_configFrobError_of_entrywise_close`, `…_of_majorant`, `…_of_response_mean`; legacy `ConfigError` siblings | `AlignedPipeline.lean` |
| **Corollary 2** — vanishing rate as budgets grow | `endToEndFrobRate`, `endToEndFrobQuadraticRate`, `eventually_endToEndFrobRate_le_endToEndFrobQuadraticRate`, `tendsto_endToEndFrobQuadraticRate_zero`; legacy `endToEndRate` siblings | `RateChain.lean` |
| Weyl's eigenvalue inequality | `abs_eigenvalues_sub_le` | `Weyl.lean` |
| Davis–Kahan sin-Θ bound; rank-`d` eigengap | `sum_cross_inner_sq_le_opNorm`, `sum_cross_inner_sq_le_of_rank_floor_opNorm`; source-facing crude siblings | `DavisKahan.lean`, `RankGap.lean` |
| The aligning orthogonal map `W*` | `alignedSpectralConfig`, `AlignExists`; Gram rigidity / polar factor | `AlignedPipeline.lean`, `GramRigidity.lean`, `PolarFactor.lean`, `Overlap.lean` |
| PSD rank-`≤d` ⇒ Gram of a `d`-config (produces the population `ψ`) | `exists_config_gram_eq_of_posSemidef_rank_le` | `GramRealization.lean` |
| Matrix-world capstone (entrywise `η` ⇒ aligned Frobenius error) | `exists_isometry_configFrobError_le_of_entrywise_close`; legacy `ConfigError` corollary | `MatrixPerturbation.lean` |

---


### Reuse with DavisKahan / YWS / TauCeti

`ConfigPerturbation.lean` now consumes the selected-block operator-norm
Davis--Kahan endpoint from the reusable `TauCeti`/`DavisKahan` layer and keeps
the exact eigenvalue-commutator residual through a Bessel/Parseval sum.  The
older ambient-`n` wrapper theorems remain available for source fidelity.

The current proof also consumes the Yu--Wang--Samworth population-gap and
alignment results.  The population-only residual sin-Theta bound controls both
cross-energy orientations without a sample-gap condition, removing the former
`hsmall : ε ≤ α / 2` hypothesis.  The YWS aligned-frame/overlap-map bridge is
combined with the sharp TauCeti near-isometry theorem to remove the former
`hpolar` hypothesis.  Thus the paper-facing finite Frobenius theorem now needs
only the population spectral floor/cap/rank assumptions and operator closeness,
not separate local spectral-applicability conditions.

The square-root commutator term also keeps the stronger residual estimate all
the way to the public bound: its denominator is `√α`, rather than the earlier
compatibility envelope `√(α/2)`.

### ArXiv v1 norm inconsistency

The retained transcription is arXiv v1, which is also the version consumed by
the January-2026 Quench argument.  That source is internally inconsistent about
the norm in Theorem 2: the displayed theorem carries a `2,∞` subscript, while
the discussion describes the proved concentration bounds as Frobenius and
lists a two-to-infinity result as future work.  The formalization therefore
exposes the Frobenius norm controlled directly by the appendix-style spectral
argument as `ConfigFrobError`.  The valid rowwise consequence
`‖error_i‖ ≤ ConfigFrobError` is proved separately; it is not labeled as a
literal transcription of the disputed v1 display.

The June-2026 arXiv v2 substantially revises the theorem and its rate.  Updating
the repository's paper target from v1 to v2 should be treated as a separate
source-version migration rather than folded into this Quench-facing v1 chain.

## What to scrutinize: assumptions beyond the paper

- **Measurability of the raw spectral embedding** (`hmeas_spec` in the aligned
  pipeline / downstream bridges). This is the one genuine
  Borel-measurability primitive Lean needs to take probabilities; it concerns a
  *fixed* eigendecomposition map (no data-dependent choice).
- **`AlignExists` / `Classical.choose` alignment.** `alignedSpectralConfig`
  selects the aligning `W*` nonconstructively; to stay choice-free for
  measurability we route through the existential predicate `AlignExists`. This
  is machinery the paper does not need (it argues classically).
- **Assumptions 1–2 are encoded** as `IsHermitian` / `PosSemidef` / `rank ≤ d`
  and explicit eigenvalue floor `α` / cap `Λ` hypotheses.  The former numeric
  `hsmall` / `hpolar` side conditions are no longer part of the finite spectral
  theorem.  Consequently the high-probability finite-bound wrappers also no
  longer assume that the perturbation-rate sequence tends to zero; vanishing
  rates are required only by the separate consistency/rate conclusions that
  actually prove convergence to zero.
- **The response→CMDS transport now has the paper's `n³/r` scaling algebra.**
  The primary bridge bounds each response dissimilarity entry directly by
  `2η/m` instead of first taking a Frobenius norm over all `n²` entries.  With
  `η = x/n`, the subsequent entrywise-to-operator factor of `n` cancels exactly,
  leaving a fixed multiple of `x`, while the Chebyshev/union-bound ratio becomes
  exactly `n³ σ²/x²` (or `n³ γ/(r x²)` for `r` iid replicates).
  `PaperRate.lean` records this cancellation and combines it with
  `configFrobBound_le_configFrobQuadraticMajorant`, so the DK spectral stage is
  bounded by a degree-`≤ 2` polynomial in the same `x`.  It now also formalizes
  the literal source specialization `x=(n³/r)^(1/2-δ)`: `r = ω(n³)` is encoded
  as a Mathlib little-o relation, the Chebyshev ratio reduces to a bounded
  second-moment factor times `(n³/r)^(2δ)`, and both the iid response event and
  the growing DK spectral certificate vanish for `δ ∈ (0,1/2)`.  The
  constructive Quench safe schedule remains available as the explicit
  `(n+1)^-2` / `(n+1)^6` sufficient schedule with compact-cover exponent `2d`.
- **Response boundedness in growing bridges.** The preferred Quench-facing
  response theorem no longer assumes separate uniform bounds for every sample
  and population dissimilarity. A population response-norm envelope, together
  with the response-mean event, derives both bounds where they are needed.
- **Finite-dimensionality** of the ambient space is assumed throughout, as the
  paper intends.

---

## Status

COMPLETE: **zero sorries, zero axioms** — every statement in the library is
proved and true as written. The full chain is formally connected:

> iid responses → second moments (`trace(Σ)/r`) → Chebyshev + union bound →
> dissimilarity entrywise events → CMDS double-centering → Weyl /
> Davis–Kahan / polar-factor perturbation → aligned embedding error
> (`alignedSpectralConfigFrob`, explicit `configFrobBound`) → Quench's uniform
> embedding-error hypothesis and Helm's alignment consistency,

with the explicit fixed-dimension end-to-end rate composed in `RateChain.lean`.
`GrowingPipeline.lean` additionally removes coordinate alignment from
nearest-neighbor consumers by proving pairwise-distance control directly.  Its
`GrowingConfigControl` now tracks `configFrobBound` rather than the legacy
`configBound`, so the growing Quench path also avoids the extra `sqrt(count)`
row-sum conversion while retaining the older `ConfigError` pairwise theorems as
compatibility results.
Four legacy scaffold statements that were false as written were retired (kept
as prose records pointing at their proved replacements; originals in git history). See
[`../docs/planning/acharyya-plan.md`](../docs/planning/acharyya-plan.md) for the
work-package history.

*Provenance:* the original scaffold session's model label is recorded as
`Codex 5.5 High`; the spectral bridge, aligned pipeline, rate chain, and
retirement pass were formalized by Claude Fable 5 (claude-fable-5[1m]), per
user-observed model labels.

## File guide

| File | Contents |
|---|---|
| [`Bridge.lean`](Bridge.lean) | Theorem-1 event chain: response-mean → direct pairwise entrywise → CMDS-entrywise closeness; legacy Frobenius transport retained for compatibility. |
| [`ConfigPerturbation.lean`](ConfigPerturbation.lean) | **The bridge theorem** `exists_isometry_configError_spectralConfig_le` + explicit `configBound` — deterministic core of Theorem 2. |
| [`AlignedPipeline.lean`](AlignedPipeline.lean) | `alignedSpectralConfig` (choice-based aligned estimator) + the high-probability aligned-`ConfigError` theorems (entrywise and response-mean versions). |
| [`GrowingPipeline.lean`](GrowingPipeline.lean) | Choice-free pairwise-distance perturbation, target-augmented growing-dimension foundations, and `GrowingConfigControl` for joint model/response schedules. |
| [`GrowingResponse.lean`](GrowingResponse.lean) | Growing Chebyshev/union-bound concentration, direct response→CMDS transport, and exact `η=x/n` / `n³σ²/x²` paper-scale identities. |
| [`PaperRate.lean`](PaperRate.lean) | Literal `r = ω(n³)` / `(n³/r)^(1/2-δ)` specialization, paper-scale iid response concentration, and the degree-`≤2` DK Frobenius growing certificate. |
| [`RateChain.lean`](RateChain.lean) | Explicit end-to-end rates: the preferred Frobenius `endToEndFrobRate` and HP/vanishing theorems, plus the legacy `ConfigError` rate. |
| [`MatrixPerturbation.lean`](MatrixPerturbation.lean) | Matrix-world capstone: entrywise `η` ⇒ aligned `ConfigError ≤ configBound`, with rank transport for trailing eigenvalues. |
| [`Weyl.lean`](Weyl.lean) | Discrete Courant–Fischer + Weyl's eigenvalue perturbation inequality. |
| [`DavisKahan.lean`](DavisKahan.lean) | Cross-term identity + Davis–Kahan cross-block sin-Θ bound. |
| [`RankGap.lean`](RankGap.lean) | Eigengap derivation from rank-`d` / floor structure via Weyl. |
| [`Overlap.lean`](Overlap.lean) | Eigenvector overlap matrix, `QᵀQ − I` deviation, Sylvester commutator identity. |
| [`PolarFactor.lean`](PolarFactor.lean) | Quantitative polar factor: near-isometry ⇒ exact isometry within `2δ`. |
| [`GramRigidity.lean`](GramRigidity.lean) | Exact Gram rigidity: equal Grams ⇒ isometry-related (the `κ = 0` limit of `W*`). |
| [`GramRealization.lean`](GramRealization.lean) | PSD rank-`≤d` matrices are Gram matrices of `d`-dimensional configurations. |
| [`SpectralPipeline.lean`](SpectralPipeline.lean) | World-map between DKPS/CMDS, matrix, spectral, and configuration layers; `CMDSpectralAssumptions`; population CMDS Gram realization. |
| [`OperatorBridge.lean`](OperatorBridge.lean) | Honest `ℓ²→ℓ²` operator-norm transport between the matrix and operator worlds. |
| [`Deterministic.lean`](Deterministic.lean) | Finite-dimensional centering / double-centering definitions and stability. |
| [`MathlibBridge.lean`](MathlibBridge.lean) | Conversions from curried `DisMat` objects to Mathlib `Matrix`; symmetry / Frobenius / operator-bound predicates. |
| [`Basic.lean`](Basic.lean) | Library entry point (imports). |
| [`prose/`](prose/) | Markdown transcription of the paper. |

Downstream consumers of this library:
[`../DkpsQuench2026/Geometry/AlignedCMDS.lean`](../DkpsQuench2026/Geometry/AlignedCMDS.lean) and
[`../Helm2025/AcharyyaBridge.lean`](../Helm2025/AcharyyaBridge.lean).

## Build / sanity checks

```bash
lake build Acharyya2025
grep -RIn '\baxiom\b' Acharyya2025     # expect: no matches
grep -RIn '\bsorry\b' Acharyya2025     # expect: no matches
```

### Growing response concentration

`GrowingResponse.lean` extends the response-level concentration chain to
stage-dependent finite populations.  It provides:

- sample means constructed from concrete replicate arrays;
- the matrix-valued iid second-moment bound for those averages;
- Chebyshev and union bounds with a varying population size;
- a finite-target double union bound;
- direct response-mean to CMDS-entrywise propagation when the matrix dimension varies;
- the paper-scale choice `η=x/n`, with exact Chebyshev ratio `n³σ²/x²`.

This is the response-level input used by the growing target-augmented Quench
bridge.  For infinite target classes, uniform target concentration remains an
explicit statistical condition rather than being inferred from pointwise
second moments.

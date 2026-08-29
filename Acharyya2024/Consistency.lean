/-
Consistency theorems for:

Acharyya, Trosset, Priebe, Helm.
"Consistent estimation of generative model representations in the data kernel perspective space"
arXiv:2409.17308.

Status (2026-06-11): COMPLETE — no open obligations remain in this file.

- The probabilistic Trosset–Priebe raw-stress stability is proved in
  `Acharyya2024.RawStress`: deterministic core (minimizer existence, √-stress
  Lipschitz continuity, subsequence stability) + a modulus of continuity at the
  limit matrix + outer-measure event inclusion.  No measurable selection of
  minimizers is needed anywhere.
- Statements that were false as written in the original scaffold (missing
  probability hypotheses; an unconditional fixed-limit claim that fails when
  the limiting matrix admits minimizers with distinct distance profiles) have
  been REPAIRED: each now carries the honest hypotheses
  (`hsample`/`hlimit`/`huniq`) and is proved.  The repair history is recorded
  in planning/acharyya-plan.md and in git.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/

import Acharyya2024.Common
import Acharyya2024.RawStress
import Acharyya2024.Probability
import Acharyya2024.ContinuousMDS
import Acharyya2024.GrowingModels
import ForTauCeti.Analysis.InnerProductSpace.Gram.Matrix
import ForTauCeti.Probability.RigidAlignment

open scoped BigOperators Topology ProbabilityTheory
open Filter MeasureTheory

namespace Acharyya2024.Consistency

variable {Ω : Type} [MeasurableSpace Ω]

/-! ## Paper layer 1: fixed model set, fixed query set -/

/--
**Unconditional raw-stress MDS stability (set version).**

If the observed dissimilarity matrices converge in probability to `DeltaInf`,
then with probability tending to one, the random MDS output is `ε`-close in
every pairwise distance to *some* raw-stress minimizer of `DeltaInf`.  This is
the strongest statement that is true without further hypotheses: when
`DeltaInf` admits minimizers with genuinely different distance profiles, no
fixed limit configuration (and no subsequence) can serve all sample paths.

Proved in `Acharyya2024.RawStress.mds_stability_inProbability_set` via a
modulus of continuity at `DeltaInf` plus outer-measure event inclusion — no
measurable selection of minimizers is required.

Mathematical source/citation:
- Trosset and Priebe, "Continuous multidimensional scaling", cited as Theorem 2
  in Acharyya et al. 2024, Appendix A.1/A.2.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
-- Paper correspondence: the *unconditional* (minimizer-SET) form behind paper
-- Theorem 1 / Lemma 1. It is the honest version of those subsequence claims when
-- `DeltaInf` may admit several minimizers with different distance profiles.
theorem rawStress_mds_stability_set
  (P : Measure Ω)
  {n d : Nat}                                  -- n = #models (fixed), d = embedding dimension
  -- Data: a sequence (indexed by replicate count r) of random dissimilarity matrices,
  -- their deterministic limit `DeltaInf`, and a random MDS minimizer `ψhat r ω` for each.
  (Dseq : Nat → Ω → DisMat n)
  (DeltaInf : DisMat n)
  (ψhat : Nat → Ω → Config n d)
  -- `hψhat`: `ψhat r ω` is genuinely a raw-stress minimizer of the observed matrix `Dseq r ω`.
  (hψhat : ∀ r ω, ψhat r ω ∈ MDS n d (Dseq r ω))
  -- `hD`: observed dissimilarities converge to `DeltaInf` in probability (paper's `‖D − Δ^(∞)‖_F →P 0`).
  (hD : ConvergesInProbabilityZero P (fun r ω => frobSub (Dseq r ω) DeltaInf))
  {ε : Real} (hε : 0 < ε) :
  -- Conclusion: with probability → 1, every pairwise distance of `ψhat r ω` is within ε
  -- of those of *some* minimizer of `DeltaInf` (closeness to the minimizer SET).
  Tendsto (fun r => P {ω | ¬ ∃ ψ ∈ MDS n d DeltaInf,
    ∀ i j : Fin n, pairDistErr (ψhat r ω) ψ i j ≤ ε}) atTop (𝓝 0) :=
  RawStress.mds_stability_inProbability_set P Dseq DeltaInf ψhat hψhat hD hε

/-- Unconditional raw-stress stability for the canonical MDS choice.

The selected estimator `RawStress.mdsConfig (Dseq r ω)` is automatically a
minimizer, so the theorem exposes only the genuine statistical premise
`Dseq → DeltaInf` in probability. -/
theorem rawStress_mds_stability_set_canonical
  (P : Measure Ω)
  {n d : Nat}
  (Dseq : Nat → Ω → DisMat n)
  (DeltaInf : DisMat n)
  (hD : ConvergesInProbabilityZero P (fun r ω => frobSub (Dseq r ω) DeltaInf))
  {ε : Real} (hε : 0 < ε) :
  Tendsto (fun r => P {ω | ¬ ∃ ψ ∈ MDS n d DeltaInf,
    ∀ i j : Fin n,
      pairDistErr (RawStress.mdsConfig (d := d) (Dseq r ω)) ψ i j ≤ ε})
    atTop (𝓝 0) := by
  exact rawStress_mds_stability_set P Dseq DeltaInf
    (fun r ω => RawStress.mdsConfig (d := d) (Dseq r ω))
    (fun r ω => RawStress.mdsConfig_mem (d := d) (Dseq r ω)) hD hε

/--
**Corollary 1, alignment step.**

Convergence of every pairwise distance to the target's forces the configurations to be
eventually alignable: for each tolerance there is a rigid motion carrying the estimate that
close to the target.  This is the content of the source's Corollary 1, which upgrades the
pairwise-distance conclusion of Theorem 3 to coordinate convergence after an orthogonal map
and a translation.

The step needs no spectral hypothesis; it is
`TauCeti.eventually_exists_rigidMotion_dist_lt`, a compactness argument.  That matters because
the raw-stress route into it is itself eigengap-free, so this whole path avoids the population
eigenvalue floor that a classical-MDS bridge requires.

Note the quantifier.  The source writes "there exist sequences `W^(u)` and `a^(u)`" outside the
probability, i.e. a single deterministic alignment sequence.  What the argument supports is an
alignment depending on the sample point, since the estimate does; see the census gap
`corollary1-deterministic-alignment`.
-/
theorem exists_rigidMotion_of_pairDist_tendsto
    {n d : Nat} (hn : 0 < n)
    (ψhat : Nat → Config n d) (ψ : Config n d)
    (h : ∀ i j, Tendsto (fun t => pairDistErr (ψhat t) ψ i j) atTop (𝓝 0)) :
    ∀ ε > 0, ∀ᶠ t in atTop,
      ∃ (W : Rvec d ≃ₗᵢ[Real] Rvec d) (a : Rvec d), ∀ i, ‖W (ψhat t i) + a - ψ i‖ < ε := by
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  refine TauCeti.eventually_exists_rigidMotion_dist_lt (φ := ψhat) (ψ := ψ) ?_
  intro i j
  rw [tendsto_iff_dist_tendsto_zero]
  refine (h i j).congr fun t => ?_
  rw [Real.dist_eq]
  rfl

/--
**Corollary 1, almost-sure alignment.**

If almost surely every pairwise distance of the estimates converges to the target's, then
almost surely the estimates are eventually alignable to within any tolerance.  The finitely
many almost-sure hypotheses are intersected and the deterministic alignment step is applied
sample point by sample point.

The almost-sure mode is the one that goes through without extra machinery.  Stating the same
conclusion in probability would additionally require the set of sample points admitting an
`ε`-alignment to be measurable, and that is an existential over the isometry group rather than
a countable condition; making it measurable means introducing the alignment error as an
infimum over rigid motions and proving it continuous, which needs compactness of the group.
See the census gap `corollary1-deterministic-alignment`.
-/
theorem ae_eventually_exists_rigidMotion_of_ae_pairDist_tendsto
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    {n d : Nat} (hn : 0 < n)
    (ψhat : Nat → Ω → Config n d) (ψ : Config n d)
    (h : ∀ i j, ∀ᵐ ω ∂P, Tendsto (fun t => pairDistErr (ψhat t ω) ψ i j) atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, ∀ ε > 0, ∀ᶠ t in atTop,
      ∃ (W : Rvec d ≃ₗᵢ[Real] Rvec d) (a : Rvec d), ∀ i, ‖W (ψhat t ω i) + a - ψ i‖ < ε := by
  have hall : ∀ᵐ ω ∂P, ∀ i j, Tendsto (fun t => pairDistErr (ψhat t ω) ψ i j) atTop (𝓝 0) := by
    rw [MeasureTheory.ae_all_iff]
    intro i
    rw [MeasureTheory.ae_all_iff]
    intro j
    exact h i j
  filter_upwards [hall] with ω hω
  exact exists_rigidMotion_of_pairDist_tendsto hn (fun t => ψhat t ω) ψ hω

/--
Trosset-style raw-stress MDS stability — REPAIRED + PROVED (2026-06-11).

The original scaffold statement asserted a single subsequence and a fixed
`ψ ∈ MDS n d DeltaInf` with convergence in probability, with no hypothesis on
the minimizer set of `DeltaInf`.  That is not provable: if `DeltaInf` has two
minimizers with distinct pairwise-distance profiles and the sample output
oscillates between their neighborhoods with probability `1/2` each, no
subsequence converges in probability to a fixed profile.  The repaired
statement adds the profile-uniqueness hypothesis `huniq` the paper implicitly
needs, and in exchange concludes along the FULL sequence (the witness
subsequence is `id`) — strictly stronger than the paper's subsequence claim.

The unconditional content (closeness to the minimizer SET) is
`rawStress_mds_stability_set` above.

Mathematical source/citation:
- Trosset and Priebe, "Continuous multidimensional scaling", cited as Theorem 2
  in Acharyya et al. 2024, Appendix A.1/A.2.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
-- Paper correspondence: this is the paper's Theorem 1 / Lemma 1 shape
-- (`‖ψ̂_i − ψ̂_{i'}‖ − ‖ψ_i − ψ_{i'}‖ →P 0` along a subsequence), here REPAIRED with the
-- extra profile-uniqueness hypothesis `huniq` (see below) and proved along the FULL sequence.
theorem rawStress_mds_stability
  (P : Measure Ω)
  {n d : Nat}
  (Dseq : Nat → Ω → DisMat n)
  (DeltaInf : DisMat n)
  (ψhat : Nat → Ω → Config n d)
  -- `hψhat`: each `ψhat r ω` is a raw-stress minimizer of the observed matrix.
  (hψhat : ∀ r ω, ψhat r ω ∈ MDS n d (Dseq r ω))
  -- `huniq`: EXTRA (implicit) assumption beyond the paper — all minimizers of `DeltaInf`
  -- share one pairwise-distance profile. The paper's subsequence claim implicitly needs this
  -- (otherwise no fixed profile serves all sample paths); in exchange the conclusion holds
  -- along the full sequence, strictly stronger than the paper's subsequence statement.
  (huniq : RawStress.UniquePairProfile n d DeltaInf)
  -- `hD`: observed dissimilarities → `DeltaInf` in probability (paper's `‖D − Δ^(∞)‖_F →P 0`).
  (hD : ConvergesInProbabilityZero P (fun r ω => frobSub (Dseq r ω) DeltaInf)) :
  -- Conclusion: there is a subsequence `u` (here `id`) and a minimizer `ψ` of `DeltaInf`
  -- such that every pairwise distance error `‖ψ̂_i − ψ̂_{i'}‖ − ‖ψ_i − ψ_{i'}‖` → 0 in probability.
  ∃ u : Nat → Nat,
    Subseq u ∧
    ∃ ψ : Config n d,
      ψ ∈ MDS n d DeltaInf ∧
      ∀ i j : Fin n,
        ConvergesInProbability P (fun t ω => pairDistErr (ψhat (u t) ω) ψ i j) 0 := by
  obtain ⟨ψ, hψ_mem, hψ_conv⟩ :=
    RawStress.mds_stability_inProbability_of_uniqueProfile P Dseq DeltaInf ψhat hψhat huniq hD
  exact ⟨id, strictMono_id, ψ, hψ_mem, fun i j => hψ_conv i j⟩

/--
Fixed `n,m` consistency theorem: paper Theorem 1 shape, with the repaired
profile-uniqueness hypothesis threaded through.

Paper correspondence: this is the **fixed-models / fixed-queries** regime —
the paper's Theorem 1 (Section 4.1). It is a thin renaming wrapper around
`rawStress_mds_stability`.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem fixed_models_fixed_queries_consistency_of_uniqueProfile
  (P : Measure Ω)
  {n d : Nat}
  (Dseq : Nat → Ω → DisMat n)
  (DeltaInf : DisMat n)
  (ψhat : Nat → Ω → Config n d)
  -- `hψhat`: each `ψhat r ω` is a raw-stress minimizer of the observed matrix.
  (hψhat : ∀ r ω, ψhat r ω ∈ MDS n d (Dseq r ω))
  -- `huniq`: EXTRA (implicit) assumption beyond the paper — uniqueness of the minimizer
  -- distance profile of `DeltaInf` (see `rawStress_mds_stability`).
  (huniq : RawStress.UniquePairProfile n d DeltaInf)
  -- `hD`: observed dissimilarities → `DeltaInf` in probability.
  (hD : ConvergesInProbabilityZero P (fun r ω => frobSub (Dseq r ω) DeltaInf)) :
  -- Conclusion: a subsequence of MDS minimizers has pairwise distances converging (in
  -- probability) to those of a true minimizer `ψ` of `DeltaInf` (paper Theorem 1).
  ∃ u : Nat → Nat,
    Subseq u ∧
    ∃ ψ : Config n d,
      ψ ∈ MDS n d DeltaInf ∧
      ∀ i j : Fin n,
        ConvergesInProbability P (fun t ω => pairDistErr (ψhat (u t) ω) ψ i j) 0 := by
  exact rawStress_mds_stability P Dseq DeltaInf ψhat hψhat huniq hD

/--
Fixed-model consistency when the limiting dissimilarities are exactly
realizable in the chosen embedding dimension.

Exact realizability supplies the distance-profile uniqueness premise required
by the repaired fixed-limit theorem, so callers need not prove that technical
condition separately.
-/
theorem fixed_models_fixed_queries_consistency_of_exactRealization
  (P : Measure Ω)
  {n d : Nat}
  (Dseq : Nat → Ω → DisMat n)
  (DeltaInf : DisMat n)
  (ψhat : Nat → Ω → Config n d)
  (hψhat : ∀ r ω, ψhat r ω ∈ MDS n d (Dseq r ω))
  (hexact : ∃ ψ : Config n d, RealizesDissimilarity ψ DeltaInf)
  (hD : ConvergesInProbabilityZero P (fun r ω => frobSub (Dseq r ω) DeltaInf)) :
  ∃ u : Nat → Nat,
    Subseq u ∧
    ∃ ψ : Config n d,
      ψ ∈ MDS n d DeltaInf ∧
      ∀ i j : Fin n,
        ConvergesInProbability P (fun t ω => pairDistErr (ψhat (u t) ω) ψ i j) 0 := by
  exact fixed_models_fixed_queries_consistency_of_uniqueProfile P Dseq DeltaInf ψhat hψhat
    (RawStress.uniquePairProfile_of_exists_realizes hexact) hD

/-- Fixed-model exact-realizability consistency for the canonical MDS
estimator.

This is the lowest-plumbing paper-facing form: existence and membership of the
sample raw-stress minimizer are discharged by `RawStress.mdsConfig`, while exact
realizability dispatches the limiting profile-uniqueness condition. -/
theorem fixed_models_fixed_queries_consistency_canonical_of_exactRealization
  (P : Measure Ω)
  {n d : Nat}
  (Dseq : Nat → Ω → DisMat n)
  (DeltaInf : DisMat n)
  (hexact : ∃ ψ : Config n d, RealizesDissimilarity ψ DeltaInf)
  (hD : ConvergesInProbabilityZero P (fun r ω => frobSub (Dseq r ω) DeltaInf)) :
  ∃ u : Nat → Nat,
    Subseq u ∧
    ∃ ψ : Config n d,
      ψ ∈ MDS n d DeltaInf ∧
      ∀ i j : Fin n,
        ConvergesInProbability P
          (fun t ω => pairDistErr
            (RawStress.mdsConfig (d := d) (Dseq (u t) ω)) ψ i j) 0 := by
  exact fixed_models_fixed_queries_consistency_of_exactRealization P Dseq DeltaInf
    (fun r ω => RawStress.mdsConfig (d := d) (Dseq r ω))
    (fun r ω => RawStress.mdsConfig_mem (d := d) (Dseq r ω)) hexact hD

/-! ## Paper layer 2: fixed model set, growing query set -/

/--
Convergence in probability to zero survives adding a deterministic vanishing
perturbation: if `0 ≤ C r ω ≤ A r ω + b r` with `A → 0` in probability and
`b → 0` deterministically, then `C → 0` in probability.

This is the triangle-inequality layer of the paper's Theorem 2: it splits the
empirical-to-limit error into the sampling error (handled by
`Acharyya2024.Probability`) and the deterministic Assumption-1 error.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
-- Paper correspondence: internal helper (a general "squeeze" for convergence in
-- probability). Not a named paper result; it supplies the triangle-inequality step
-- of paper Theorem 2 used in `growing_queries_dissimilarity_converges`.
theorem convergesInProbabilityZero_of_le_add
    (P : Measure Ω)
    (A C : Nat → Ω → Real)
    (b : Nat → Real)
    -- `hC_nonneg`: `C` is nonnegative (it is a Frobenius distance in the application).
    (hC_nonneg : ∀ r ω, 0 ≤ C r ω)
    -- `hle`: pointwise bound `C ≤ A + b` splitting `C` into a random part `A` and a
    -- deterministic part `b`.
    (hle : ∀ r ω, C r ω ≤ A r ω + b r)
    -- `hA`: random part → 0 in probability; `hb`: deterministic part → 0.
    (hA : ConvergesInProbabilityZero P A)
    (hb : Tendsto b atTop (𝓝 0)) :
    -- Conclusion: `C → 0` in probability.
    ConvergesInProbabilityZero P C := by
  intro ε hε
  have hb_event : ∀ᶠ r in atTop, b r ≤ ε / 2 := by
    have hball : ∀ᶠ r in atTop, b r ∈ Metric.ball (0 : Real) (ε / 2) :=
      hb.eventually (Metric.ball_mem_nhds _ (by linarith))
    filter_upwards [hball] with r hr
    have : |b r| < ε / 2 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hr
    exact ((abs_lt.mp this).2).le
  have hA_half := hA (ε / 2) (by linarith)
  rw [ENNReal.tendsto_nhds_zero] at hA_half ⊢
  intro δ hδ
  filter_upwards [hA_half δ hδ, hb_event] with r hAr hbr
  refine le_trans (measure_mono ?_) hAr
  intro ω hω
  have hCω : ε < C r ω := by
    have : dist (C r ω) 0 > ε := hω
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (hC_nonneg r ω)] at this
  have hAω : ε / 2 < A r ω := by
    have := hle r ω
    linarith
  show dist (A r ω) 0 > ε / 2
  rw [Real.dist_eq, sub_zero]
  exact lt_of_lt_of_le hAω (le_abs_self _)

/--
Probability step for the fixed-model/growing-query regime (paper Theorem 2),
REPAIRED version.

The original scaffold statement had no hypotheses and was false. The honest
content splits as `frobSub (Dseq r ω) DeltaInf ≤
frobSub (Dseq r ω) (Delta r) + frobSub (Delta r) DeltaInf` where:

* `hsample` — the sampling error `frobSub (Dseq r ω) (Delta r)` converges to
  zero in probability; in the paper this is supplied by the Markov/variance
  argument, formalized in `Acharyya2024.Probability`
  (`dissimilarity_convergesInProbability_of_secondMoment`) together with
  `Acharyya2024.SecondMoment` (the iid `trace(Σ)/r` computation).
* `hlimit` — the deterministic Assumption-1 error
  `frobSub (Delta r) DeltaInf → 0`.

Mathematical source/citation:
- Acharyya, Trosset, Priebe, Helm, arXiv:2409.17308, Theorem 2 and Appendix
  A.2 (the final triangle-inequality step invoking Assumption 1).

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
-- Paper correspondence: this is the dissimilarity-concentration content of paper
-- Theorem 2 (`‖D − Δ^(∞)‖_F →P 0`), split via the triangle inequality into a sampling
-- error against the model-mean-discrepancy matrix `Delta r` plus an Assumption-1 error.
theorem growing_queries_dissimilarity_converges
  (P : Measure Ω)
  {n : Nat}
  -- `Dseq` = observed dissimilarities; `Delta r` = stage-`r` population (model-mean
  -- discrepancy) matrix `Δ`; `DeltaInf` = limit `Δ^(∞)` from Assumption 1.
  (Dseq : Nat → Ω → DisMat n)
  (Delta : Nat → DisMat n)
  (DeltaInf : DisMat n)
  -- `hsample`: sampling error `‖D − Δ‖_F →P 0` (supplied in the paper by the Markov/
  -- variance argument of Theorem 2, formalized in `Acharyya2024.Probability`).
  (hsample :
    ConvergesInProbabilityZero P (fun r ω => frobSub (Dseq r ω) (Delta r)))
  -- `hlimit`: deterministic Assumption-1 error `‖Δ − Δ^(∞)‖_F → 0`.
  (hlimit : Tendsto (fun r => frobSub (Delta r) DeltaInf) atTop (𝓝 0)) :
  -- Conclusion: observed dissimilarities converge to `Δ^(∞)` in probability (paper Thm 2).
  ConvergesInProbabilityZero P (fun r ω => frobSub (Dseq r ω) DeltaInf) := by
  refine convergesInProbabilityZero_of_le_add P
    (fun r ω => frobSub (Dseq r ω) (Delta r))
    (fun r ω => frobSub (Dseq r ω) DeltaInf)
    (fun r => frobSub (Delta r) DeltaInf)
    (fun r ω => Real.sqrt_nonneg _)
    (fun r ω => ?_) hsample hlimit
  -- Triangle inequality for the Frobenius distance, via the `ℓ²(pairs)` norm.
  have htri := abs_norm_sub_norm_le
    (WithLp.toLp 2 (fun p : Fin n × Fin n => Dseq r ω p.1 p.2 - DeltaInf p.1 p.2))
    (WithLp.toLp 2 (fun p : Fin n × Fin n => Delta r p.1 p.2 - DeltaInf p.1 p.2))
  have hnorm : ∀ (A B : DisMat n),
      ‖WithLp.toLp 2 (fun p : Fin n × Fin n => A p.1 p.2 - B p.1 p.2)‖
        = frobSub A B := by
    intro A B
    rw [EuclideanSpace.norm_eq, frobSub, frob, frobSq]
    congr 1
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp [Real.norm_eq_abs, sq_abs]
  have hdiff : ‖WithLp.toLp 2 (fun p : Fin n × Fin n => Dseq r ω p.1 p.2 - DeltaInf p.1 p.2)
        - WithLp.toLp 2 (fun p : Fin n × Fin n => Delta r p.1 p.2 - DeltaInf p.1 p.2)‖
      = frobSub (Dseq r ω) (Delta r) := by
    rw [← hnorm (Dseq r ω) (Delta r)]
    congr 1
    apply (WithLp.linearEquiv 2 ℝ _).injective
    ext p
    show (Dseq r ω p.1 p.2 - DeltaInf p.1 p.2) - (Delta r p.1 p.2 - DeltaInf p.1 p.2)
      = Dseq r ω p.1 p.2 - Delta r p.1 p.2
    ring
  rw [hnorm, hnorm, hdiff] at htri
  have := (abs_le.mp htri).2
  linarith

/--
The growing-query dissimilarity conclusion with the deterministic limit
assumption reduced to entrywise convergence.

Because the model set is fixed and finite, pointwise convergence of every
population dissimilarity entry automatically gives the required Frobenius
convergence.
-/
theorem growing_queries_dissimilarity_converges_of_entrywise
  (P : Measure Ω)
  {n : Nat}
  (Dseq : Nat → Ω → DisMat n)
  (Delta : Nat → DisMat n)
  (DeltaInf : DisMat n)
  (hsample :
    ConvergesInProbabilityZero P (fun r ω => frobSub (Dseq r ω) (Delta r)))
  (hentry : ∀ i j : Fin n,
    Tendsto (fun r => Delta r i j) atTop (𝓝 (DeltaInf i j))) :
  ConvergesInProbabilityZero P (fun r ω => frobSub (Dseq r ω) DeltaInf) := by
  exact growing_queries_dissimilarity_converges P Dseq Delta DeltaInf hsample
    (tendsto_frobSub_zero_of_entrywise Delta DeltaInf hentry)

/--
Fixed `n`, growing-query consistency: paper Theorem 3 shape, with the repaired
probability-step hypotheses threaded through.

Paper correspondence: this is the **fixed-models / growing-queries** regime
(Section 4.2). It combines paper Theorem 2 (the dissimilarity step,
`growing_queries_dissimilarity_converges`) with Lemma 1 / the layer-1 stability
to yield paper Theorem 3 (under the `o(r)` variance condition, here supplied
abstractly via `hsample`/`hlimit`).

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem fixed_models_growing_queries_consistency_of_uniqueProfile
  (P : Measure Ω)
  {n d : Nat}
  (Dseq : Nat → Ω → DisMat n)
  (Delta : Nat → DisMat n)
  (DeltaInf : DisMat n)
  (ψhat : Nat → Ω → Config n d)
  -- `hψhat`: each `ψhat r ω` minimizes raw stress for the observed matrix.
  (hψhat : ∀ r ω, ψhat r ω ∈ MDS n d (Dseq r ω))
  -- `huniq`: EXTRA (implicit) assumption beyond the paper — minimizer profile uniqueness.
  (huniq : RawStress.UniquePairProfile n d DeltaInf)
  -- `hsample` + `hlimit`: the two parts of the paper Theorem 2 dissimilarity step
  -- (sampling error and Assumption-1 error). In the paper these follow from the
  -- variance condition `(1/m)∑_j γ_ij = o(r)`; here they are taken as hypotheses.
  (hsample :
    ConvergesInProbabilityZero P (fun r ω => frobSub (Dseq r ω) (Delta r)))
  (hlimit : Tendsto (fun r => frobSub (Delta r) DeltaInf) atTop (𝓝 0)) :
  -- Conclusion: a subsequence of MDS minimizers has pairwise distances converging in
  -- probability to those of a true minimizer `ψ` of `Δ^(∞)` (paper Theorem 3).
  ∃ u : Nat → Nat,
    Subseq u ∧
    ∃ ψ : Config n d,
      ψ ∈ MDS n d DeltaInf ∧
      ∀ i j : Fin n,
        ConvergesInProbability P (fun t ω => pairDistErr (ψhat (u t) ω) ψ i j) 0 := by
  exact fixed_models_fixed_queries_consistency_of_uniqueProfile P Dseq DeltaInf ψhat hψhat huniq
    (growing_queries_dissimilarity_converges P Dseq Delta DeltaInf hsample hlimit)

/--
Fixed-model, growing-query consistency with both technical limit assumptions
dispatched by natural structural hypotheses: exact realizability of the limit
and entrywise convergence of the population dissimilarities.
-/
theorem fixed_models_growing_queries_consistency_of_exactRealization_entrywise
  (P : Measure Ω)
  {n d : Nat}
  (Dseq : Nat → Ω → DisMat n)
  (Delta : Nat → DisMat n)
  (DeltaInf : DisMat n)
  (ψhat : Nat → Ω → Config n d)
  (hψhat : ∀ r ω, ψhat r ω ∈ MDS n d (Dseq r ω))
  (hexact : ∃ ψ : Config n d, RealizesDissimilarity ψ DeltaInf)
  (hsample :
    ConvergesInProbabilityZero P (fun r ω => frobSub (Dseq r ω) (Delta r)))
  (hentry : ∀ i j : Fin n,
    Tendsto (fun r => Delta r i j) atTop (𝓝 (DeltaInf i j))) :
  ∃ u : Nat → Nat,
    Subseq u ∧
    ∃ ψ : Config n d,
      ψ ∈ MDS n d DeltaInf ∧
      ∀ i j : Fin n,
        ConvergesInProbability P (fun t ω => pairDistErr (ψhat (u t) ω) ψ i j) 0 := by
  exact fixed_models_fixed_queries_consistency_of_exactRealization P Dseq DeltaInf ψhat
    hψhat hexact
    (growing_queries_dissimilarity_converges_of_entrywise P Dseq Delta DeltaInf hsample hentry)

/-- Fixed-model, growing-query consistency for the canonical raw-stress
estimator, with exact realizability and entrywise population convergence.

All minimizer-selection and deterministic Frobenius-limit plumbing is
discharged internally. -/
theorem fixed_models_growing_queries_consistency_canonical_of_exactRealization_entrywise
  (P : Measure Ω)
  {n d : Nat}
  (Dseq : Nat → Ω → DisMat n)
  (Delta : Nat → DisMat n)
  (DeltaInf : DisMat n)
  (hexact : ∃ ψ : Config n d, RealizesDissimilarity ψ DeltaInf)
  (hsample :
    ConvergesInProbabilityZero P (fun r ω => frobSub (Dseq r ω) (Delta r)))
  (hentry : ∀ i j : Fin n,
    Tendsto (fun r => Delta r i j) atTop (𝓝 (DeltaInf i j))) :
  ∃ u : Nat → Nat,
    Subseq u ∧
    ∃ ψ : Config n d,
      ψ ∈ MDS n d DeltaInf ∧
      ∀ i j : Fin n,
        ConvergesInProbability P
          (fun t ω => pairDistErr
            (RawStress.mdsConfig (d := d) (Dseq (u t) ω)) ψ i j) 0 := by
  exact fixed_models_growing_queries_consistency_of_exactRealization_entrywise
    P Dseq Delta DeltaInf
    (fun r ω => RawStress.mdsConfig (d := d) (Dseq r ω))
    (fun r ω => RawStress.mdsConfig_mem (d := d) (Dseq r ω))
    hexact hsample hentry

/-! ## Paper layer 3: growing model set and growing query set -/

/--
Triangular-array consistency for the growing-model regime — REPAIRED + PROVED
(2026-06-11, WP8).

The paper's final regime involves a triangular array of model sets and query
sets: at stage `k` there are `nOf k` models, and for each fixed `k` the sampled
dissimilarity matrices converge (in probability) to the stage-`k` limit
`DeltaInf k`.  The original scaffold statement had NO probability hypotheses
connecting `Dseq` to `DeltaInf` and was false as written; the repaired version
adds the per-stage hypotheses `hD` (dissimilarity convergence) and `huniq`
(profile uniqueness, as in `rawStress_mds_stability`).

The paper extracts one shared subsequence across all stages by a diagonal
argument.  Under the repaired layer-1 stability the diagonal argument is
unnecessary: the full sequence converges at every stage, so the shared
subsequence is simply `id` — a strictly stronger conclusion.

SCOPE CAVEAT (honesty).  This is the *per-stage, finite* form: a countable family
of finite (`Fin (nOf k)`) consistency statements, one per stage `k`.  It is NOT
the paper's full Theorem 4/5 conclusion, which is an `Lᵖ` average over a
*continuum* of iid model draws `φ ~ P` from the model space —
`∫∫ |‖ψ̂₁ − ψ̂₂‖ − ‖mds(φ₁) − mds(φ₂)‖|ᵖ dP dP →P 0`.  Modelling the model
distribution `P`, the iid draw of models, and the continuous-MDS map `mds(φ)` is
not formalized here; this theorem is the finite consistency content that the
paper's argument specializes to at each stage, re-indexed over stages.

Mathematical source/citation:
- Acharyya, Trosset, Priebe, Helm, "Consistent estimation of generative model
  representations in the data kernel perspective space", Theorem 4 and Appendix
  A.3 (the finite per-stage content; the integral-over-`P` form is not
  formalized — see the scope caveat).

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
-- Paper correspondence: the **growing-models / growing-queries** regime (Section 4.3),
-- corresponding to the FINITE per-stage content of paper Theorem 4. See the SCOPE CAVEAT
-- above: this is NOT the paper's full Lᵖ-over-the-model-distribution conclusion.
theorem growing_models_growing_queries_perStage_consistency_of_uniqueProfile
  (P : Measure Ω)
  (d : Nat)
  -- `nOf k` = number of models at stage `k` (a triangular array; the model count grows in `k`).
  (nOf : Nat → Nat)
  -- Per-stage data: observed dissimilarities `Dseq`, limits `DeltaInf k`, minimizers `ψhat`.
  (Dseq : Nat → Ω → (k : Nat) → DisMat (nOf k))
  (DeltaInf : (k : Nat) → DisMat (nOf k))
  (ψhat : Nat → Ω → (k : Nat) → Config (nOf k) d)
  -- `hψhat`: at every stage `k`, `ψhat r ω k` minimizes raw stress for the observed matrix.
  (hψhat : ∀ r ω k, ψhat r ω k ∈ MDS (nOf k) d (Dseq r ω k))
  -- `huniq`: EXTRA (implicit) assumption beyond the paper — per-stage minimizer profile uniqueness.
  (huniq : ∀ k, RawStress.UniquePairProfile (nOf k) d (DeltaInf k))
  -- `hD`: per-stage dissimilarity convergence in probability (paper's `D →P Δ^(∞)`, each stage).
  (hD : ∀ k, ConvergesInProbabilityZero P
    (fun r ω => frobSub (Dseq r ω k) (DeltaInf k))) :
  -- Conclusion: a single subsequence `u` (here `id`) such that, at every stage `k`, the MDS
  -- minimizers' pairwise distances converge in probability to those of a true minimizer `ψ`.
  ∃ u : Nat → Nat,
    Subseq u ∧
    ∀ k : Nat,
      ∃ ψ : Config (nOf k) d,
        ψ ∈ MDS (nOf k) d (DeltaInf k) ∧
        ∀ i j : Fin (nOf k),
          ConvergesInProbability P
            (fun t ω => pairDistErr (ψhat (u t) ω k) ψ i j) 0 := by
  refine ⟨id, strictMono_id, fun k => ?_⟩
  obtain ⟨ψ, hψ_mem, hψ_conv⟩ :=
    RawStress.mds_stability_inProbability_of_uniqueProfile P
      (fun r ω => Dseq r ω k) (DeltaInf k) (fun r ω => ψhat r ω k)
      (fun r ω => hψhat r ω k) (huniq k) (hD k)
  exact ⟨ψ, hψ_mem, fun i j => hψ_conv i j⟩

/--
Per-stage growing-model consistency when every stage limit is exactly
realizable in the common embedding dimension.
-/
theorem growing_models_growing_queries_perStage_consistency_of_exactRealization
  (P : Measure Ω)
  (d : Nat)
  (nOf : Nat → Nat)
  (Dseq : Nat → Ω → (k : Nat) → DisMat (nOf k))
  (DeltaInf : (k : Nat) → DisMat (nOf k))
  (ψhat : Nat → Ω → (k : Nat) → Config (nOf k) d)
  (hψhat : ∀ r ω k, ψhat r ω k ∈ MDS (nOf k) d (Dseq r ω k))
  (hexact : ∀ k, ∃ ψ : Config (nOf k) d,
    RealizesDissimilarity ψ (DeltaInf k))
  (hD : ∀ k, ConvergesInProbabilityZero P
    (fun r ω => frobSub (Dseq r ω k) (DeltaInf k))) :
  ∃ u : Nat → Nat,
    Subseq u ∧
    ∀ k : Nat,
      ∃ ψ : Config (nOf k) d,
        ψ ∈ MDS (nOf k) d (DeltaInf k) ∧
        ∀ i j : Fin (nOf k),
          ConvergesInProbability P
            (fun t ω => pairDistErr (ψhat (u t) ω k) ψ i j) 0 := by
  exact growing_models_growing_queries_perStage_consistency_of_uniqueProfile P d nOf Dseq
    DeltaInf ψhat hψhat
    (fun k => RawStress.uniquePairProfile_of_exists_realizes (hexact k)) hD

/-- Per-stage growing-model consistency for the canonical raw-stress estimator
when every stage limit is exactly realizable. -/
theorem growing_models_growing_queries_perStage_consistency_canonical_of_exactRealization
  (P : Measure Ω)
  (d : Nat)
  (nOf : Nat → Nat)
  (Dseq : Nat → Ω → (k : Nat) → DisMat (nOf k))
  (DeltaInf : (k : Nat) → DisMat (nOf k))
  (hexact : ∀ k, ∃ ψ : Config (nOf k) d,
    RealizesDissimilarity ψ (DeltaInf k))
  (hD : ∀ k, ConvergesInProbabilityZero P
    (fun r ω => frobSub (Dseq r ω k) (DeltaInf k))) :
  ∃ u : Nat → Nat,
    Subseq u ∧
    ∀ k : Nat,
      ∃ ψ : Config (nOf k) d,
        ψ ∈ MDS (nOf k) d (DeltaInf k) ∧
        ∀ i j : Fin (nOf k),
          ConvergesInProbability P
            (fun t ω => pairDistErr
              (RawStress.mdsConfig (d := d) (Dseq (u t) ω k)) ψ i j) 0 := by
  exact growing_models_growing_queries_perStage_consistency_of_exactRealization
    P d nOf Dseq DeltaInf
    (fun r ω k => RawStress.mdsConfig (d := d) (Dseq r ω k))
    (fun r ω k => RawStress.mdsConfig_mem (d := d) (Dseq r ω k))
    hexact hD

/--
Triangular-array consistency in the paper's Theorem-5 *shape*: the per-stage
dissimilarity convergence is split into a per-stage sampling error against a
stage-and-budget population `Delta r k` plus a deterministic per-stage
Assumption-1 error, mirroring `fixed_models_growing_queries_consistency_of_uniqueProfile`.

Same SCOPE CAVEAT as `growing_models_growing_queries_perStage_consistency_of_uniqueProfile`:
this is the finite per-stage form, not the paper's `Lᵖ`-over-the-model-distribution
conclusion (the model distribution and the continuous-MDS map are not
formalized).

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
-- Paper correspondence: the **growing-models / growing-queries** regime in the paper's
-- Theorem 5 *shape* (the finite per-stage content). Same SCOPE CAVEAT as above: not the
-- paper's full Lᵖ-over-the-model-distribution conclusion.
theorem growing_models_growing_queries_perStage_consistency_of_sample_limit_uniqueProfile
  (P : Measure Ω)
  (d : Nat)
  (nOf : Nat → Nat)                                   -- stage-`k` model count
  -- Per-stage data, with `Delta r k` the stage-`k`, budget-`r` population matrix.
  (Dseq : Nat → Ω → (k : Nat) → DisMat (nOf k))
  (Delta : Nat → (k : Nat) → DisMat (nOf k))
  (DeltaInf : (k : Nat) → DisMat (nOf k))
  (ψhat : Nat → Ω → (k : Nat) → Config (nOf k) d)
  -- `hψhat`: per-stage raw-stress minimality of `ψhat`.
  (hψhat : ∀ r ω k, ψhat r ω k ∈ MDS (nOf k) d (Dseq r ω k))
  -- `huniq`: EXTRA (implicit) assumption beyond the paper — per-stage profile uniqueness.
  (huniq : ∀ k, RawStress.UniquePairProfile (nOf k) d (DeltaInf k))
  -- `hsample` + `hlimit`: per-stage split of the dissimilarity convergence (paper Theorem 4)
  -- into sampling error and deterministic Assumption-2 error.
  (hsample : ∀ k, ConvergesInProbabilityZero P
    (fun r ω => frobSub (Dseq r ω k) (Delta r k)))
  (hlimit : ∀ k, Tendsto (fun r => frobSub (Delta r k) (DeltaInf k)) atTop (𝓝 0)) :
  -- Conclusion: one subsequence `u` (here `id`) giving per-stage in-probability convergence
  -- of MDS pairwise distances to those of a true minimizer `ψ` (paper Theorem 5 shape).
  ∃ u : Nat → Nat,
    Subseq u ∧
    ∀ k : Nat,
      ∃ ψ : Config (nOf k) d,
        ψ ∈ MDS (nOf k) d (DeltaInf k) ∧
        ∀ i j : Fin (nOf k),
          ConvergesInProbability P
            (fun t ω => pairDistErr (ψhat (u t) ω k) ψ i j) 0 := by
  refine growing_models_growing_queries_perStage_consistency_of_uniqueProfile P d nOf Dseq DeltaInf ψhat
    hψhat huniq (fun k => ?_)
  exact growing_queries_dissimilarity_converges P
    (fun r ω => Dseq r ω k) (fun r => Delta r k) (DeltaInf k)
    (hsample k) (hlimit k)

/-- Canonical-MDS version of the per-stage sample/population-limit theorem,
with exact realizability replacing the profile-uniqueness premise. -/
theorem growing_models_growing_queries_perStage_consistency_canonical_of_sample_limit_exactRealization
  (P : Measure Ω)
  (d : Nat)
  (nOf : Nat → Nat)
  (Dseq : Nat → Ω → (k : Nat) → DisMat (nOf k))
  (Delta : Nat → (k : Nat) → DisMat (nOf k))
  (DeltaInf : (k : Nat) → DisMat (nOf k))
  (hexact : ∀ k, ∃ ψ : Config (nOf k) d,
    RealizesDissimilarity ψ (DeltaInf k))
  (hsample : ∀ k, ConvergesInProbabilityZero P
    (fun r ω => frobSub (Dseq r ω k) (Delta r k)))
  (hlimit : ∀ k, Tendsto (fun r => frobSub (Delta r k) (DeltaInf k)) atTop (𝓝 0)) :
  ∃ u : Nat → Nat,
    Subseq u ∧
    ∀ k : Nat,
      ∃ ψ : Config (nOf k) d,
        ψ ∈ MDS (nOf k) d (DeltaInf k) ∧
        ∀ i j : Fin (nOf k),
          ConvergesInProbability P
            (fun t ω => pairDistErr
              (RawStress.mdsConfig (d := d) (Dseq (u t) ω k)) ψ i j) 0 := by
  exact growing_models_growing_queries_perStage_consistency_of_sample_limit_uniqueProfile
    P d nOf Dseq Delta DeltaInf
    (fun r ω k => RawStress.mdsConfig (d := d) (Dseq r ω k))
    (fun r ω k => RawStress.mdsConfig_mem (d := d) (Dseq r ω k))
    (fun k => RawStress.uniquePairProfile_of_exists_realizes (hexact k))
    hsample hlimit

/--
**Corollary 1, in probability.**

The almost-sure form above is the one that goes through with a deterministic modulus.  The
in-probability form needs more: a modulus valid for *every* configuration at once, since the
sample point is not fixed while the tolerance is chosen.  That is
`TauCeti.exists_delta_forall_exists_rigidMotion`, and the alignment error it bounds --
`TauCeti.alignmentError`, the least uniform distance to the target achievable by a rigid motion
-- is the quantity that converges.

The hypothesis is exactly the conclusion of `rawStress_mds_stability`: each of the finitely many
pairwise distance errors converges to zero in probability.  A union bound assembles them.

No measurability is required of the estimates.  The events here are existential over the
isometry group, so they need not be measurable, but a measure is monotone and countably
subadditive on arbitrary sets and that is all the argument uses.
-/
theorem tendsto_measure_alignmentError_of_pairDist_convergesInProbability
    (P : Measure Ω) [IsProbabilityMeasure P]
    {n d : Nat} (hn : 0 < n)
    (ψhat : Nat → Ω → Config n d) (ψ : Config n d)
    (h : ∀ i j, ConvergesInProbability P (fun t ω => pairDistErr (ψhat t ω) ψ i j) 0)
    {ε : Real} (hε : 0 < ε) :
    Tendsto (fun t => P {ω | ε < TauCeti.alignmentError ψ (ψhat t ω)}) atTop (𝓝 0) := by
  classical
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hunion : ∀ δ > (0 : Real), Tendsto
      (fun t => P {ω | ¬ ∀ i j, |‖ψhat t ω i - ψhat t ω j‖ - ‖ψ i - ψ j‖| ≤ δ})
      atTop (𝓝 0) := by
    intro δ hδ
    have hsub : ∀ t, {ω | ¬ ∀ i j, |‖ψhat t ω i - ψhat t ω j‖ - ‖ψ i - ψ j‖| ≤ δ}
        ⊆ ⋃ p : Fin n × Fin n,
            {ω | dist (pairDistErr (ψhat t ω) ψ p.1 p.2) 0 > δ} := by
      intro t ω hω
      simp only [Set.mem_ofPred_eq, not_forall, not_le] at hω
      obtain ⟨i, j, hij⟩ := hω
      refine Set.mem_iUnion.mpr ⟨(i, j), ?_⟩
      simp only [Set.mem_ofPred_eq, gt_iff_lt, Real.dist_eq, sub_zero, pairDistErr, pairDist,
        abs_abs]
      exact hij
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (f := fun t => P {ω | ¬ ∀ i j, |‖ψhat t ω i - ψhat t ω j‖ - ‖ψ i - ψ j‖| ≤ δ})
      (h := fun t => ∑ p : Fin n × Fin n,
        P {ω | dist (pairDistErr (ψhat t ω) ψ p.1 p.2) 0 > δ}) ?_
      (Filter.Eventually.of_forall fun _ => bot_le)
      (Filter.Eventually.of_forall fun t => ?_)
    · have hsum : Tendsto (fun t => ∑ p : Fin n × Fin n,
          P {ω | dist (pairDistErr (ψhat t ω) ψ p.1 p.2) 0 > δ}) atTop (𝓝 0) := by
        have := tendsto_finset_sum (Finset.univ : Finset (Fin n × Fin n))
          (fun p _ => h p.1 p.2 δ hδ)
        simpa using this
      exact hsum
    · calc P {ω | ¬ ∀ i j, |‖ψhat t ω i - ψhat t ω j‖ - ‖ψ i - ψ j‖| ≤ δ}
          ≤ P (⋃ p : Fin n × Fin n,
              {ω | dist (pairDistErr (ψhat t ω) ψ p.1 p.2) 0 > δ}) := measure_mono (hsub t)
        _ ≤ ∑' p : Fin n × Fin n,
              P {ω | dist (pairDistErr (ψhat t ω) ψ p.1 p.2) 0 > δ} := measure_iUnion_le _
        _ = ∑ p : Fin n × Fin n,
              P {ω | dist (pairDistErr (ψhat t ω) ψ p.1 p.2) 0 > δ} := tsum_fintype _
  exact TauCeti.tendsto_measure_alignmentError_gt P ψhat (fun _ => ψ)
    (fun _ _ => measurable_const) hunion hε

/--
**Corollary 1, coordinate convergence in probability.**

The printed corollary asserts convergence of the aligned coordinates, not of the alignment
error.  `TauCeti.alignedConfig` performs the alignment inside the estimator -- sample point by
sample point, up to a slack `s t` that may be taken to vanish -- so its coordinates converge in
probability to the target's.

The alignment is therefore chosen *inside* the probability.  The source writes "there exist
sequences `W^(u)` and `a^(u)`" outside it, which the argument does not support, since the
aligning motion depends on the estimate and hence on the sample point; see the census gap
`corollary1-deterministic-alignment`.
-/
theorem tendsto_measure_alignedConfig_dist_gt
    (P : Measure Ω) [IsProbabilityMeasure P]
    {n d : Nat} (hn : 0 < n)
    (ψhat : Nat → Ω → Config n d) (ψ : Config n d)
    (s : Nat → Real) (hs : ∀ t, 0 < s t) (hs0 : Tendsto s atTop (𝓝 0))
    (h : ∀ i j, ConvergesInProbability P (fun t ω => pairDistErr (ψhat t ω) ψ i j) 0)
    {ε : Real} (hε : 0 < ε) :
    Tendsto
      (fun t => P {ω | ∃ i, ε < ‖TauCeti.alignedConfig ψ (ψhat t ω) (s t) i - ψ i‖})
      atTop (𝓝 0) := by
  classical
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hAE := tendsto_measure_alignmentError_of_pairDist_convergesInProbability P hn ψhat ψ h
    (ε := ε / 2) (by linarith)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hAE
    (Filter.Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [Filter.Tendsto.eventually_lt_const
    (show (0 : Real) < ε / 2 by linarith) hs0] with t hts
  refine measure_mono fun ω hω => ?_
  obtain ⟨i, hi⟩ := hω
  have hle := TauCeti.norm_alignedConfig_sub_le ψ (ψhat t ω) (hs t) i
  show ε / 2 < TauCeti.alignmentError ψ (ψhat t ω)
  linarith

/-! ### Corollary 1 as printed is false

The source writes "there exist sequences `W^(u)` and `a^(u)`" *outside* the probability: one
orthogonal map and one translation per stage, serving every sample point.  The argument does not
support that, and neither does the mathematics.  A raw-stress minimizer is determined only up to
a rigid motion, so a legitimate selection may return a reflected copy on some sample points and
the original on others.  Every pairwise distance is then exactly correct at every stage, so the
hypothesis holds in its strongest form, while no single motion can align both branches.

The repair is `tendsto_measure_alignedConfig_dist_gt`: choose the motion inside the probability,
sample point by sample point.  That is what the estimator can actually do, and it is what the
corollary's downstream uses need.
-/

/-- The fair two-point measure on `Bool`, the sample space of the refutation. -/
noncomputable def coinMeasure : Measure Bool :=
  (1 / 2 : ENNReal) • Measure.dirac true + (1 / 2 : ENNReal) • Measure.dirac false

instance : IsProbabilityMeasure coinMeasure := by
  constructor
  simp only [coinMeasure, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [one_div]
  exact ENNReal.inv_two_add_inv_two

theorem coinMeasure_singleton (b : Bool) : coinMeasure {b} = 1 / 2 := by
  cases b <;> simp [coinMeasure, Measure.coe_add, Measure.coe_smul]

/-- Integration against the fair two-point measure. -/
theorem integral_coinMeasure (f : Bool → Real) :
    ∫ ω, f ω ∂coinMeasure = (1 / 2) * f true + (1 / 2) * f false := by
  haveI hf1 : IsFiniteMeasure ((1 / 2 : ENNReal) • Measure.dirac (α := Bool) true) :=
    ⟨by simp⟩
  haveI hf2 : IsFiniteMeasure ((1 / 2 : ENNReal) • Measure.dirac (α := Bool) false) :=
    ⟨by simp⟩
  have h1 : Integrable f ((1 / 2 : ENNReal) • Measure.dirac (α := Bool) true) :=
    Integrable.of_finite
  have h2 : Integrable f ((1 / 2 : ENNReal) • Measure.dirac (α := Bool) false) :=
    Integrable.of_finite
  rw [coinMeasure, integral_add_measure h1 h2, integral_smul_measure, integral_smul_measure,
    integral_dirac, integral_dirac]
  norm_num

theorem coinMeasure_ge_half {S : Set Bool} (hS : true ∈ S ∨ false ∈ S) :
    (1 / 2 : ENNReal) ≤ coinMeasure S := by
  rcases hS with h | h
  · rw [← coinMeasure_singleton true]
    exact measure_mono (Set.singleton_subset_iff.mpr h)
  · rw [← coinMeasure_singleton false]
    exact measure_mono (Set.singleton_subset_iff.mpr h)

/--
**Corollary 1, as printed, is false.**

There is a selection of raw-stress minimizers whose pairwise distances are *exactly* those of
the target at every stage -- so the corollary's hypothesis holds in its strongest possible form
-- and yet for no sequence of orthogonal maps `W^(u)` and translations `a^(u)` do the estimated
coordinates converge in probability to `W^(u) ψ_i + a^(u)`.

The witness is the one-dimensional two-point configuration `(0, x)` together with its reflection
`(0, -x)`, each selected with probability one half.  Both are genuine minimizers, since raw
stress depends only on pairwise distances; a single motion within `‖x‖/2` of both would put `x`
and `-x` within `‖x‖` of each other.

`tendsto_measure_alignedConfig_dist_gt` is the corresponding repair, with the motion chosen
inside the probability.
-/
theorem not_exists_deterministic_rigidMotion_of_pairDist_exact :
    ∃ (ψhat : Nat → Bool → Config 2 1) (ψ : Config 2 1) (D : DisMat 2),
      -- the estimates and the target are genuine raw-stress minimizers, as in the corollary's
      -- own setting: they are MDS outputs, not arbitrary configurations
      (∀ t ω, ψhat t ω ∈ MDS 2 1 D) ∧ ψ ∈ MDS 2 1 D ∧
      (∀ i j, ConvergesInProbability coinMeasure
        (fun t ω => pairDistErr (ψhat t ω) ψ i j) 0) ∧
      ∀ (W : Nat → (Rvec 1 ≃ₗᵢ[Real] Rvec 1)) (a : Nat → Rvec 1),
        ¬ ∀ ε > (0 : Real), Tendsto
            (fun t => coinMeasure
              {ω | ∃ i, ε < ‖ψhat t ω i - (W t (ψ i) + a t)‖}) atTop (𝓝 0) := by
  classical
  set x : Rvec 1 := EuclideanSpace.single 0 (1 : Real) with hxdef
  have hxnorm : ‖x‖ = 1 := by simp [hxdef]
  set D : DisMat 2 := fun i j => if i = j then 0 else 1 with hD
  -- both branches realize `D` exactly, so both have zero raw stress and are minimizers
  have hmin : ∀ z : Config 2 1, rawStress 2 1 D z = 0 → z ∈ MDS 2 1 D := by
    intro z hz w
    rw [hz]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hstress : ∀ y : Rvec 1, ‖y‖ = 1 → rawStress 2 1 D ![0, y] = 0 := by
    intro y hy
    simp only [rawStress, Fin.sum_univ_two, hD, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
    norm_num [hy, Fin.ext_iff, norm_sub_rev (0 : Rvec 1) y]
  have hmem0 : (![0, x] : Config 2 1) ∈ MDS 2 1 D := hmin _ (hstress x hxnorm)
  have hmemn : (![0, -x] : Config 2 1) ∈ MDS 2 1 D := hmin _ (hstress (-x) (by simp [hxnorm]))
  refine ⟨fun _ ω => if ω then ![0, x] else ![0, -x], ![0, x], D,
    fun t ω => by cases ω <;> simpa using ‹_›, hmem0, ?_, ?_⟩
  · -- the pairwise distances are exactly right, so the hypothesis holds at every stage
    intro i j ε hε
    have hzero : ∀ ω : Bool,
        pairDistErr (if ω then ![0, x] else ![0, -x]) ![0, x] i j = 0 := by
      intro ω
      cases ω <;> fin_cases i <;> fin_cases j <;>
        simp [pairDistErr, pairDist]
    have hempty : ∀ _t : Nat,
        {ω : Bool | dist (pairDistErr (if ω then ![0, x] else ![0, -x])
          (![0, x] : Config 2 1) i j) 0 > ε} = (∅ : Set Bool) := by
      intro _t
      ext ω
      simp [hzero ω, not_lt.mpr hε.le]
    refine Filter.Tendsto.congr (fun t => ?_)
      (tendsto_const_nhds : Filter.Tendsto (fun _ : Nat => (0 : ENNReal)) Filter.atTop (𝓝 0))
    rw [hempty t, measure_empty]
  · -- yet no deterministic alignment sequence works
    intro W a hcon
    have h := hcon (1 / 2) (by norm_num)
    have hmem : ∀ t : Nat,
        true ∈ {ω : Bool | ∃ i, (1 / 2 : Real) <
            ‖(if ω then ![0, x] else ![0, -x] : Config 2 1) i
              - (W t ((![0, x] : Config 2 1) i) + a t)‖} ∨
        false ∈ {ω : Bool | ∃ i, (1 / 2 : Real) <
            ‖(if ω then ![0, x] else ![0, -x] : Config 2 1) i
              - (W t ((![0, x] : Config 2 1) i) + a t)‖} := by
      intro t
      by_contra hno
      push Not at hno
      obtain ⟨h1, h2⟩ := hno
      simp only [Set.mem_ofPred_eq, not_exists, not_lt] at h1 h2
      have e1' : ‖x - (W t x + a t)‖ ≤ 1 / 2 := by simpa using h1 1
      have e2' : ‖(-x) - (W t x + a t)‖ ≤ 1 / 2 := by simpa using h2 1
      have htri : ‖x - (-x)‖
          ≤ ‖x - (W t x + a t)‖ + ‖(W t x + a t) - (-x)‖ := by
        have hsum : (x - (W t x + a t)) + ((W t x + a t) - (-x)) = x - (-x) := by abel
        calc ‖x - (-x)‖ = ‖(x - (W t x + a t)) + ((W t x + a t) - (-x))‖ := by rw [hsum]
          _ ≤ _ := norm_add_le _ _
      have hrev : ‖(W t x + a t) - (-x)‖ = ‖(-x) - (W t x + a t)‖ := norm_sub_rev _ _
      have hxx : ‖x - (-x)‖ = 2 := by
        have hstep : x - (-x) = (2 : Real) • x := by rw [sub_neg_eq_add, two_smul]
        rw [hstep, norm_smul, hxnorm]
        simp
      rw [hxx, hrev] at htri
      linarith
    have hhalf : ∀ t : Nat, (1 / 2 : ENNReal) ≤ coinMeasure
        {ω : Bool | ∃ i, (1 / 2 : Real) <
          ‖(if ω then ![0, x] else ![0, -x] : Config 2 1) i
            - (W t ((![0, x] : Config 2 1) i) + a t)‖} :=
      fun t => coinMeasure_ge_half (hmem t)
    have hle : (1 / 2 : ENNReal) ≤ 0 :=
      ge_of_tendsto h (Filter.Eventually.of_forall hhalf)
    simp at hle

/--
**Theorem 5 for the empirical model distribution.**

The source's Theorem 5 composes its Theorem 4 rate with Lemma 2: under the trace-covariance
condition, the `L^p(P × P)` discrepancy between the estimated pairwise distances and the
continuous-MDS ones vanishes in probability.  This is that composition, with `P` the empirical
measure of the sampled models.

Every link is now a proved theorem rather than an assumed hypothesis:

* `Probability.dissimilarity_convergesInProbability_of_gamma` turns the source's
  `((1/m) ∑_j γ_ij)/r → 0` into convergence of the sample dissimilarities, with the number of
  queries growing with the replicate count;
* `hpop` is the source's Assumption 1, that the population dissimilarities approach the limiting
  ones, and the triangle inequality composes the two;
* `RawStress.mds_stability_inProbability_of_uniqueProfile` turns that into convergence of the
  estimates' pairwise distances -- with the profile-uniqueness premise whose necessity
  `ProfileNonuniqueness.no_fixed_limiting_profile` establishes;
* `ContinuousMDS.tendsto_measure_lpPairDistErr_gt` assembles the pairs into the `L^p`
  discrepancy, along the full sequence and uniformly in `p`.

What separates this from the printed theorem is that `P` is the empirical measure of the sampled
models rather than the population law they are drawn from -- the step the source attributes to
the cited continuous-MDS literature.
-/
theorem lp_consistency_of_gamma_empirical
    (P : Measure Ω) [IsProbabilityMeasure P]
    {n d q : Nat} [NeZero n] (m : Nat → Nat)
    (Xbar : ∀ r, Ω → Fin n → Mat (m r) q)
    (μpop : ∀ r, Fin n → Mat (m r) q)
    (DeltaInf : DisMat n)
    (γ : ∀ r, Fin n → Fin (m r) → Real)
    (hγnonneg : ∀ r i j, 0 ≤ γ r i j)
    (hint : ∀ r i, Integrable (fun ω => ‖Xbar r ω i - μpop r i‖ ^ 2) P)
    (hmoment : ∀ i, ∀ᶠ r in atTop, ∫ ω, ‖Xbar r ω i - μpop r i‖ ^ 2 ∂P
      ≤ (∑ i', ∑ j, γ r i' j) / (r : Real))
    (hγ : Tendsto (fun r => ((m r : Real))⁻¹ * (∑ i, ∑ j, γ r i j) / (r : Real))
      atTop (𝓝 0))
    -- Assumption 1: the population dissimilarities approach the limiting ones
    (hpop : Tendsto (fun r => frobSub (responseDist (μpop r)) DeltaInf) atTop (𝓝 0))
    (ψhat : Nat → Ω → Config n d)
    (hψhat : ∀ r ω, ψhat r ω ∈ MDS n d (responseDist (Xbar r ω)))
    (huniq : RawStress.UniquePairProfile n d DeltaInf) :
    ∃ ψ ∈ MDS n d DeltaInf, ∀ p : Real, 1 ≤ p → ∀ ε : Real, 0 < ε →
      Tendsto (fun r => P {ω | ε < ((n : Real))⁻¹ * ((n : Real))⁻¹ *
        ∑ i, ∑ j, |‖ψhat r ω i - ψhat r ω j‖ - ‖ψ i - ψ j‖| ^ p}) atTop (𝓝 0) := by
  classical
  -- (1) the sample dissimilarities reach the limiting matrix
  have hsample := Probability.dissimilarity_convergesInProbability_of_gamma P m Xbar μpop γ
    hγnonneg hint hmoment hγ
  have hD : ConvergesInProbabilityZero P
      (fun r ω => frobSub (responseDist (Xbar r ω)) DeltaInf) := by
    intro ε hε
    have hhalf : (0 : Real) < ε / 2 := by linarith
    have hpop' : ∀ᶠ r in atTop, frobSub (responseDist (μpop r)) DeltaInf ≤ ε / 2 := by
      have := hpop.eventually_lt_const hhalf
      exact this.mono fun r hr => hr.le
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hsample (ε / 2) hhalf)
      (Filter.Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [hpop'] with r hr
    refine measure_mono fun ω hω => ?_
    simp only [Set.mem_ofPred_eq, gt_iff_lt, Real.dist_eq, sub_zero,
      abs_of_nonneg (frobSub_nonneg _ _)] at hω ⊢
    by_contra hcon
    push Not at hcon
    have := frobSub_triangle (responseDist (Xbar r ω)) (responseDist (μpop r)) DeltaInf
    linarith
  -- (2) the estimates' pairwise distances reach a fixed minimizer's
  obtain ⟨ψ, hψmem, hψconv⟩ :=
    RawStress.mds_stability_inProbability_of_uniqueProfile P
      (fun r ω => responseDist (Xbar r ω)) DeltaInf ψhat hψhat huniq hD
  refine ⟨ψ, hψmem, fun p hp ε hε => ?_⟩
  -- (3) assemble the pairs into the `L^p` discrepancy
  have hconv : ∀ i j : Fin n, ∀ δ > (0 : Real), Tendsto
      (fun r => P {ω | δ < |‖ψhat r ω ((id : Fin n → Fin n) i)
        - ψhat r ω ((id : Fin n → Fin n) j)‖
        - ‖ψ ((id : Fin n → Fin n) i) - ψ ((id : Fin n → Fin n) j)‖|}) atTop (𝓝 0) := by
    intro i j δ hδ
    refine (hψconv i j δ hδ).congr fun r => ?_
    congr 1
    ext ω
    simp [pairDistErr, pairDist, Real.dist_eq, abs_abs]
  have hlp := ContinuousMDS.tendsto_measure_lpPairDistErr_gt (M := Fin n) P (κ := Fin n)
    (d := d) p hp (id : Fin n → Fin n) ψhat ψ
    (fun u ω => measurable_of_countable _) (measurable_of_countable _) hconv (ε := ε) hε
  refine hlp.congr fun r => ?_
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq]
  rw [ContinuousMDS.lpPairDistErr_empiricalPopulation (M := Fin n) d (by linarith : (0:Real) ≤ p)
    (id : Fin n → Fin n) (ψhat r ω) ψ (measurable_of_countable _) (measurable_of_countable _)]
  simp

/--
**Theorem 5 from Assumption 2**, for the empirical model distribution.

The same composition as `lp_consistency_of_gamma_empirical`, with the source's Assumption 2
supplied as a structure rather than its consequence as a hypothesis.  The limiting dissimilarity
matrix is the one the assumption induces, `Delta^(infinity)(phi_i, phi_i') = ||phi_i - phi_i'||`.
-/
theorem lp_consistency_of_gamma_ambientLimit
    (P : Measure Ω) [IsProbabilityMeasure P]
    {n d qamb pdim : Nat} [NeZero n] (m : Nat → Nat)
    (Xbar : ∀ r, Ω → Fin n → Mat (m r) pdim)
    (μpop : ∀ r, Fin n → Mat (m r) pdim)
    (H2 : GrowingModels.AmbientModelLimit n qamb m μpop)
    (γ : ∀ r, Fin n → Fin (m r) → Real)
    (hγnonneg : ∀ r i j, 0 ≤ γ r i j)
    (hint : ∀ r i, Integrable (fun ω => ‖Xbar r ω i - μpop r i‖ ^ 2) P)
    (hmoment : ∀ i, ∀ᶠ r in atTop, ∫ ω, ‖Xbar r ω i - μpop r i‖ ^ 2 ∂P
      ≤ (∑ i', ∑ j, γ r i' j) / (r : Real))
    (hγ : Tendsto (fun r => ((m r : Real))⁻¹ * (∑ i, ∑ j, γ r i j) / (r : Real))
      atTop (𝓝 0))
    (ψhat : Nat → Ω → Config n d)
    (hψhat : ∀ r ω, ψhat r ω ∈ MDS n d (responseDist (Xbar r ω)))
    (huniq : RawStress.UniquePairProfile n d
      (GrowingModels.limitDissimilarity H2.latent)) :
    ∃ ψ ∈ MDS n d (GrowingModels.limitDissimilarity H2.latent),
      ∀ p : Real, 1 ≤ p → ∀ ε : Real, 0 < ε →
        Tendsto (fun r => P {ω | ε < ((n : Real))⁻¹ * ((n : Real))⁻¹ *
          ∑ i, ∑ j, |‖ψhat r ω i - ψhat r ω j‖ - ‖ψ i - ψ j‖| ^ p}) atTop (𝓝 0) :=
  lp_consistency_of_gamma_empirical P m Xbar μpop
    (GrowingModels.limitDissimilarity H2.latent) γ hγnonneg hint hmoment hγ
    H2.tendsto_frobSub ψhat hψhat huniq

/-! ### The identifiability premise is necessary

`tendsto_outOfSampleExtension` and `tendsto_argmin_of_tendsto_of_equiLipschitz` both assume the
limiting one-point stress has a *unique* minimizer.  That premise cannot be dropped, for the same
reason `RawStress.UniquePairProfile` cannot: the minimizer set may carry more than one point, and
then different admissible selections converge to different limits, so no statement of the form
"the minimizers converge to `v'`" can hold.

The witness is two reference points at distance two with target dissimilarity two from each.  A
position matching both exactly does not exist, and the stress is minimized at three separate
places. -/

/-- The two-point reference embedding of the witness: `+1` and `-1` on a fair coin. -/
noncomputable def twoPointEmbedding : Bool → Rvec 1 :=
  fun b => EuclideanSpace.single 0 (if b then (1 : Real) else -1)

/-- Its population one-point stress at target dissimilarity `2`, in closed form. -/
theorem continuousPointStress_twoPoint (v : Rvec 1) :
    ContinuousMDS.continuousPointStress 1 coinMeasure twoPointEmbedding
      (fun _ => (2 : Real)) v
      = (1 / 2) * (|v 0 - 1| - 2) ^ 2 + (1 / 2) * (|v 0 + 1| - 2) ^ 2 := by
  rw [ContinuousMDS.continuousPointStress, integral_coinMeasure]
  simp only [twoPointEmbedding, norm_sub_one_dim, EuclideanSpace.single_apply]
  norm_num

/-- The population one-point stress of the witness is at least `1` everywhere. -/
theorem one_le_continuousPointStress_twoPoint (v : Rvec 1) :
    (1 : Real) ≤ ContinuousMDS.continuousPointStress 1 coinMeasure twoPointEmbedding
      (fun _ => (2 : Real)) v := by
  rw [continuousPointStress_twoPoint]
  set t : Real := v 0 with ht
  rcases le_or_gt 1 t with h1 | h1
  · rw [abs_of_nonneg (by linarith : (0:Real) ≤ t - 1),
      abs_of_nonneg (by linarith : (0:Real) ≤ t + 1)]
    nlinarith [sq_nonneg (t - 2)]
  · rcases le_or_gt t (-1) with h2 | h2
    · rw [abs_of_nonpos (by linarith : t - 1 ≤ (0:Real)),
        abs_of_nonpos (by linarith : t + 1 ≤ (0:Real))]
      nlinarith [sq_nonneg (t + 2)]
    · rw [abs_of_nonpos (by linarith : t - 1 ≤ (0:Real)),
        abs_of_nonneg (by linarith : (0:Real) ≤ t + 1)]
      nlinarith [sq_nonneg t]

/-- Both `0` and the point at distance two from it attain that value, so the minimizer is not
unique. -/
theorem continuousPointStress_twoPoint_eq_one :
    ContinuousMDS.continuousPointStress 1 coinMeasure twoPointEmbedding
        (fun _ => (2 : Real)) 0 = 1 ∧
    ContinuousMDS.continuousPointStress 1 coinMeasure twoPointEmbedding
        (fun _ => (2 : Real)) (EuclideanSpace.single 0 (2 : Real)) = 1 := by
  constructor <;>
    · rw [continuousPointStress_twoPoint]
      simp [EuclideanSpace.single_apply]
      norm_num

/--
**The identifiability premise cannot be dropped.**

There are population data whose one-point stress has two distinct minimizers.  Constant
sequences at each of them minimize the stress at every stage and converge, to different limits,
so no theorem concluding that minimizers converge to a single point can hold without a
uniqueness premise.
-/
theorem not_unique_min_continuousPointStress :
    ∃ (V W : Nat → Rvec 1) (v' w' : Rvec 1),
      v' ≠ w' ∧
      (∀ n, ∀ u : Rvec 1,
        ContinuousMDS.continuousPointStress 1 coinMeasure twoPointEmbedding
            (fun _ => (2 : Real)) (V n)
          ≤ ContinuousMDS.continuousPointStress 1 coinMeasure twoPointEmbedding
            (fun _ => (2 : Real)) u) ∧
      (∀ n, ∀ u : Rvec 1,
        ContinuousMDS.continuousPointStress 1 coinMeasure twoPointEmbedding
            (fun _ => (2 : Real)) (W n)
          ≤ ContinuousMDS.continuousPointStress 1 coinMeasure twoPointEmbedding
            (fun _ => (2 : Real)) u) ∧
      Tendsto V atTop (𝓝 v') ∧ Tendsto W atTop (𝓝 w') := by
  obtain ⟨h0, h2⟩ := continuousPointStress_twoPoint_eq_one
  refine ⟨fun _ => 0, fun _ => EuclideanSpace.single 0 (2 : Real), 0,
    EuclideanSpace.single 0 (2 : Real), ?_, fun n u => ?_, fun n u => ?_,
    tendsto_const_nhds, tendsto_const_nhds⟩
  · intro hcon
    have := congrArg (fun x : Rvec 1 => x 0) hcon
    simp [EuclideanSpace.single_apply] at this
  · rw [h0]; exact one_le_continuousPointStress_twoPoint u
  · rw [h2]; exact one_le_continuousPointStress_twoPoint u

/-! ## Theorem 5 over the population law

`lp_consistency_of_gamma_empirical` proves Theorem 5 with `P` the empirical measure of the
sampled models.  The printed theorem draws the models from a population law `P` and integrates
against `P × P`.  What follows is that statement.

The composition the source asserts is "Theorem 4, then Lemma 2", and the two halves are stated on
different footings: Theorem 4 fixes the models and randomises the replicates, while Lemma 2 draws
the models.  Passing between them needs three things, all of them now proved rather than assumed:

* the conditional bad-event probabilities integrate over the model draw by domination, so no
  bound uniform over the model population is required
  (`Probability.pairwise_dissimilarity_convergesInProbability_of_gamma`);
* a fresh query paired with a drawn reference, and two distinct drawn references, have the same
  law `P × P`, so Theorem 4's conclusion is literally Lemma 2's hypothesis
  (`ContinuousMDS.tendsto_measure_absPairErr_query_of_sampled`, and the two `measure_absPairErr_*`
  identities behind it);
* the per-index errors have a common mean because the source's `D` is a statistic of the two
  models involved (`ContinuousMDS.integral_absPairErr_eq_of_dissimilarityFactors`), which is what
  the identically-distributed hypothesis of Lemma 2 asked for.

The one place where this is a repair rather than a transcription is the sampling model: a model
is drawn as a complete object -- its latent vector `phi` *and* the law of its responses, here the
kernel `κ` -- rather than only its latent vector, which is all the printed lemma says.  That
reading is forced by the printed conclusion, whose integrand depends on the estimate and hence on
the response data; and it is what makes `hid` a theorem instead of an assumption.
-/

omit [MeasurableSpace Ω] in
private theorem tendsto_measure_ge_of_ae_tendsto {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f : Nat → α → Real) (g : α → Real)
    (hf : ∀ r, AEStronglyMeasurable (f r) μ)
    (hfg : ∀ᵐ x ∂μ, Tendsto (fun r => f r x) atTop (𝓝 (g x)))
    {ε : Real} (hε : 0 < ε) :
    Tendsto (fun r => μ {x | ε ≤ |f r x - g x|}) atTop (𝓝 0) := by
  have h := tendstoInMeasure_of_tendsto_ae hf hfg (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε)
  refine h.congr fun r => congrArg _ ?_
  ext x
  simp [edist_dist, Real.dist_eq, ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)]

/--
**Theorem 5 over the population law.**

A model is a point of `Lam`; its latent representation is `phi`, its stage-`r` response matrix is
`Xbar` and its population means are `mu`, and the law of its response data given the model is the
Markov kernel `κ`.  Models are drawn independently from `Pmod`, so a model with its data is drawn
from `P = Pmod ⊗ₘ κ`, and the `L^p(P × P)` discrepancy of the printed conclusion is
`ContinuousMDS.lpPairDistErr`.

The hypotheses are the source's: the second-moment bound with the model's own `∑_j γ_ij` and the
`o(r)` rate for it, both read almost surely in the model draw (`hint`, `hmoment`, `hγ`);
Assumption 2 (`hA2`); and the standing structural hypotheses of Lemma 2 -- bounded dissimilarities
and a unique minimizer of the limiting one-point stress -- which the source attributes to its
reference.  Nothing uniform over the model population appears.
-/
theorem lp_consistency_of_gamma_population
    {Lam : Type} [MeasurableSpace Lam]
    (Pmod : Measure Lam) [IsProbabilityMeasure Pmod]
    (κ : ProbabilityTheory.Kernel Lam Ω) [ProbabilityTheory.IsMarkovKernel κ]
    {d qamb pdim : Nat} {p : Real} (hp : 0 < p) (m : Nat → Nat)
    (Xbar : ∀ r, Lam × Ω → Mat (m r) pdim) (mu : ∀ r, Lam → Mat (m r) pdim)
    (phi : Lam → Rvec qamb) (S : Lam → Nat → Real)
    (hmeasX : ∀ r, Measurable (Xbar r)) (hmeasMu : ∀ r, Measurable (mu r))
    (hmeasPhi : Measurable phi)
    (hS : ∀ᵐ l ∂Pmod, ∀ r, 0 ≤ S l r)
    (hint : ∀ᵐ l ∂Pmod, ∀ r, Integrable (fun ω => ‖Xbar r (l, ω) - mu r l‖ ^ 2) (κ l))
    (hmoment : ∀ᵐ l ∂Pmod, ∀ᶠ r in atTop,
      ∫ ω, ‖Xbar r (l, ω) - mu r l‖ ^ 2 ∂(κ l) ≤ S l r / (r : Real))
    (hγ : ∀ᵐ l ∂Pmod,
      Tendsto (fun r => ((m r : Real))⁻¹ * S l r / (r : Real)) atTop (𝓝 0))
    (hA2 : ∀ᵐ z ∂((Pmod ⊗ₘ κ).prod (Pmod ⊗ₘ κ)),
      Tendsto (fun r => ((m r : Real))⁻¹ * ‖mu r z.1.1 - mu r z.2.1‖) atTop
        (𝓝 ‖phi z.1.1 - phi z.2.1‖))
    (χ : Lam × Ω → Rvec d) {K : Real} (hχ : Measurable χ) (hχb : ∀ x, ‖χ x‖ ≤ K)
    (hΔb : ∀ x y : Lam × Ω, |‖phi x.1 - phi y.1‖| ≤ K)
    (hGb : ∀ (r : Nat) (x y : Lam × Ω),
      |((m r : Real))⁻¹ * ‖Xbar r x - Xbar r y‖| ≤ K)
    (χlim : Lam × Ω → Rvec d)
    (hχlimmin : ∀ x : Lam × Ω, ∀ w : Rvec d,
      ContinuousMDS.continuousPointStress d (Pmod ⊗ₘ κ) χ (fun y => ‖phi x.1 - phi y.1‖) (χlim x)
        ≤ ContinuousMDS.continuousPointStress d (Pmod ⊗ₘ κ) χ
            (fun y => ‖phi x.1 - phi y.1‖) w)
    (hunique : ∀ x : Lam × Ω, ∀ w : Rvec d,
      (∀ w' : Rvec d,
        ContinuousMDS.continuousPointStress d (Pmod ⊗ₘ κ) χ (fun y => ‖phi x.1 - phi y.1‖) w
          ≤ ContinuousMDS.continuousPointStress d (Pmod ⊗ₘ κ) χ
              (fun y => ‖phi x.1 - phi y.1‖) w') →
      w = χlim x)
    (Ψ : Nat → (Nat → Lam × Ω) → Lam × Ω → Rvec d)
    (hΨmin : ∀ (r : Nat) (φ : Nat → Lam × Ω) (x : Lam × Ω), ∀ w : Rvec d,
      ContinuousMDS.pointStress (fun i : Fin (r + 1) => χ (φ i))
          (fun i : Fin (r + 1) => ((m r : Real))⁻¹ * ‖Xbar r x - Xbar r (φ i)‖) (Ψ r φ x)
        ≤ ContinuousMDS.pointStress (fun i : Fin (r + 1) => χ (φ i))
            (fun i : Fin (r + 1) => ((m r : Real))⁻¹ * ‖Xbar r x - Xbar r (φ i)‖) w)
    (hmeasΨ : ∀ r, Measurable fun z : (Nat → Lam × Ω) × ((Lam × Ω) × (Lam × Ω)) =>
      ContinuousMDS.pairDiscrepancy d p (Ψ r z.1) χlim z.2) :
    ∃ ns : Nat → Nat, StrictMono ns ∧ ∀ ε : Real, 0 < ε →
      Tendsto (fun u => (Measure.infinitePi fun _ : Nat => (Pmod ⊗ₘ κ))
        {φ | ε < ContinuousMDS.lpPairDistErr d (Pmod ⊗ₘ κ) p (Ψ (ns u) φ) χlim})
        atTop (𝓝 0) := by
  classical
  set P : Measure (Lam × Ω) := Pmod ⊗ₘ κ with hP
  set Δ : (Lam × Ω) → (Lam × Ω) → Real := fun x y => ‖phi x.1 - phi y.1‖ with hΔdef
  set G : Nat → (Lam × Ω) → (Lam × Ω) → Real :=
    fun r x y => ((m r : Real))⁻¹ * ‖Xbar r x - Xbar r y‖ with hGdef
  have hΔ2 : Measurable fun q : (Lam × Ω) × (Lam × Ω) => Δ q.1 q.2 := by
    simp only [hΔdef]
    fun_prop
  have hΔmeas : ∀ x, Measurable (Δ x) := by
    intro x
    simp only [hΔdef]
    fun_prop
  have hG : ∀ r, Measurable fun q : (Lam × Ω) × (Lam × Ω) => G r q.1 q.2 := by
    intro r
    simp only [hGdef]
    exact (((hmeasX r).comp measurable_fst).sub ((hmeasX r).comp measurable_snd)).norm.const_mul _
  -- Theorem 4 for the drawn pair, with no uniformity over the model population
  have hpair := Probability.pairwise_dissimilarity_convergesInProbability_of_gamma
    Pmod κ m Xbar mu S hmeasX hmeasMu hS hint hmoment hγ
  -- Assumption 2, as convergence in probability of the population dissimilarities
  have hA2' : ∀ δ : Real, 0 < δ → Tendsto (fun r => (P.prod P)
      {z : (Lam × Ω) × (Lam × Ω) | δ ≤ |((m r : Real))⁻¹ * ‖mu r z.1.1 - mu r z.2.1‖
        - ‖phi z.1.1 - phi z.2.1‖|}) atTop (𝓝 0) := by
    intro δ hδ
    refine tendsto_measure_ge_of_ae_tendsto (P.prod P) _ _ (fun r => ?_) hA2 hδ
    exact (((hmeasMu r).comp (measurable_fst.comp measurable_fst)).sub
      ((hmeasMu r).comp (measurable_fst.comp measurable_snd))).norm.const_mul
        _ |>.aestronglyMeasurable
  -- the two halves compose by the triangle inequality
  have hcomb : ∀ δ : Real, 0 < δ → Tendsto (fun r => (P.prod P)
      {q : (Lam × Ω) × (Lam × Ω) | δ ≤ |G r q.1 q.2 - Δ q.1 q.2|}) atTop (𝓝 0) := by
    intro δ hδ
    have hhalf : (0 : Real) < δ / 2 := by linarith
    have hsub : ∀ r : Nat,
        {q : (Lam × Ω) × (Lam × Ω) | δ ≤ |G r q.1 q.2 - Δ q.1 q.2|}
          ⊆ {q : (Lam × Ω) × (Lam × Ω) | dist (((m r : Real))⁻¹ * ‖Xbar r q.1 - Xbar r q.2‖
                - ((m r : Real))⁻¹ * ‖mu r q.1.1 - mu r q.2.1‖) (0 : Real) > δ / 2}
            ∪ {q : (Lam × Ω) × (Lam × Ω) | δ / 2 ≤ |((m r : Real))⁻¹ * ‖mu r q.1.1 - mu r q.2.1‖
                - ‖phi q.1.1 - phi q.2.1‖|} := by
      intro r q hq
      by_contra hcon
      simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt, not_le,
        Real.dist_eq, sub_zero] at hcon
      simp only [Set.mem_ofPred_eq, hGdef, hΔdef] at hq
      have habs : |((m r : Real))⁻¹ * ‖Xbar r q.1 - Xbar r q.2‖ - ‖phi q.1.1 - phi q.2.1‖|
          ≤ |((m r : Real))⁻¹ * ‖Xbar r q.1 - Xbar r q.2‖
              - ((m r : Real))⁻¹ * ‖mu r q.1.1 - mu r q.2.1‖|
            + |((m r : Real))⁻¹ * ‖mu r q.1.1 - mu r q.2.1‖ - ‖phi q.1.1 - phi q.2.1‖| := by
        have : ((m r : Real))⁻¹ * ‖Xbar r q.1 - Xbar r q.2‖ - ‖phi q.1.1 - phi q.2.1‖
            = (((m r : Real))⁻¹ * ‖Xbar r q.1 - Xbar r q.2‖
                - ((m r : Real))⁻¹ * ‖mu r q.1.1 - mu r q.2.1‖)
              + (((m r : Real))⁻¹ * ‖mu r q.1.1 - mu r q.2.1‖
                - ‖phi q.1.1 - phi q.2.1‖) := by ring
        rw [this]
        exact abs_add_le _ _
      linarith [hcon.1, hcon.2]
    have hsum : Tendsto (fun r : Nat =>
        (P.prod P) {q : (Lam × Ω) × (Lam × Ω) |
            dist (((m r : Real))⁻¹ * ‖Xbar r q.1 - Xbar r q.2‖
              - ((m r : Real))⁻¹ * ‖mu r q.1.1 - mu r q.2.1‖) (0 : Real) > δ / 2}
          + (P.prod P) {q : (Lam × Ω) × (Lam × Ω) |
              δ / 2 ≤ |((m r : Real))⁻¹ * ‖mu r q.1.1 - mu r q.2.1‖
                - ‖phi q.1.1 - phi q.2.1‖|}) atTop (𝓝 0) := by
      simpa using (hpair (δ / 2) hhalf).add (hA2' (δ / 2) hhalf)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun r => bot_le) (fun r => ?_)
    exact le_trans (measure_mono (hsub r)) (measure_union_le _ _)
  -- Lemma 2, with the identically-distributed hypothesis derived from the factorization
  refine ContinuousMDS.exists_subseq_tendsto_measure_lpPairDistErr_of_pairwise P hp Δ χ
    hχ hΔmeas hΔ2 hχb (fun x y => hΔb x y) χlim hχlimmin hunique G hG hGb
    (fun r φ x i => G r x (φ i)) (fun _ _ _ _ => rfl) ?_ Ψ hΨmin hmeasΨ
  -- the hypothesis of Lemma 2 is the conclusion of Theorem 4, transported across the pair law
  intro δ hδ
  have hmeasure : ∀ r : Nat, (P.prod (Measure.infinitePi fun _ : Nat => P))
      {z : (Lam × Ω) × (Nat → Lam × Ω) | δ ≤ |G r z.1 (z.2 0) - Δ z.1 (z.2 0)|}
        = (P.prod P) {q : (Lam × Ω) × (Lam × Ω) | δ ≤ |G r q.1 q.2 - Δ q.1 q.2|} := fun r =>
    ContinuousMDS.measure_absPairErr_query_eq P hG hΔ2 (fun r φ x i => G r x (φ i))
      (fun _ _ _ _ => rfl) r 0 δ
  have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hcomb δ hδ)
  simp only [Function.comp_def, ENNReal.toReal_zero] at this
  exact this.congr fun r => by rw [← hmeasure r]

/--
**Theorem 5 over the population law, from the source's sampling model.**

`lp_consistency_of_gamma_population` takes the second-moment bound as a hypothesis.  Here it is
discharged: what is given is the source's sampling model -- for each drawn model, each query, and
each stage, `r` replicates that are independent for that query and have trace-covariance
`γ_ij` -- together with the printed rate condition, read for almost every drawn model.  Nothing
between the replicate assumptions and the `L^p` conclusion is assumed.

Independence is assumed only across the replicates of a fixed query of a fixed model, which is
what `g(f_i(q_j)_k) ~iid F_ij` says; the responses to different queries are never asked to be
independent of one another.
-/
theorem lp_consistency_of_replicates_population
    {Lam : Type} [MeasurableSpace Lam]
    (Pmod : Measure Lam) [IsProbabilityMeasure Pmod]
    (κ : ProbabilityTheory.Kernel Lam Ω) [ProbabilityTheory.IsMarkovKernel κ]
    {d qamb pdim : Nat} {p : Real} (hp : 0 < p) (m : Nat → Nat)
    (Y : ∀ r : Nat, Lam → Fin (m r) → Fin r → Ω → Rvec pdim)
    (muq : ∀ r : Nat, Lam → Fin (m r) → Rvec pdim)
    (γ : ∀ r : Nat, Lam → Fin (m r) → Real)
    (Xbar : ∀ r, Lam × Ω → Mat (m r) pdim) (mu : ∀ r, Lam → Mat (m r) pdim)
    (phi : Lam → Rvec qamb)
    (hmeasX : ∀ r, Measurable (Xbar r)) (hmeasMu : ∀ r, Measurable (mu r))
    (hmeasPhi : Measurable phi)
    (hXbar : ∀ r l ω (j : Fin (m r)) (c : Fin pdim),
      Xbar r (l, ω) (j, c) = ((r : Real)⁻¹ • ∑ t, Y r l j t ω) c)
    (hmu : ∀ r l (j : Fin (m r)) (c : Fin pdim), mu r l (j, c) = muq r l j c)
    (hγnonneg : ∀ r l j, 0 ≤ γ r l j)
    (hL2 : ∀ᵐ l ∂Pmod, ∀ r j t, MemLp (Y r l j t) 2 (κ l))
    (hmean : ∀ᵐ l ∂Pmod, ∀ r j t (c : Fin pdim), ∫ ω, Y r l j t ω c ∂(κ l) = muq r l j c)
    (hindep : ∀ᵐ l ∂Pmod, ∀ r (j : Fin (m r)), Set.Pairwise (Set.univ : Set (Fin r))
      fun t t' => ProbabilityTheory.IndepFun (Y r l j t) (Y r l j t') (κ l))
    (hγbound : ∀ᵐ l ∂Pmod, ∀ r j t,
      ∫ ω, ‖Y r l j t ω - muq r l j‖ ^ 2 ∂(κ l) ≤ γ r l j)
    (hintcoord : ∀ᵐ l ∂Pmod, ∀ r (q : Fin (m r) × Fin pdim),
      Integrable (fun ω => (Xbar r (l, ω) q - mu r l q) ^ 2) (κ l))
    (hγrate : ∀ᵐ l ∂Pmod,
      Tendsto (fun r => ((m r : Real))⁻¹ * (∑ j, γ r l j) / (r : Real)) atTop (𝓝 0))
    (hA2 : ∀ᵐ z ∂((Pmod ⊗ₘ κ).prod (Pmod ⊗ₘ κ)),
      Tendsto (fun r => ((m r : Real))⁻¹ * ‖mu r z.1.1 - mu r z.2.1‖) atTop
        (𝓝 ‖phi z.1.1 - phi z.2.1‖))
    (χ : Lam × Ω → Rvec d) {K : Real} (hχ : Measurable χ) (hχb : ∀ x, ‖χ x‖ ≤ K)
    (hΔb : ∀ x y : Lam × Ω, |‖phi x.1 - phi y.1‖| ≤ K)
    (hGb : ∀ (r : Nat) (x y : Lam × Ω),
      |((m r : Real))⁻¹ * ‖Xbar r x - Xbar r y‖| ≤ K)
    (χlim : Lam × Ω → Rvec d)
    (hχlimmin : ∀ x : Lam × Ω, ∀ w : Rvec d,
      ContinuousMDS.continuousPointStress d (Pmod ⊗ₘ κ) χ (fun y => ‖phi x.1 - phi y.1‖) (χlim x)
        ≤ ContinuousMDS.continuousPointStress d (Pmod ⊗ₘ κ) χ
            (fun y => ‖phi x.1 - phi y.1‖) w)
    (hunique : ∀ x : Lam × Ω, ∀ w : Rvec d,
      (∀ w' : Rvec d,
        ContinuousMDS.continuousPointStress d (Pmod ⊗ₘ κ) χ (fun y => ‖phi x.1 - phi y.1‖) w
          ≤ ContinuousMDS.continuousPointStress d (Pmod ⊗ₘ κ) χ
              (fun y => ‖phi x.1 - phi y.1‖) w') →
      w = χlim x)
    (Ψ : Nat → (Nat → Lam × Ω) → Lam × Ω → Rvec d)
    (hΨmin : ∀ (r : Nat) (φ : Nat → Lam × Ω) (x : Lam × Ω), ∀ w : Rvec d,
      ContinuousMDS.pointStress (fun i : Fin (r + 1) => χ (φ i))
          (fun i : Fin (r + 1) => ((m r : Real))⁻¹ * ‖Xbar r x - Xbar r (φ i)‖) (Ψ r φ x)
        ≤ ContinuousMDS.pointStress (fun i : Fin (r + 1) => χ (φ i))
            (fun i : Fin (r + 1) => ((m r : Real))⁻¹ * ‖Xbar r x - Xbar r (φ i)‖) w)
    (hmeasΨ : ∀ r, Measurable fun z : (Nat → Lam × Ω) × ((Lam × Ω) × (Lam × Ω)) =>
      ContinuousMDS.pairDiscrepancy d p (Ψ r z.1) χlim z.2) :
    ∃ ns : Nat → Nat, StrictMono ns ∧ ∀ ε : Real, 0 < ε →
      Tendsto (fun u => (Measure.infinitePi fun _ : Nat => (Pmod ⊗ₘ κ))
        {φ | ε < ContinuousMDS.lpPairDistErr d (Pmod ⊗ₘ κ) p (Ψ (ns u) φ) χlim})
        atTop (𝓝 0) := by
  refine lp_consistency_of_gamma_population Pmod κ hp m Xbar mu phi
    (fun l r => ∑ j, γ r l j) hmeasX hmeasMu hmeasPhi
    (Filter.Eventually.of_forall fun l r => Finset.sum_nonneg fun j _ => hγnonneg r l j)
    ?_ ?_ hγrate hA2 χ hχ hχb hΔb hGb χlim hχlimmin hunique Ψ hΨmin hmeasΨ
  · -- integrability of the Frobenius error, from the coordinates
    filter_upwards [hintcoord] with l hl r
    exact Acharyya2024.SecondMoment.integrable_norm_sq_of_coord (κ l)
      (fun ω => Xbar r (l, ω)) (mu r l) (hl r)
  · -- Appendix A.2 for the drawn model, row by row over its queries
    filter_upwards [hL2, hmean, hindep, hγbound, hintcoord]
      with l hL2l hmeanl hindepl hγboundl hintcoordl
    exact Probability.eventually_integral_norm_sq_le_sum_gamma (κ l) m (fun r => Y r l)
      (fun r => muq r l) (fun r => γ r l) (fun r ω => Xbar r (l, ω)) (fun r => mu r l)
      (fun r ω => hXbar r l ω) (fun r => hmu r l) (fun r => hL2l r) (fun r => hmeanl r)
      (fun r => hindepl r) (fun r => hγboundl r) (fun r => hintcoordl r)


end Acharyya2024.Consistency

/-
Second-moment (variance/trace) algebra for the iid sample mean, supplying the
hypothesis that the probabilistic step of

Acharyya, Trosset, Priebe, Helm.
"Consistent estimation of generative model representations in the data kernel
perspective space"
arXiv:2409.17308, Appendix A.2 (and the finite-sample companion
arXiv:2511.08307, Theorem 1) consume.

The downstream concentration theorem
`Acharyya2024.Probability.dissimilarity_convergesInProbability_of_secondMoment`
needs a bound `∫ ‖X̄(r)ᵢ − μᵢ‖² ∂P ≤ v r` with `v r → 0`.  For an iid (or merely
pairwise-independent, identically-centered, square-integrable) sample
`X₀, …, X_{r-1}` of `EuclideanSpace ℝ ι`-valued responses with mean `μ`, the
paper establishes this via the elementary variance identity

  E ‖(1/r) Σₖ Xₖ − μ‖² = (1/r) · E ‖X − μ‖²    ("trace(Σ)/r" in paper notation),

where `E ‖X − μ‖² = trace(cov X)`.  This file proves that identity (and the
additive generalization that does not assume identical distribution) and the
`≤ γ/r` bound the Acharyya chain actually consumes.

This file is paper-agnostic variance algebra: a plausible Mathlib contribution
candidate near `Mathlib/Probability/Moments/Variance.lean`.  The scalar engine is
Mathlib's `ProbabilityTheory.IndepFun.variance_sum`; the work here is the
coordinatewise reduction on `EuclideanSpace`.

No added axioms, no open proof obligations.
-/

import Mathlib
import ForTauCeti.Probability.Moments.SampleMean

open scoped BigOperators Topology
open Filter MeasureTheory ProbabilityTheory

namespace Acharyya2024.SecondMoment

variable {Ω : Type} [MeasurableSpace Ω]

/-- Coordinate-wise common mean upgrades to a Bochner common mean for an
integrable `EuclideanSpace`-valued sample.  Used to feed the coordinate-mean
paper statements into the Mathlib-staged Bochner-mean theorems.

Internal helper, not stated in the paper: it merely says that if every
coordinate of the (vector-valued) expectation equals `μ c`, then the
vector-valued expectation equals `μ`. -/
private theorem bochner_mean_of_coord
    (P : Measure Ω) {ι : Type} [Fintype ι]
    (Y : Ω → EuclideanSpace Real ι) (μ : EuclideanSpace Real ι)
    (hint : Integrable Y P)                      -- integrability (extra, implicit in paper)
    (hmean : ∀ c, ∫ ω, Y ω c ∂P = μ c) :         -- each coordinate mean equals μ c
    -- Conclusion: the vector-valued (Bochner) expectation of Y equals μ.
    ∫ ω, Y ω ∂P = μ := by
  ext c
  have h : (EuclideanSpace.proj c : EuclideanSpace Real ι →L[Real] Real) (∫ ω, Y ω ∂P)
      = ∫ ω, Y ω c ∂P :=
    (ContinuousLinearMap.integral_comp_comm _ hint).symm
  rw [hmean c] at h
  exact h

/--
**Main second-moment identity (additive form).**

Let `X : Fin r → Ω → EuclideanSpace ℝ ι` be pairwise-independent,
square-integrable response vectors with common mean `μ : EuclideanSpace ℝ ι`
(each coordinate `∫ X k ω c = μ c`).  Then the mean-squared error of the sample
mean equals `r⁻²` times the sum of the individual mean-squared errors:

  ∫ ‖r⁻¹ Σₖ Xₖ − μ‖² ∂P = r⁻² Σₖ ∫ ‖Xₖ − μ‖² ∂P.

Only pairwise independence and identical centring are needed (not identical
distribution); the cross terms vanish by independence.  The proof upgrades the
coordinate means to a Bochner mean (`bochner_mean_of_coord`) and applies the
Mathlib-staged `TauCeti.integral_norm_sq_average_sub_eq_sum`.

PAPER CORRESPONDENCE: the additive form behind the paper's variance computation
`E‖(X̄_i)_j· − (μ_i)_j·‖² = trace(cov[(X̄_i)_j·]) = γ_ij/r` (Appendix A.2). This
generalizes the paper, which assumes iid, to merely pairwise independence with a
common mean.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem integral_norm_sq_sampleMean_sub_mean_eq_sum
    (P : Measure Ω) [IsProbabilityMeasure P]   -- probability measure (total mass 1)
    {ι : Type} [Fintype ι]                      -- finite coordinate index (response dimension)
    {r : Nat} (hr : 0 < r)                      -- positive sample size r
    (X : Fin r → Ω → EuclideanSpace Real ι)     -- iid-style sample X₀,…,X_{r-1}
    (μ : EuclideanSpace Real ι)                 -- common mean
    (hL2 : ∀ k, MemLp (X k) 2 P)                -- finite second moment (square-integrable); extra, implicit in paper
    (hmean : ∀ k (c : ι), ∫ ω, X k ω c ∂P = μ c)  -- identical centring: each sample has mean μ
    (hindep : Set.Pairwise (Set.univ : Set (Fin r))
      fun i j => IndepFun (X i) (X j) P) :       -- pairwise independence (paper assumes iid)
    -- Conclusion: mean-squared error of the sample mean = r⁻² · Σₖ (per-sample mean-squared error).
    ∫ ω, ‖(r : Real)⁻¹ • (∑ k, X k ω) - μ‖ ^ 2 ∂P
      = (r : Real)⁻¹ ^ 2 * ∑ k, ∫ ω, ‖X k ω - μ‖ ^ 2 ∂P := by
  -- Bridge the paper's coordinate-mean hypotheses to the Mathlib-staged abstract
  -- theorem (only pairwise independence and a Bochner mean are needed).
  have hbm : ∀ k, ∫ ω, X k ω ∂P = μ :=
    fun k => bochner_mean_of_coord P (X k) μ ((hL2 k).integrable one_le_two)
      (fun c => hmean k c)
  exact TauCeti.integral_norm_sq_average_sub_eq_sum P hr X μ hL2 hbm hindep

/--
**iid corollary (equality form).**

If in addition the per-sample mean-squared errors are identical
(`∫ ‖X k − μ‖² = ∫ ‖X 0 − μ‖²` for all `k`, automatic for an iid sample), the
additive identity collapses to the paper's `trace(Σ)/r` rate:

  ∫ ‖r⁻¹ Σₖ Xₖ − μ‖² ∂P = r⁻¹ · ∫ ‖X 0 − μ‖² ∂P.

Requires `0 < r` (the scaling collapses the `r⁻²·r` to `r⁻¹`).

PAPER CORRESPONDENCE: this is exactly the paper's `trace(Σ)/r` rate, i.e. the iid
identity `E‖(X̄_i)_j· − (μ_i)_j·‖² = γ_ij/r` of Appendix A.2.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem integral_norm_sq_sampleMean_sub_mean
    (P : Measure Ω) [IsProbabilityMeasure P]   -- probability measure (total mass 1)
    {ι : Type} [Fintype ι]                      -- finite coordinate index (response dimension)
    {r : Nat} (hr : 0 < r)                      -- positive sample size r
    (X : Fin r → Ω → EuclideanSpace Real ι)     -- iid-style sample
    (μ : EuclideanSpace Real ι)                 -- common mean
    (hL2 : ∀ k, MemLp (X k) 2 P)                -- finite second moment; extra, implicit in paper
    (hmean : ∀ k (c : ι), ∫ ω, X k ω c ∂P = μ c)  -- identical centring (mean μ)
    (hindep : Set.Pairwise (Set.univ : Set (Fin r))
      fun i j => IndepFun (X i) (X j) P)         -- pairwise independence
    (hident : ∀ k, ∫ ω, ‖X k ω - μ‖ ^ 2 ∂P
      = ∫ ω, ‖X ⟨0, hr⟩ ω - μ‖ ^ 2 ∂P) :         -- identically distributed second moment (the "id" of iid)
    -- Conclusion: sample-mean mean-squared error = r⁻¹ · (single-sample second moment) — the trace(Σ)/r rate.
    ∫ ω, ‖(r : Real)⁻¹ • (∑ k, X k ω) - μ‖ ^ 2 ∂P
      = (r : Real)⁻¹ * ∫ ω, ‖X ⟨0, hr⟩ ω - μ‖ ^ 2 ∂P := by
  rw [integral_norm_sq_sampleMean_sub_mean_eq_sum P hr X μ hL2 hmean hindep]
  simp_rw [hident]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hr0 : (r : Real) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp

/--
**Bound consumed by the Acharyya concentration chain.**

If each per-sample mean-squared error is bounded by `γ` (in the paper,
`γ = trace(Σ)`), then the sample-mean mean-squared error decays at rate `γ/r`:

  ∫ ‖r⁻¹ Σₖ Xₖ − μ‖² ∂P ≤ γ / r.

This is exactly the `v r = γ/r → 0` hypothesis of
`Acharyya2024.Probability.dissimilarity_convergesInProbability_of_secondMoment`.
Requires `0 < r`.

PAPER CORRESPONDENCE: produces the bound `≤ γ_ij/r` (with `γ = trace(Σ_ij)`) that
feeds the concentration step of Theorem 2; it is the link between the variance
algebra here and the `hmoment`/`v r → 0` hypothesis there.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem integral_norm_sq_sampleMean_sub_mean_le_of_bound
    (P : Measure Ω) [IsProbabilityMeasure P]   -- probability measure (total mass 1)
    {ι : Type} [Fintype ι]                      -- finite coordinate index (response dimension)
    {r : Nat} (hr : 0 < r)                      -- positive sample size r
    (X : Fin r → Ω → EuclideanSpace Real ι)     -- iid-style sample
    (μ : EuclideanSpace Real ι)                 -- common mean
    (hL2 : ∀ k, MemLp (X k) 2 P)                -- finite second moment; extra, implicit in paper
    (hmean : ∀ k (c : ι), ∫ ω, X k ω c ∂P = μ c)  -- identical centring (mean μ)
    (hindep : Set.Pairwise (Set.univ : Set (Fin r))
      fun i j => IndepFun (X i) (X j) P)         -- pairwise independence
    {γ : Real}                                   -- second-moment bound (paper: γ = trace(Σ))
    (hbound : ∀ k, ∫ ω, ‖X k ω - μ‖ ^ 2 ∂P ≤ γ) :  -- each per-sample second moment ≤ γ
    -- Conclusion: the sample-mean mean-squared error decays at rate γ/r (paper's γ_ij/r → 0).
    ∫ ω, ‖(r : Real)⁻¹ • (∑ k, X k ω) - μ‖ ^ 2 ∂P ≤ γ / r := by
  rw [integral_norm_sq_sampleMean_sub_mean_eq_sum P hr X μ hL2 hmean hindep]
  have hr0 : (0 : Real) < (r : Real) := by exact_mod_cast hr
  -- Sum of per-sample second moments is ≤ r·γ.
  have hsum_le : (∑ k, ∫ ω, ‖X k ω - μ‖ ^ 2 ∂P) ≤ (r : Real) * γ := by
    calc (∑ k, ∫ ω, ‖X k ω - μ‖ ^ 2 ∂P)
          ≤ ∑ _k : Fin r, γ := Finset.sum_le_sum fun k _ => hbound k
      _ = (r : Real) * γ := by
            simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- Multiply by `r⁻² ≥ 0` and simplify `r⁻² · r · γ = γ / r`.
  have hinv_nonneg : (0 : Real) ≤ (r : Real)⁻¹ ^ 2 := by positivity
  calc (r : Real)⁻¹ ^ 2 * ∑ k, ∫ ω, ‖X k ω - μ‖ ^ 2 ∂P
        ≤ (r : Real)⁻¹ ^ 2 * ((r : Real) * γ) :=
          mul_le_mul_of_nonneg_left hsum_le hinv_nonneg
    _ = γ / r := by
          rw [sq, mul_assoc, inv_mul_cancel_left₀ hr0.ne', div_eq_inv_mul]

/-! ## (e) Grounding `γ` as the paper's per-query trace-covariance

The concentration theorems take a bound on `∫ ‖X̄ᵢ − μᵢ‖²`.  The paper's hypothesis is stated in
terms of `γ_ij = trace(Σ_ij)`, the trace-covariance of the response of model `i` to query `j`,
summed over queries.  These two are the same quantity, and this is why: the Frobenius second
moment of a response matrix splits over its rows, and the row `j` contribution is exactly the
trace-covariance of the response to query `j`. -/

/-- The second moment of a Euclidean-space-valued variable splits over coordinates. -/
theorem integral_norm_sq_eq_sum_coord {ι : Type} [Fintype ι] (P : Measure Ω)
    (X : Ω → EuclideanSpace Real ι) (μ : EuclideanSpace Real ι)
    (hint : ∀ i, Integrable (fun ω => (X ω i - μ i) ^ 2) P) :
    ∫ ω, ‖X ω - μ‖ ^ 2 ∂P = ∑ i, ∫ ω, (X ω i - μ i) ^ 2 ∂P := by
  have hpt : ∀ ω, ‖X ω - μ‖ ^ 2 = ∑ i, (X ω i - μ i) ^ 2 := by
    intro ω
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Real.norm_eq_abs, sq_abs]
  simp_rw [hpt]
  exact integral_finsetSum _ (fun i _ => hint i)

/--
**`γ` is the paper's trace-covariance, summed over queries.**

The Frobenius second moment of a response matrix is the sum over queries of the trace-covariance
of the response to that query.  So the `γ` that the concentration theorems consume is the
paper's `∑_j γ_ij` and not an abstract bound.
-/
theorem integral_norm_sq_eq_sum_query {m p : Nat} (P : Measure Ω)
    (X : Ω → EuclideanSpace Real (Fin m × Fin p)) (μ : EuclideanSpace Real (Fin m × Fin p))
    (hint : ∀ q : Fin m × Fin p, Integrable (fun ω => (X ω q - μ q) ^ 2) P) :
    ∫ ω, ‖X ω - μ‖ ^ 2 ∂P
      = ∑ j : Fin m, ∑ k : Fin p, ∫ ω, (X ω (j, k) - μ (j, k)) ^ 2 ∂P := by
  rw [integral_norm_sq_eq_sum_coord P X μ hint, Fintype.sum_prod_type]

/-! ## (f) Appendix A.2 through to the response matrix

`integral_norm_sq_sampleMean_sub_mean_le_of_bound` is Appendix A.2 for one query: the replicate
average of the responses to a single query has mean-squared error at most `gamma_ij / r`.  The
quantity the concentration step consumes is the Frobenius error of the whole response *matrix*,
and passing from one to the other is a sum over rows.

The sum costs nothing, and in particular it does **not** need the responses to different queries
to be independent.  The Frobenius second moment splits over coordinates by
`integral_norm_sq_eq_sum_query` -- an identity, not an inequality -- so each row may be bounded on
its own.  Only the replicates of a *fixed* query need to be independent, which is exactly what the
source assumes when it writes `g(f_i(q_j)_k) ~iid F_ij`. -/

/--
**Appendix A.2 for the response matrix.**

`Y j k` is the `k`-th replicate of the response to query `j`, `mu j` its mean, and `gamma j` a
bound on its second moment -- the paper's `gamma_ij = trace(Sigma_ij)`.  `Xbar` is the response
matrix whose `j`-th row is the replicate average, and the conclusion is the bound the
concentration theorems consume:

  `E ‖Xbar_i − mu_i‖² ≤ (∑_j gamma_ij) / r`.

Independence is assumed only across the replicates of each fixed query.
-/
theorem integral_norm_sq_matrix_le_sum_row_bounds
    (P : Measure Ω) [IsProbabilityMeasure P] {m p : Nat} {r : Nat} (hr : 0 < r)
    (Y : Fin m → Fin r → Ω → EuclideanSpace Real (Fin p))
    (mu : Fin m → EuclideanSpace Real (Fin p))
    (γ : Fin m → Real)
    (hL2 : ∀ j k, MemLp (Y j k) 2 P)
    (hmean : ∀ j k (c : Fin p), ∫ ω, Y j k ω c ∂P = mu j c)
    (hindep : ∀ j, Set.Pairwise (Set.univ : Set (Fin r))
      fun k k' => IndepFun (Y j k) (Y j k') P)
    (hbound : ∀ j k, ∫ ω, ‖Y j k ω - mu j‖ ^ 2 ∂P ≤ γ j)
    (Xbar : Ω → EuclideanSpace Real (Fin m × Fin p))
    (μM : EuclideanSpace Real (Fin m × Fin p))
    (hXbar : ∀ ω (j : Fin m) (c : Fin p),
      Xbar ω (j, c) = ((r : Real)⁻¹ • ∑ k, Y j k ω) c)
    (hμM : ∀ (j : Fin m) (c : Fin p), μM (j, c) = mu j c)
    (hint : ∀ q : Fin m × Fin p, Integrable (fun ω => (Xbar ω q - μM q) ^ 2) P) :
    ∫ ω, ‖Xbar ω - μM‖ ^ 2 ∂P ≤ (∑ j, γ j) / r := by
  rw [integral_norm_sq_eq_sum_query P Xbar μM hint, Finset.sum_div]
  refine Finset.sum_le_sum fun j _ => ?_
  have hcongr : ∀ (c : Fin p) (ω : Ω),
      (Xbar ω (j, c) - μM (j, c)) ^ 2
        = (((r : Real)⁻¹ • ∑ k, Y j k ω) c - mu j c) ^ 2 := by
    intro c ω
    rw [hXbar, hμM]
  have hint' : ∀ c : Fin p, Integrable
      (fun ω => (((r : Real)⁻¹ • ∑ k, Y j k ω) c - mu j c) ^ 2) P := fun c =>
    (hint (j, c)).congr (Filter.Eventually.of_forall fun ω => hcongr c ω)
  have hrow : ∑ c : Fin p, ∫ ω, (Xbar ω (j, c) - μM (j, c)) ^ 2 ∂P
      = ∫ ω, ‖((r : Real)⁻¹ • ∑ k, Y j k ω) - mu j‖ ^ 2 ∂P := by
    rw [integral_norm_sq_eq_sum_coord P (fun ω => (r : Real)⁻¹ • ∑ k, Y j k ω) (mu j) hint']
    exact Finset.sum_congr rfl fun c _ =>
      integral_congr_ae (Filter.Eventually.of_forall fun ω => hcongr c ω)
  rw [hrow]
  exact integral_norm_sq_sampleMean_sub_mean_le_of_bound P hr (Y j) (mu j) (hL2 j)
    (hmean j) (hindep j) (hbound j)


/-- The Frobenius square is integrable as soon as each coordinate square is: the two agree
pointwise, and a finite sum of integrable functions is integrable. -/
theorem integrable_norm_sq_of_coord {ι : Type} [Fintype ι] (P : Measure Ω)
    (X : Ω → EuclideanSpace Real ι) (μ : EuclideanSpace Real ι)
    (hint : ∀ i, Integrable (fun ω => (X ω i - μ i) ^ 2) P) :
    Integrable (fun ω => ‖X ω - μ‖ ^ 2) P := by
  have hpt : ∀ ω, ‖X ω - μ‖ ^ 2 = ∑ i, (X ω i - μ i) ^ 2 := by
    intro ω
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Real.norm_eq_abs, sq_abs]
  exact (integrable_finsetSum _ fun i _ => hint i).congr
    (Filter.Eventually.of_forall fun ω => (hpt ω).symm)


end Acharyya2024.SecondMoment

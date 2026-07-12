/-
Random spectral regularity for raw-response Quench.

The production growing theorem currently assumes a population eigenvalue floor
and ceiling for every reference-sampling outcome.  That is stronger than the
probabilistic setting warrants.  This module replaces those global assumptions
by a high-probability spectral event derived from:

* compact bounded perspectives;
* iid reference sampling;
* one population covariance nondegeneracy condition.

The lemmas are intentionally split into probability, covariance-to-Gram, target
augmentation, and eigenvalue comparison steps so no single proof must solve the
whole argument.
-/

import DkpsQuench2026.Geometry.CenteredCovariance
import DkpsQuench2026.Spectral.GramSpectrum

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise Topology
open scoped RealInnerProductSpace InnerProductSpace Matrix
open Filter MeasureTheory ProbabilityTheory

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace DkpsQuench2026

open Acharyya2024
open Acharyya2025.Bridge
open Acharyya2025.Deterministic
open Acharyya2025.MatrixPerturbation
open Acharyya2025.MathlibBridge

universe u v wr

variable {Q : Type u} [DecidableEq Q]
variable {X : Type v} [MeasurableSpace X]
variable {Ωref : Type wr} [MeasurableSpace Ωref]

/-- Stage-`n` reference perspective configuration. -/
def referencePerspectiveConfig
    {d : Nat}
    (ψ : Model Q X → Vec d)
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (n : Nat) (ωref : Ωref) : Config n d :=
  fun i => ψ (f_ref n ωref i)

/-- Sample-centered empirical covariance of the reference perspectives.

Using the sample centroid here is essential: this matrix is exactly the
feature-space scatter associated with the centered Gram matrix used by CMDS.
The probability proof must therefore control both empirical second moments and
the empirical mean; a covariance about a fixed population center would have the
wrong inequality direction for the later spectral floor. -/
noncomputable def referenceEmpiricalCovariance
    {d : Nat}
    (ψ : Model Q X → Vec d)
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (n : Nat) (ωref : Ωref) : DisMat d :=
  fun a b => (n : Real)⁻¹ *
    ∑ i : Fin n,
      centerConfig (referencePerspectiveConfig ψ f_ref n ωref) i a *
      centerConfig (referencePerspectiveConfig ψ f_ref n ωref) i b

/-- Empirical mean of one perspective coordinate over the stage references. -/
noncomputable def referenceCoordinateMean
    {d : Nat}
    (ψ : Model Q X → Vec d)
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (n : Nat) (ωref : Ωref) (a : Fin d) : Real :=
  (n : Real)⁻¹ * ∑ i : Fin n, ψ (f_ref n ωref i) a

/-- Empirical mean of one coordinate product over the stage references. -/
noncomputable def referenceCoordinateProductMean
    {d : Nat}
    (ψ : Model Q X → Vec d)
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (n : Nat) (ωref : Ωref) (a b : Fin d) : Real :=
  (n : Real)⁻¹ * ∑ i : Fin n,
    ψ (f_ref n ωref i) a * ψ (f_ref n ωref i) b

/-- Algebraic expansion of one sample-centered covariance entry.

Unfold the centroid, distribute both finite sums, and use
`Finset.sum_mul`/`Finset.mul_sum`.  This theorem is deliberately probability
free; the scalar covariance weak law should only have to combine convergence
of the three quantities displayed here.

Implementation recipe (execute in this order):
1. Unfold `referenceEmpiricalCovariance`, `referenceCoordinateMean`,
   `referenceCoordinateProductMean`, `centerConfig`, and `configCentroid` at the
   fixed coordinates `a,b`.
2. Rewrite the centroid coordinates as the corresponding empirical means.
3. Expand `(x_i - x̄_a) * (y_i - x̄_b)` inside the finite sum.
4. Use `Finset.sum_sub_distrib`, `Finset.sum_add_distrib`,
   `Finset.sum_mul`, and `Finset.mul_sum` to collect terms.
5. Simplify the two sums of constants with `Fintype.card_fin`; cancel
   `(n : Real)⁻¹ * n` in the nonzero case.
6. Handle `n = 0` separately by `cases n`; both sides simplify to zero.  For
   `n+1`, prove the cast is nonzero and finish with `ring`.
7. Keep this theorem purely algebraic and use it as the only covariance
   expansion downstream.
-/
theorem referenceEmpiricalCovariance_entry_eq_product_sub_mean_mul_mean
    {d : Nat}
    (ψ : Model Q X → Vec d)
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (n : Nat) (ωref : Ωref) (a b : Fin d) :
    referenceEmpiricalCovariance ψ f_ref n ωref a b =
      referenceCoordinateProductMean ψ f_ref n ωref a b -
        referenceCoordinateMean ψ f_ref n ωref a *
          referenceCoordinateMean ψ f_ref n ωref b := by
  simp only [referenceEmpiricalCovariance, referenceCoordinateProductMean,
    referenceCoordinateMean, centerConfig, configCentroid, referencePerspectiveConfig,
    PiLp.sub_apply, PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply, smul_eq_mul]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    have expand : ∀ i : Fin n,
        (ψ (f_ref n ωref i) a - (n : ℝ)⁻¹ * ∑ j, ψ (f_ref n ωref j) a) *
          (ψ (f_ref n ωref i) b - (n : ℝ)⁻¹ * ∑ j, ψ (f_ref n ωref j) b) =
        ψ (f_ref n ωref i) a * ψ (f_ref n ωref i) b
          - (n : ℝ)⁻¹ * (∑ j, ψ (f_ref n ωref j) b) * ψ (f_ref n ωref i) a
          - (n : ℝ)⁻¹ * (∑ j, ψ (f_ref n ωref j) a) * ψ (f_ref n ωref i) b
          + (n : ℝ)⁻¹ * (∑ j, ψ (f_ref n ωref j) a) *
              ((n : ℝ)⁻¹ * ∑ j, ψ (f_ref n ωref j) b) :=
      fun i => by ring
    simp only [expand, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring

/-- Scalar weak law for one perspective coordinate mean.

This should be proved from the iid joint-law interface by a bounded second-
moment Chebyshev estimate.  Compactness supplies a uniform coordinate bound.
Keeping it separate lets a weaker agent debug the sample-mean probability
argument before handling products or covariance algebra.

Implementation recipe (execute in this order):
1. Derive a uniform bound `B` on `‖ψ f‖` from
   `exists_perspective_norm_bound_of_isCompact_range`; hence
   `|ψ f a| ≤ B` and the scalar variance is bounded by `4*B^2` (a loose bound is
   fine).
2. Use `hiid` to identify the stage coordinates
   `fun ω => ψ (f_ref n ω i) a` as iid with law induced by `Pf` and to obtain
   measurability.
3. Apply the existing finite-sample/second-moment mean theorem in
   `Acharyya2024` or `Acharyya2025.GrowingResponse` to the scalar variables.
4. Obtain a probability bound of order `C/(n*ε^2)` by Chebyshev; treat `n=0`
   separately and use the theorem only eventually.
5. Unfold `HighProbAtTop`; choose `N` so `C/(n*ε^2) < δ`, convert the complement
   estimate to the event lower bound, and simplify the population mean.
6. Search anchors: `integral_norm_sq_replicateMean_sub_mean_le_of_bound`,
   `Probability.meas_gt_le_ofReal_secondMoment_div_sq`, and the iid fields used
   in `Coverage.lean`.  Do not invoke a matrix concentration theorem.
-/
theorem highProb_referenceCoordinateMean_of_compact_iid
    {d : Nat}
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μref : Nat → Measure Ωref) (hμref : ∀ n, IsProbabilityMeasure (μref n))
    (ψ : Model Q X → Vec d) (hψ : Measurable ψ)
    (hcompact : IsCompact (Set.range ψ))
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (hiid : IIDReferenceSampler Pf μref f_ref)
    (a : Fin d) {ε : Real} (hε : 0 < ε) :
    HighProbAtTop μref hμref (fun n => {ωref |
      |referenceCoordinateMean ψ f_ref n ωref a -
        ∫ f, ψ f a ∂Pf| ≤ ε}) := by
  have hmap : ∀ (n : Nat) (i : Fin n),
      (μref n).map (fun ωref => f_ref n ωref i) = Pf := by
    intro n i
    apply Measure.ext
    intro A hA
    rw [Measure.map_apply (hiid.measurable n i) hA]
    have hj := hiid.joint_law n (fun j => if j = i then A else Set.univ)
      (fun j => by by_cases h : j = i <;> simp [h, hA])
    have hset : {ωref | ∀ j, f_ref n ωref j ∈ if j = i then A else Set.univ}
        = (fun ωref => f_ref n ωref i) ⁻¹' A := by
      ext ωref
      simp only [Set.mem_setOf_eq, Set.mem_preimage]
      exact ⟨fun h => by have := h i; simpa using this,
        fun h j => by by_cases hji : j = i <;> simp [hji, h]⟩
    rw [hset] at hj
    rw [hj]
    simp only [apply_ite Pf, measure_univ, Finset.prod_ite_eq', Finset.mem_univ, if_true]
  obtain ⟨rB, hrB⟩ := hcompact.isBounded.subset_closedBall 0
  set B := max 0 rB with hBdef
  have hB0 : 0 ≤ B := le_max_left _ _
  have hBbound : ∀ f, ‖ψ f‖ ≤ B := fun f => by
    have hmem : ψ f ∈ Metric.closedBall (0 : Vec d) rB := hrB ⟨f, rfl⟩
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hmem
    exact hmem.trans (le_max_right _ _)
  set c := ∫ f, ψ f a ∂Pf with hc
  have hcoord_bound : ∀ f, |ψ f a| ≤ B := by
    intro f
    rw [show |ψ f a| = ‖ψ f a‖ from (Real.norm_eq_abs _).symm]
    exact (PiLp.norm_apply_le (ψ f) a).trans (hBbound f)
  have hcoordMeas : Measurable (fun f => ψ f a) :=
    ((EuclideanSpace.proj a).continuous.measurable).comp hψ
  have hZmeas : ∀ n (i : Fin n), Measurable (fun ωref => ψ (f_ref n ωref i) a) :=
    fun n i => hcoordMeas.comp (hiid.measurable n i)
  have hint_coord : ∀ n (i : Fin n),
      ∫ ωref, ψ (f_ref n ωref i) a ∂(μref n) = c := by
    intro n i
    have hmap' : ∫ m, ψ m a ∂((μref n).map (fun ωref => f_ref n ωref i))
        = ∫ ωref, ψ (f_ref n ωref i) a ∂(μref n) :=
      integral_map (hiid.measurable n i).aemeasurable hcoordMeas.aestronglyMeasurable
    rw [hmap n i] at hmap'
    rw [hc]; exact hmap'.symm
  have hL2 : ∀ n (i : Fin n), MemLp (fun ωref => ψ (f_ref n ωref i) a) 2 (μref n) := by
    intro n i
    haveI := hμref n
    exact MemLp.of_bound (hZmeas n i).aestronglyMeasurable B
      (Eventually.of_forall fun ωref => by rw [Real.norm_eq_abs]; exact hcoord_bound _)
  have hc_bound : |c| ≤ B := by
    have hInt : Integrable (fun f => ψ f a) Pf :=
      (MemLp.of_bound hcoordMeas.aestronglyMeasurable B
        (Eventually.of_forall fun f => by rw [Real.norm_eq_abs]; exact hcoord_bound _)).integrable
        le_rfl
    calc |c| ≤ ∫ f, |ψ f a| ∂Pf := abs_integral_le_integral_abs
      _ ≤ ∫ _f, B ∂Pf := integral_mono hInt.abs (integrable_const B) (fun f => hcoord_bound f)
      _ = B := by simp
  have hindep : ∀ n, Set.Pairwise (Set.univ : Set (Fin n))
      (fun i j => IndepFun (fun ωref => ψ (f_ref n ωref i) a)
        (fun ωref => ψ (f_ref n ωref j) a) (μref n)) := by
    intro n i _ j _ hij
    rw [indepFun_iff_measure_inter_preimage_eq_mul]
    intro s t hs ht
    set A' := (fun f => ψ f a) ⁻¹' s with hA'
    set B' := (fun f => ψ f a) ⁻¹' t with hB'
    have hsm : MeasurableSet A' := hcoordMeas hs
    have htm : MeasurableSet B' := hcoordMeas ht
    have hj := hiid.joint_law n
      (fun k => if k = i then A' else if k = j then B' else Set.univ)
      (fun k => by
        rcases eq_or_ne k i with h1 | h1
        · simp only [if_pos h1]; exact hsm
        · rcases eq_or_ne k j with h2 | h2
          · simp only [if_neg h1, if_pos h2]; exact htm
          · simp only [if_neg h1, if_neg h2]; exact MeasurableSet.univ)
    have hset : {ωref | ∀ k, f_ref n ωref k ∈
          (if k = i then A' else if k = j then B' else Set.univ)}
        = ((fun ωref => ψ (f_ref n ωref i) a) ⁻¹' s)
          ∩ ((fun ωref => ψ (f_ref n ωref j) a) ⁻¹' t) := by
      ext ωref
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, hA', hB']
      constructor
      · intro h
        exact ⟨by have := h i; simpa using this,
          by have := h j; rwa [if_neg (Ne.symm hij), if_pos rfl] at this⟩
      · rintro ⟨hi', hj'⟩ k
        rcases eq_or_ne k i with h1 | h1
        · subst h1; simp only [if_pos rfl]; exact hi'
        · rcases eq_or_ne k j with h2 | h2
          · subst h2; simp only [if_neg h1, if_pos rfl]; exact hj'
          · simp only [if_neg h1, if_neg h2]; exact Set.mem_univ _
    rw [hset] at hj
    rw [hj]
    have hmi : (μref n) ((fun ωref => ψ (f_ref n ωref i) a) ⁻¹' s) = Pf A' := by
      rw [show (fun ωref => ψ (f_ref n ωref i) a) ⁻¹' s
          = (fun ωref => f_ref n ωref i) ⁻¹' A' from rfl,
        ← Measure.map_apply (hiid.measurable n i) hsm, hmap n i]
    have hmj : (μref n) ((fun ωref => ψ (f_ref n ωref j) a) ⁻¹' t) = Pf B' := by
      rw [show (fun ωref => ψ (f_ref n ωref j) a) ⁻¹' t
          = (fun ωref => f_ref n ωref j) ⁻¹' B' from rfl,
        ← Measure.map_apply (hiid.measurable n j) htm, hmap n j]
    rw [hmi, hmj]
    rw [Finset.prod_congr rfl (g := fun k =>
        if k = i then Pf A' else if k = j then Pf B' else 1) (fun k _ => by
      rcases eq_or_ne k i with h1 | h1
      · simp only [if_pos h1]
      · rcases eq_or_ne k j with h2 | h2
        · simp only [if_neg h1, if_pos h2]
        · simp only [if_neg h1, if_neg h2, measure_univ])]
    rw [← Finset.prod_subset (Finset.subset_univ ({i, j} : Finset (Fin n)))
      (fun k _ hk => by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
        simp only [if_neg hk.1, if_neg hk.2])]
    rw [Finset.prod_pair hij, if_pos rfl, if_neg (Ne.symm hij), if_pos rfl]
  have hmse : ∀ n : Nat, 0 < n →
      ∫ ωref, (referenceCoordinateMean ψ f_ref n ωref a - c) ^ 2 ∂(μref n)
        ≤ 4 * B ^ 2 / n := by
    intro n hn
    haveI := hμref n
    have hbound_i : ∀ i : Fin n,
        ∫ ωref, (ψ (f_ref n ωref i) a - c) ^ 2 ∂(μref n) ≤ 4 * B ^ 2 := by
      intro i
      have hle : ∀ ωref, (ψ (f_ref n ωref i) a - c) ^ 2 ≤ 4 * B ^ 2 := by
        intro ωref
        have h1 : |ψ (f_ref n ωref i) a - c| ≤ 2 * B := by
          have htriangle : |ψ (f_ref n ωref i) a - c|
              ≤ |ψ (f_ref n ωref i) a| + |c| := by
            rw [sub_eq_add_neg, ← abs_neg c]; exact abs_add_le _ _
          have h2 := hcoord_bound (f_ref n ωref i)
          linarith [hc_bound]
        have hsq : |ψ (f_ref n ωref i) a - c| * |ψ (f_ref n ωref i) a - c|
            ≤ (2 * B) * (2 * B) :=
          mul_le_mul h1 h1 (abs_nonneg _) (by linarith)
        nlinarith [hsq, sq_abs (ψ (f_ref n ωref i) a - c)]
      calc ∫ ωref, (ψ (f_ref n ωref i) a - c) ^ 2 ∂(μref n)
          ≤ ∫ _ωref, 4 * B ^ 2 ∂(μref n) :=
            integral_mono ((hL2 n i).sub (memLp_const c)).integrable_sq (integrable_const _) hle
        _ = 4 * B ^ 2 := by simp
    simp only [referenceCoordinateMean]
    rw [ForMathlib.integral_sq_scaledSum_sub_of_pairwise_indep (μref n) hn
      (fun i ωref => ψ (f_ref n ωref i) a) c (fun i => hL2 n i) (fun i => hint_coord n i)
      (hindep n)]
    have hsum : ∑ i : Fin n, ∫ ωref, (ψ (f_ref n ωref i) a - c) ^ 2 ∂(μref n)
        ≤ (n : Real) * (4 * B ^ 2) := by
      calc ∑ i : Fin n, ∫ ωref, (ψ (f_ref n ωref i) a - c) ^ 2 ∂(μref n)
          ≤ ∑ _i : Fin n, 4 * B ^ 2 := Finset.sum_le_sum fun i _ => hbound_i i
        _ = (n : Real) * (4 * B ^ 2) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hn0 : (0 : Real) < (n : Real) := by exact_mod_cast hn
    calc (n : Real)⁻¹ ^ 2 * ∑ i : Fin n, ∫ ωref, (ψ (f_ref n ωref i) a - c) ^ 2 ∂(μref n)
        ≤ (n : Real)⁻¹ ^ 2 * ((n : Real) * (4 * B ^ 2)) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 4 * B ^ 2 / n := by rw [sq]; field_simp
  apply Acharyya2025.GrowingResponse.highProbAtTop_of_tendsto_compl_zero
  have hcompl : ∀ n : Nat, 0 < n →
      μref n ({ωref | |referenceCoordinateMean ψ f_ref n ωref a - c| ≤ ε}ᶜ)
        ≤ ENNReal.ofReal (2 * (4 * B ^ 2 / n) / ε ^ 2) := by
    intro n hn
    haveI := hμref n
    have hInt : Integrable
        (fun ωref => (referenceCoordinateMean ψ f_ref n ωref a - c) ^ 2) (μref n) := by
      have hM : MemLp (fun ωref => referenceCoordinateMean ψ f_ref n ωref a) 2 (μref n) := by
        simp only [referenceCoordinateMean]
        exact (memLp_finsetSum _ (fun i _ => hL2 n i)).const_mul _
      exact (hM.sub (memLp_const c)).integrable_sq
    have hInt' : Integrable
        (fun ωref => (-(referenceCoordinateMean ψ f_ref n ωref a - c)) ^ 2) (μref n) := by
      simpa only [neg_sq] using hInt
    have hpos := ForMathlib.meas_gt_le_ofReal_integral_sq_div_sq (μref n)
      (Y := fun ωref => referenceCoordinateMean ψ f_ref n ωref a - c) hInt hε (hmse n hn)
    have hneg := ForMathlib.meas_gt_le_ofReal_integral_sq_div_sq (μref n)
      (Y := fun ωref => -(referenceCoordinateMean ψ f_ref n ωref a - c)) hInt' hε
      (by simpa only [neg_sq] using hmse n hn)
    have hsub : {ωref | |referenceCoordinateMean ψ f_ref n ωref a - c| ≤ ε}ᶜ
        ⊆ {ωref | ε < referenceCoordinateMean ψ f_ref n ωref a - c}
          ∪ {ωref | ε < -(referenceCoordinateMean ψ f_ref n ωref a - c)} := by
      intro ωref hω
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hω
      rcases lt_abs.mp hω with h | h
      · exact Or.inl h
      · exact Or.inr h
    calc μref n ({ωref | |referenceCoordinateMean ψ f_ref n ωref a - c| ≤ ε}ᶜ)
        ≤ μref n ({ωref | ε < referenceCoordinateMean ψ f_ref n ωref a - c}
            ∪ {ωref | ε < -(referenceCoordinateMean ψ f_ref n ωref a - c)}) :=
          measure_mono hsub
      _ ≤ μref n {ωref | ε < referenceCoordinateMean ψ f_ref n ωref a - c}
            + μref n {ωref | ε < -(referenceCoordinateMean ψ f_ref n ωref a - c)} :=
          measure_union_le _ _
      _ ≤ ENNReal.ofReal (4 * B ^ 2 / n / ε ^ 2) + ENNReal.ofReal (4 * B ^ 2 / n / ε ^ 2) :=
          add_le_add hpos hneg
      _ = ENNReal.ofReal (2 * (4 * B ^ 2 / n) / ε ^ 2) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
  have hupperlim : Tendsto
      (fun n : Nat => ENNReal.ofReal (2 * (4 * B ^ 2 / n) / ε ^ 2)) atTop (𝓝 0) := by
    have hlim : Tendsto (fun n : Nat => 2 * (4 * B ^ 2 / n) / ε ^ 2) atTop (𝓝 0) := by
      refine (tendsto_const_div_atTop_nhds_zero_nat (8 * B ^ 2 / ε ^ 2)).congr (fun n => ?_)
      rcases Nat.eq_zero_or_pos n with hn | hn
      · simp [hn]
      · field_simp; ring
    simpa using ENNReal.tendsto_ofReal hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupperlim
    (Eventually.of_forall fun _ => zero_le)
    (eventually_atTop.mpr ⟨1, fun n hn => hcompl n hn⟩)

/-- Scalar weak law for one perspective-coordinate product mean.

Apply the same bounded Chebyshev argument as the coordinate-mean theorem to the
measurable bounded scalar map `f ↦ ψ f a * ψ f b`.  No covariance expansion
belongs in this proof.

Implementation recipe (execute in this order):
1. Reuse the perspective norm bound `B`; prove
   `|ψ f a * ψ f b| ≤ B^2` and hence a uniform second-moment bound for the scalar
   product map.
2. Prove the product map is measurable from `hψ` and coordinate evaluation.
3. Transport the iid law through the measurable product map using the same
   `IIDReferenceSampler` fields as in the coordinate-mean theorem.
4. Apply the same scalar sample-mean Chebyshev theorem with mean
   `∫ f, ψ f a * ψ f b ∂Pf`.
5. Convert the `O(1/n)` complement bound to `HighProbAtTop` exactly as in
   `highProb_referenceCoordinateMean_of_compact_iid`.
6. Factor any repeated scalar weak-law code into a local helper taking a bounded
   measurable scalar observable; do not mix covariance algebra into this proof.
-/
theorem highProb_referenceCoordinateProductMean_of_compact_iid
    {d : Nat}
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μref : Nat → Measure Ωref) (hμref : ∀ n, IsProbabilityMeasure (μref n))
    (ψ : Model Q X → Vec d) (hψ : Measurable ψ)
    (hcompact : IsCompact (Set.range ψ))
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (hiid : IIDReferenceSampler Pf μref f_ref)
    (a b : Fin d) {ε : Real} (hε : 0 < ε) :
    HighProbAtTop μref hμref (fun n => {ωref |
      |referenceCoordinateProductMean ψ f_ref n ωref a b -
        ∫ f, ψ f a * ψ f b ∂Pf| ≤ ε}) := by
  have hmap : ∀ (n : Nat) (i : Fin n),
      (μref n).map (fun ωref => f_ref n ωref i) = Pf := by
    intro n i
    apply Measure.ext
    intro A hA
    rw [Measure.map_apply (hiid.measurable n i) hA]
    have hj := hiid.joint_law n (fun j => if j = i then A else Set.univ)
      (fun j => by by_cases h : j = i <;> simp [h, hA])
    have hset : {ωref | ∀ j, f_ref n ωref j ∈ if j = i then A else Set.univ}
        = (fun ωref => f_ref n ωref i) ⁻¹' A := by
      ext ωref
      simp only [Set.mem_setOf_eq, Set.mem_preimage]
      exact ⟨fun h => by have := h i; simpa using this,
        fun h j => by by_cases hji : j = i <;> simp [hji, h]⟩
    rw [hset] at hj
    rw [hj]
    simp only [apply_ite Pf, measure_univ, Finset.prod_ite_eq', Finset.mem_univ, if_true]
  obtain ⟨rB, hrB⟩ := hcompact.isBounded.subset_closedBall 0
  set B := max 0 rB with hBdef
  have hB0 : 0 ≤ B := le_max_left _ _
  have hBbound : ∀ f, ‖ψ f‖ ≤ B := fun f => by
    have hmem : ψ f ∈ Metric.closedBall (0 : Vec d) rB := hrB ⟨f, rfl⟩
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hmem
    exact hmem.trans (le_max_right _ _)
  set Bg := B ^ 2 with hBgdef
  have hBg0 : 0 ≤ Bg := by positivity
  have hcoord_a : ∀ f, |ψ f a| ≤ B := fun f => by
    rw [show |ψ f a| = ‖ψ f a‖ from (Real.norm_eq_abs _).symm]
    exact (PiLp.norm_apply_le (ψ f) a).trans (hBbound f)
  have hcoord_b : ∀ f, |ψ f b| ≤ B := fun f => by
    rw [show |ψ f b| = ‖ψ f b‖ from (Real.norm_eq_abs _).symm]
    exact (PiLp.norm_apply_le (ψ f) b).trans (hBbound f)
  set c := ∫ f, ψ f a * ψ f b ∂Pf with hc
  have hcoord_bound : ∀ f, |ψ f a * ψ f b| ≤ Bg := by
    intro f
    rw [abs_mul, hBgdef, sq]
    exact mul_le_mul (hcoord_a f) (hcoord_b f) (abs_nonneg _) hB0
  have hcoordMeas : Measurable (fun f => ψ f a * ψ f b) :=
    (((EuclideanSpace.proj a).continuous.measurable).comp hψ).mul
      (((EuclideanSpace.proj b).continuous.measurable).comp hψ)
  have hZmeas : ∀ n (i : Fin n),
      Measurable (fun ωref => ψ (f_ref n ωref i) a * ψ (f_ref n ωref i) b) :=
    fun n i => hcoordMeas.comp (hiid.measurable n i)
  have hint_coord : ∀ n (i : Fin n),
      ∫ ωref, ψ (f_ref n ωref i) a * ψ (f_ref n ωref i) b ∂(μref n) = c := by
    intro n i
    have hmap' : ∫ m, ψ m a * ψ m b ∂((μref n).map (fun ωref => f_ref n ωref i))
        = ∫ ωref, ψ (f_ref n ωref i) a * ψ (f_ref n ωref i) b ∂(μref n) :=
      integral_map (hiid.measurable n i).aemeasurable hcoordMeas.aestronglyMeasurable
    rw [hmap n i] at hmap'
    rw [hc]; exact hmap'.symm
  have hL2 : ∀ n (i : Fin n),
      MemLp (fun ωref => ψ (f_ref n ωref i) a * ψ (f_ref n ωref i) b) 2 (μref n) := by
    intro n i
    haveI := hμref n
    exact MemLp.of_bound (hZmeas n i).aestronglyMeasurable Bg
      (Eventually.of_forall fun ωref => by rw [Real.norm_eq_abs]; exact hcoord_bound _)
  have hc_bound : |c| ≤ Bg := by
    have hInt : Integrable (fun f => ψ f a * ψ f b) Pf :=
      (MemLp.of_bound hcoordMeas.aestronglyMeasurable Bg
        (Eventually.of_forall fun f => by rw [Real.norm_eq_abs]; exact hcoord_bound _)).integrable
        le_rfl
    calc |c| ≤ ∫ f, |ψ f a * ψ f b| ∂Pf := abs_integral_le_integral_abs
      _ ≤ ∫ _f, Bg ∂Pf := integral_mono hInt.abs (integrable_const Bg) (fun f => hcoord_bound f)
      _ = Bg := by simp
  have hindep : ∀ n, Set.Pairwise (Set.univ : Set (Fin n))
      (fun i j => IndepFun (fun ωref => ψ (f_ref n ωref i) a * ψ (f_ref n ωref i) b)
        (fun ωref => ψ (f_ref n ωref j) a * ψ (f_ref n ωref j) b) (μref n)) := by
    intro n i _ j _ hij
    rw [indepFun_iff_measure_inter_preimage_eq_mul]
    intro s t hs ht
    set A' := (fun f => ψ f a * ψ f b) ⁻¹' s with hA'
    set B' := (fun f => ψ f a * ψ f b) ⁻¹' t with hB'
    have hsm : MeasurableSet A' := hcoordMeas hs
    have htm : MeasurableSet B' := hcoordMeas ht
    have hj := hiid.joint_law n
      (fun k => if k = i then A' else if k = j then B' else Set.univ)
      (fun k => by
        rcases eq_or_ne k i with h1 | h1
        · simp only [if_pos h1]; exact hsm
        · rcases eq_or_ne k j with h2 | h2
          · simp only [if_neg h1, if_pos h2]; exact htm
          · simp only [if_neg h1, if_neg h2]; exact MeasurableSet.univ)
    have hset : {ωref | ∀ k, f_ref n ωref k ∈
          (if k = i then A' else if k = j then B' else Set.univ)}
        = ((fun ωref => ψ (f_ref n ωref i) a * ψ (f_ref n ωref i) b) ⁻¹' s)
          ∩ ((fun ωref => ψ (f_ref n ωref j) a * ψ (f_ref n ωref j) b) ⁻¹' t) := by
      ext ωref
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, hA', hB']
      constructor
      · intro h
        exact ⟨by have := h i; simpa using this,
          by have := h j; rwa [if_neg (Ne.symm hij), if_pos rfl] at this⟩
      · rintro ⟨hi', hj'⟩ k
        rcases eq_or_ne k i with h1 | h1
        · subst h1; simp only [if_pos rfl]; exact hi'
        · rcases eq_or_ne k j with h2 | h2
          · subst h2; simp only [if_neg h1, if_pos rfl]; exact hj'
          · simp only [if_neg h1, if_neg h2]; exact Set.mem_univ _
    rw [hset] at hj
    rw [hj]
    have hmi : (μref n) ((fun ωref => ψ (f_ref n ωref i) a * ψ (f_ref n ωref i) b) ⁻¹' s)
        = Pf A' := by
      rw [show (fun ωref => ψ (f_ref n ωref i) a * ψ (f_ref n ωref i) b) ⁻¹' s
          = (fun ωref => f_ref n ωref i) ⁻¹' A' from rfl,
        ← Measure.map_apply (hiid.measurable n i) hsm, hmap n i]
    have hmj : (μref n) ((fun ωref => ψ (f_ref n ωref j) a * ψ (f_ref n ωref j) b) ⁻¹' t)
        = Pf B' := by
      rw [show (fun ωref => ψ (f_ref n ωref j) a * ψ (f_ref n ωref j) b) ⁻¹' t
          = (fun ωref => f_ref n ωref j) ⁻¹' B' from rfl,
        ← Measure.map_apply (hiid.measurable n j) htm, hmap n j]
    rw [hmi, hmj]
    rw [Finset.prod_congr rfl (g := fun k =>
        if k = i then Pf A' else if k = j then Pf B' else 1) (fun k _ => by
      rcases eq_or_ne k i with h1 | h1
      · simp only [if_pos h1]
      · rcases eq_or_ne k j with h2 | h2
        · simp only [if_neg h1, if_pos h2]
        · simp only [if_neg h1, if_neg h2, measure_univ])]
    rw [← Finset.prod_subset (Finset.subset_univ ({i, j} : Finset (Fin n)))
      (fun k _ hk => by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
        simp only [if_neg hk.1, if_neg hk.2])]
    rw [Finset.prod_pair hij, if_pos rfl, if_neg (Ne.symm hij), if_pos rfl]
  have hmse : ∀ n : Nat, 0 < n →
      ∫ ωref, (referenceCoordinateProductMean ψ f_ref n ωref a b - c) ^ 2 ∂(μref n)
        ≤ 4 * Bg ^ 2 / n := by
    intro n hn
    haveI := hμref n
    have hbound_i : ∀ i : Fin n,
        ∫ ωref, (ψ (f_ref n ωref i) a * ψ (f_ref n ωref i) b - c) ^ 2 ∂(μref n)
          ≤ 4 * Bg ^ 2 := by
      intro i
      have hle : ∀ ωref,
          (ψ (f_ref n ωref i) a * ψ (f_ref n ωref i) b - c) ^ 2 ≤ 4 * Bg ^ 2 := by
        intro ωref
        have h1 : |ψ (f_ref n ωref i) a * ψ (f_ref n ωref i) b - c| ≤ 2 * Bg := by
          have htriangle : |ψ (f_ref n ωref i) a * ψ (f_ref n ωref i) b - c|
              ≤ |ψ (f_ref n ωref i) a * ψ (f_ref n ωref i) b| + |c| := by
            rw [sub_eq_add_neg, ← abs_neg c]; exact abs_add_le _ _
          have h2 := hcoord_bound (f_ref n ωref i)
          linarith [hc_bound]
        have hsq : |ψ (f_ref n ωref i) a * ψ (f_ref n ωref i) b - c|
            * |ψ (f_ref n ωref i) a * ψ (f_ref n ωref i) b - c| ≤ (2 * Bg) * (2 * Bg) :=
          mul_le_mul h1 h1 (abs_nonneg _) (by linarith)
        nlinarith [hsq, sq_abs (ψ (f_ref n ωref i) a * ψ (f_ref n ωref i) b - c)]
      calc ∫ ωref, (ψ (f_ref n ωref i) a * ψ (f_ref n ωref i) b - c) ^ 2 ∂(μref n)
          ≤ ∫ _ωref, 4 * Bg ^ 2 ∂(μref n) :=
            integral_mono ((hL2 n i).sub (memLp_const c)).integrable_sq (integrable_const _) hle
        _ = 4 * Bg ^ 2 := by simp
    simp only [referenceCoordinateProductMean]
    rw [ForMathlib.integral_sq_scaledSum_sub_of_pairwise_indep (μref n) hn
      (fun i ωref => ψ (f_ref n ωref i) a * ψ (f_ref n ωref i) b) c (fun i => hL2 n i)
      (fun i => hint_coord n i) (hindep n)]
    have hsum : ∑ i : Fin n,
        ∫ ωref, (ψ (f_ref n ωref i) a * ψ (f_ref n ωref i) b - c) ^ 2 ∂(μref n)
        ≤ (n : Real) * (4 * Bg ^ 2) := by
      calc ∑ i : Fin n,
            ∫ ωref, (ψ (f_ref n ωref i) a * ψ (f_ref n ωref i) b - c) ^ 2 ∂(μref n)
          ≤ ∑ _i : Fin n, 4 * Bg ^ 2 := Finset.sum_le_sum fun i _ => hbound_i i
        _ = (n : Real) * (4 * Bg ^ 2) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hn0 : (0 : Real) < (n : Real) := by exact_mod_cast hn
    calc (n : Real)⁻¹ ^ 2 * ∑ i : Fin n,
          ∫ ωref, (ψ (f_ref n ωref i) a * ψ (f_ref n ωref i) b - c) ^ 2 ∂(μref n)
        ≤ (n : Real)⁻¹ ^ 2 * ((n : Real) * (4 * Bg ^ 2)) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 4 * Bg ^ 2 / n := by rw [sq]; field_simp
  apply Acharyya2025.GrowingResponse.highProbAtTop_of_tendsto_compl_zero
  have hcompl : ∀ n : Nat, 0 < n →
      μref n ({ωref | |referenceCoordinateProductMean ψ f_ref n ωref a b - c| ≤ ε}ᶜ)
        ≤ ENNReal.ofReal (2 * (4 * Bg ^ 2 / n) / ε ^ 2) := by
    intro n hn
    haveI := hμref n
    have hInt : Integrable
        (fun ωref => (referenceCoordinateProductMean ψ f_ref n ωref a b - c) ^ 2) (μref n) := by
      have hM : MemLp
          (fun ωref => referenceCoordinateProductMean ψ f_ref n ωref a b) 2 (μref n) := by
        simp only [referenceCoordinateProductMean]
        exact (memLp_finsetSum _ (fun i _ => hL2 n i)).const_mul _
      exact (hM.sub (memLp_const c)).integrable_sq
    have hInt' : Integrable
        (fun ωref => (-(referenceCoordinateProductMean ψ f_ref n ωref a b - c)) ^ 2) (μref n) := by
      simpa only [neg_sq] using hInt
    have hpos := ForMathlib.meas_gt_le_ofReal_integral_sq_div_sq (μref n)
      (Y := fun ωref => referenceCoordinateProductMean ψ f_ref n ωref a b - c) hInt hε (hmse n hn)
    have hneg := ForMathlib.meas_gt_le_ofReal_integral_sq_div_sq (μref n)
      (Y := fun ωref => -(referenceCoordinateProductMean ψ f_ref n ωref a b - c)) hInt' hε
      (by simpa only [neg_sq] using hmse n hn)
    have hsub : {ωref | |referenceCoordinateProductMean ψ f_ref n ωref a b - c| ≤ ε}ᶜ
        ⊆ {ωref | ε < referenceCoordinateProductMean ψ f_ref n ωref a b - c}
          ∪ {ωref | ε < -(referenceCoordinateProductMean ψ f_ref n ωref a b - c)} := by
      intro ωref hω
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hω
      rcases lt_abs.mp hω with h | h
      · exact Or.inl h
      · exact Or.inr h
    calc μref n ({ωref | |referenceCoordinateProductMean ψ f_ref n ωref a b - c| ≤ ε}ᶜ)
        ≤ μref n ({ωref | ε < referenceCoordinateProductMean ψ f_ref n ωref a b - c}
            ∪ {ωref | ε < -(referenceCoordinateProductMean ψ f_ref n ωref a b - c)}) :=
          measure_mono hsub
      _ ≤ μref n {ωref | ε < referenceCoordinateProductMean ψ f_ref n ωref a b - c}
            + μref n {ωref | ε < -(referenceCoordinateProductMean ψ f_ref n ωref a b - c)} :=
          measure_union_le _ _
      _ ≤ ENNReal.ofReal (4 * Bg ^ 2 / n / ε ^ 2) + ENNReal.ofReal (4 * Bg ^ 2 / n / ε ^ 2) :=
          add_le_add hpos hneg
      _ = ENNReal.ofReal (2 * (4 * Bg ^ 2 / n) / ε ^ 2) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
  have hupperlim : Tendsto
      (fun n : Nat => ENNReal.ofReal (2 * (4 * Bg ^ 2 / n) / ε ^ 2)) atTop (𝓝 0) := by
    have hlim : Tendsto (fun n : Nat => 2 * (4 * Bg ^ 2 / n) / ε ^ 2) atTop (𝓝 0) := by
      refine (tendsto_const_div_atTop_nhds_zero_nat (8 * Bg ^ 2 / ε ^ 2)).congr (fun n => ?_)
      rcases Nat.eq_zero_or_pos n with hn | hn
      · simp [hn]
      · field_simp; ring
    simpa using ENNReal.tendsto_ofReal hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupperlim
    (Eventually.of_forall fun _ => zero_le)
    (eventually_atTop.mpr ⟨1, fun n hn => hcompl n hn⟩)

/-- Measurable finite-dimensional event that empirical reference covariance is
entrywise close to population covariance. -/
def referenceCovarianceEvent
    {d : Nat}
    (Pf : Measure (Model Q X))
    (ψ : Model Q X → Vec d)
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (center : Vec d) (ε : Real) (n : Nat) : Set Ωref :=
  {ωref | EntrywiseClose
    (referenceEmpiricalCovariance ψ f_ref n ωref)
    (perspectiveCovarianceMatrix Pf ψ center) ε}

/-- Compactness of the perspective range gives a uniform norm envelope.

Suggested proof route: the norm is continuous, hence its image on the compact
range is compact and bounded.  Extract a real upper bound and enlarge it to a
nonnegative number.  Return a bound on every model rather than only on points in
the range so later theorem applications remain simple.

Implementation recipe (execute in this order):
1. Apply compactness of `Set.range ψ` to the continuous norm map; obtain that
   `norm '' Set.range ψ` is compact.
2. Use compactness to obtain boundedness, or use
   `hcompact.isBounded.subset_closedBall` to get a radius `R` and center.
3. Convert a ball bound around an arbitrary center into a bound from zero by the
   triangle inequality, and choose `B := max 0 (...)`.
4. For each `f`, use `ψ f ∈ Set.range ψ` to specialize the boundedness result.
5. Search anchors: `IsCompact.bddAbove`, `IsCompact.isBounded`,
   `Metric.isBounded_iff_subset_closedBall`, and `ContinuousOn.norm`.
6. Do not assume the model type itself is compact; only the perspective range is.
-/
theorem exists_perspective_norm_bound_of_isCompact_range
    {d : Nat}
    (ψ : Model Q X → Vec d)
    (hcompact : IsCompact (Set.range ψ)) :
    ∃ B : Real, 0 ≤ B ∧ ∀ f, ‖ψ f‖ ≤ B := by
  obtain ⟨r, hr⟩ := hcompact.isBounded.subset_closedBall 0
  refine ⟨max 0 r, le_max_left _ _, fun f => ?_⟩
  have hmem : ψ f ∈ Metric.closedBall (0 : Vec d) r := hr ⟨f, rfl⟩
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hmem
  exact hmem.trans (le_max_right _ _)

/-- One scalar empirical-covariance entry event is measurable.

This is the atomic measurability result required by
`HighProbAtTop.finset_all`.  Expand the sample-centered covariance entry into
finite sums and products of measurable coordinates.  Keep this separate from
the finite conjunction theorem: measurability of the conjunction alone does
not provide measurability of each event needed by the high-probability
intersection API.

Implementation recipe (execute in this order):
1. Prove each map `ωref ↦ ψ (f_ref n ωref i) a` measurable by
   `(hψ.comp (href n i)).eval a` or the corresponding coordinate-evaluation
   lemma.
2. From these maps, prove measurability of `referenceCoordinateMean` and
   `referenceCoordinateProductMean` using finite sums and scalar multiplication.
3. Rewrite the empirical covariance entry with
   `referenceEmpiricalCovariance_entry_eq_product_sub_mean_mul_mean`; deduce its
   measurability by subtraction and multiplication.
4. The population covariance entry is constant in `ωref`.
5. Apply measurability of subtraction, absolute value, and `measurableSet_le` to
   the constant `ε`.
6. Avoid unfolding the double finite sum directly after step 3; the algebraic
   lemma exists to keep this proof small.
-/
theorem measurableSet_referenceCovarianceEntryEvent
    {d : Nat}
    (Pf : Measure (Model Q X))
    (ψ : Model Q X → Vec d) (hψ : Measurable ψ)
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (href : ∀ n i, Measurable fun ωref => f_ref n ωref i)
    (center : Vec d) (ε : Real) (n : Nat) (a b : Fin d) :
    MeasurableSet {ωref |
      |referenceEmpiricalCovariance ψ f_ref n ωref a b -
        perspectiveCovarianceMatrix Pf ψ center a b| ≤ ε} := by
  have hcoord : ∀ (i : Fin n) (c : Fin d),
      Measurable (fun ωref => ψ (f_ref n ωref i) c) :=
    fun i c => ((EuclideanSpace.proj c).continuous.measurable).comp (hψ.comp (href n i))
  have hmeanA : Measurable (fun ωref => referenceCoordinateMean ψ f_ref n ωref a) := by
    simp only [referenceCoordinateMean]
    exact measurable_const.mul (Finset.measurable_sum _ (fun i _ => hcoord i a))
  have hmeanB : Measurable (fun ωref => referenceCoordinateMean ψ f_ref n ωref b) := by
    simp only [referenceCoordinateMean]
    exact measurable_const.mul (Finset.measurable_sum _ (fun i _ => hcoord i b))
  have hprod : Measurable (fun ωref =>
      referenceCoordinateProductMean ψ f_ref n ωref a b) := by
    simp only [referenceCoordinateProductMean]
    exact measurable_const.mul
      (Finset.measurable_sum _ (fun i _ => (hcoord i a).mul (hcoord i b)))
  have hcov : Measurable (fun ωref =>
      referenceEmpiricalCovariance ψ f_ref n ωref a b) := by
    have heq : (fun ωref => referenceEmpiricalCovariance ψ f_ref n ωref a b) =
        (fun ωref => referenceCoordinateProductMean ψ f_ref n ωref a b -
          referenceCoordinateMean ψ f_ref n ωref a *
            referenceCoordinateMean ψ f_ref n ωref b) :=
      funext fun ωref =>
        referenceEmpiricalCovariance_entry_eq_product_sub_mean_mul_mean ψ f_ref n ωref a b
    rw [heq]
    exact hprod.sub (hmeanA.mul hmeanB)
  exact measurableSet_le ((hcov.sub measurable_const).abs) measurable_const

/-- The empirical covariance event is measurable.

Suggested proof route: unfold `EntrywiseClose` and apply
`measurableSet_finset_all` twice over `Finset.univ`, using
`measurableSet_referenceCovarianceEntryEvent` for each scalar event.  Avoid
introducing operator norms here, because the finite entrywise event is exactly
what the later union-bound proof controls.

Implementation recipe (execute in this order):
1. Unfold `referenceCovarianceEvent` and `EntrywiseClose`.
2. Express the event as
   `{ω | ∀ a ∈ Finset.univ, ∀ b ∈ Finset.univ, ω ∈ E a b}` where `E a b` is the
   scalar absolute-error event.
3. Apply `measurableSet_finset_all` first over `b`, then over `a`.
4. Discharge each scalar measurability goal with
   `measurableSet_referenceCovarianceEntryEvent`.
5. Finish the set equality by `ext ω; simp [EntrywiseClose]`.
-/
theorem measurableSet_referenceCovarianceEvent
    {d : Nat}
    (Pf : Measure (Model Q X))
    (ψ : Model Q X → Vec d) (hψ : Measurable ψ)
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (href : ∀ n i, Measurable fun ωref => f_ref n ωref i)
    (center : Vec d) (ε : Real) (n : Nat) :
    MeasurableSet (referenceCovarianceEvent Pf ψ f_ref center ε n) := by
  have hev : referenceCovarianceEvent Pf ψ f_ref center ε n =
      ⋂ (a : Fin d), ⋂ (b : Fin d),
        {ωref | |referenceEmpiricalCovariance ψ f_ref n ωref a b -
          perspectiveCovarianceMatrix Pf ψ center a b| ≤ ε} := by
    ext ωref
    simp only [referenceCovarianceEvent, EntrywiseClose, Set.mem_setOf_eq, Set.mem_iInter]
  rw [hev]
  exact MeasurableSet.iInter fun a => MeasurableSet.iInter fun b =>
    measurableSet_referenceCovarianceEntryEvent Pf ψ hψ f_ref href center ε n a b

/-- Scalar weak law for one empirical covariance entry.

For fixed coordinates `a,b`, combine
`highProb_referenceCoordinateMean_of_compact_iid` for both coordinates with
`highProb_referenceCoordinateProductMean_of_compact_iid`, then rewrite using
`referenceEmpiricalCovariance_entry_eq_product_sub_mean_mul_mean`.  Use
`hcenter` to identify the resulting population expression with
`perspectiveCovarianceMatrix`; without this mean-zero condition the statement
would be false for an arbitrary center.  The result remains pointwise in
`a,b`; the next theorem performs the fixed finite intersection.

Implementation recipe (execute in this order):
1. Choose a small scalar tolerance `δ > 0` so that errors of size `δ` in the
   product mean and the two coordinate means force covariance-entry error at
   most `ε`.  Use the compact perspective bound to bound the limiting means.
2. Obtain three high-probability events from
   `highProb_referenceCoordinateProductMean_of_compact_iid` and two applications
   of `highProb_referenceCoordinateMean_of_compact_iid`.
3. Intersect the three events using `HighProbAtTop.inter` twice; prove their
   measurability using the scalar measurable-map arguments from the preceding
   theorem.
4. On the intersection, rewrite the sample covariance using
   `referenceEmpiricalCovariance_entry_eq_product_sub_mean_mul_mean`.
5. Use `Hnondeg.center_is_mean`-style algebra supplied here as `hcenter` to show
   `∫ ψ_a ψ_b - (∫ψ_a)(∫ψ_b)` equals
   `perspectiveCovarianceMatrix Pf ψ center a b`.
6. Bound the difference of products with
   `|xy-x'y'| ≤ |x|*|y-y'| + |y'|*|x-x'|`, then close by the chosen `δ`.
7. Finally use event monotonicity to obtain the stated event.  Keep this theorem
   pointwise in `a,b`.
-/
theorem highProb_referenceCovarianceEntry_of_compact_iid
    {d : Nat}
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μref : Nat → Measure Ωref) (hμref : ∀ n, IsProbabilityMeasure (μref n))
    (ψ : Model Q X → Vec d) (hψ : Measurable ψ)
    (hcompact : IsCompact (Set.range ψ))
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (hiid : IIDReferenceSampler Pf μref f_ref)
    (center : Vec d)
    (hcenter : ∀ j, ∫ f, (ψ f - center) j ∂Pf = 0)
    (a b : Fin d) {ε : Real} (hε : 0 < ε) :
    HighProbAtTop μref hμref (fun n => {ωref |
      |referenceEmpiricalCovariance ψ f_ref n ωref a b -
        perspectiveCovarianceMatrix Pf ψ center a b| ≤ ε}) := by
  obtain ⟨B, hB0, hBbound⟩ := exists_perspective_norm_bound_of_isCompact_range ψ hcompact
  have hcma : Measurable (fun f => ψ f a) :=
    ((EuclideanSpace.proj a).continuous.measurable).comp hψ
  have hcmb : Measurable (fun f => ψ f b) :=
    ((EuclideanSpace.proj b).continuous.measurable).comp hψ
  have hbnd_a : ∀ f, |ψ f a| ≤ B := fun f => by
    rw [show |ψ f a| = ‖ψ f a‖ from (Real.norm_eq_abs _).symm]
    exact (PiLp.norm_apply_le (ψ f) a).trans (hBbound f)
  have hbnd_b : ∀ f, |ψ f b| ≤ B := fun f => by
    rw [show |ψ f b| = ‖ψ f b‖ from (Real.norm_eq_abs _).symm]
    exact (PiLp.norm_apply_le (ψ f) b).trans (hBbound f)
  have hInta : Integrable (fun f => ψ f a) Pf :=
    (MemLp.of_bound hcma.aestronglyMeasurable B
      (Eventually.of_forall fun f => by rw [Real.norm_eq_abs]; exact hbnd_a f)).integrable le_rfl
  have hIntb : Integrable (fun f => ψ f b) Pf :=
    (MemLp.of_bound hcmb.aestronglyMeasurable B
      (Eventually.of_forall fun f => by rw [Real.norm_eq_abs]; exact hbnd_b f)).integrable le_rfl
  have hIntab : Integrable (fun f => ψ f a * ψ f b) Pf :=
    (MemLp.of_bound (hcma.mul hcmb).aestronglyMeasurable (B * B)
      (Eventually.of_forall fun f => by
        simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hbnd_a f) (hbnd_b f) (abs_nonneg _) hB0)).integrable le_rfl
  have hpu : Pf.real Set.univ = 1 := by simp
  have hmeana : ∫ f, ψ f a ∂Pf = center a := by
    have h : ∫ f, (ψ f a - center a) ∂Pf = 0 := hcenter a
    rw [integral_sub hInta (integrable_const (center a)), integral_const, hpu, one_smul,
      sub_eq_zero] at h
    exact h
  have hmeanb : ∫ f, ψ f b ∂Pf = center b := by
    have h : ∫ f, (ψ f b - center b) ∂Pf = 0 := hcenter b
    rw [integral_sub hIntb (integrable_const (center b)), integral_const, hpu, one_smul,
      sub_eq_zero] at h
    exact h
  have hi1 : Integrable (fun f => center b * ψ f a) Pf := hInta.const_mul _
  have hi2 : Integrable (fun f => center a * ψ f b) Pf := hIntb.const_mul _
  have hpop : perspectiveCovarianceMatrix Pf ψ center a b
      = (∫ f, ψ f a * ψ f b ∂Pf) - (∫ f, ψ f a ∂Pf) * (∫ f, ψ f b ∂Pf) := by
    have hdef : perspectiveCovarianceMatrix Pf ψ center a b
        = ∫ f, (ψ f a - center a) * (ψ f b - center b) ∂Pf := rfl
    rw [hdef]
    have hexp : ∫ f, (ψ f a - center a) * (ψ f b - center b) ∂Pf
        = ∫ f, (ψ f a * ψ f b - center b * ψ f a - center a * ψ f b + center a * center b) ∂Pf :=
      integral_congr_ae (Eventually.of_forall fun f => by ring)
    have hI2 : Integrable (fun f => ψ f a * ψ f b - center b * ψ f a) Pf := hIntab.sub hi1
    have hI3 : Integrable
        (fun f => ψ f a * ψ f b - center b * ψ f a - center a * ψ f b) Pf := hI2.sub hi2
    rw [hexp, integral_add hI3 (integrable_const _),
      integral_sub hI2 hi2, integral_sub hIntab hi1,
      integral_const_mul, integral_const_mul, integral_const, hpu, one_smul,
      hmeana, hmeanb]
    ring
  set δ := min 1 (ε / (2 * (1 + B))) with hδdef
  have hδpos : 0 < δ := lt_min one_pos (by positivity)
  have hprod := highProb_referenceCoordinateProductMean_of_compact_iid Pf μref hμref ψ hψ
    hcompact f_ref hiid a b hδpos
  have hma := highProb_referenceCoordinateMean_of_compact_iid Pf μref hμref ψ hψ
    hcompact f_ref hiid a hδpos
  have hmb := highProb_referenceCoordinateMean_of_compact_iid Pf μref hμref ψ hψ
    hcompact f_ref hiid b hδpos
  have hmeasProd : ∀ n, MeasurableSet {ωref |
      |referenceCoordinateProductMean ψ f_ref n ωref a b - ∫ f, ψ f a * ψ f b ∂Pf| ≤ δ} := by
    intro n
    refine measurableSet_le (Measurable.abs (Measurable.sub ?_ measurable_const)) measurable_const
    simp only [referenceCoordinateProductMean]
    exact (Finset.measurable_sum _ (fun i _ =>
      (hcma.comp (hiid.measurable n i)).mul (hcmb.comp (hiid.measurable n i)))).const_mul _
  have hmeasA : ∀ n, MeasurableSet {ωref |
      |referenceCoordinateMean ψ f_ref n ωref a - ∫ f, ψ f a ∂Pf| ≤ δ} := by
    intro n
    refine measurableSet_le (Measurable.abs (Measurable.sub ?_ measurable_const)) measurable_const
    simp only [referenceCoordinateMean]
    exact (Finset.measurable_sum _ (fun i _ => hcma.comp (hiid.measurable n i))).const_mul _
  have hmeasB : ∀ n, MeasurableSet {ωref |
      |referenceCoordinateMean ψ f_ref n ωref b - ∫ f, ψ f b ∂Pf| ≤ δ} := by
    intro n
    refine measurableSet_le (Measurable.abs (Measurable.sub ?_ measurable_const)) measurable_const
    simp only [referenceCoordinateMean]
    exact (Finset.measurable_sum _ (fun i _ => hcmb.comp (hiid.measurable n i))).const_mul _
  have hinter := (hprod.inter hma hmeasProd hmeasA).inter hmb
    (fun n => (hmeasProd n).inter (hmeasA n)) hmeasB
  refine HighProbAtTop.mono hinter (fun n ωref hω => ?_)
  obtain ⟨⟨hωprod, hωa⟩, hωb⟩ := hω
  simp only [Set.mem_setOf_eq] at hωprod hωa hωb ⊢
  rw [referenceEmpiricalCovariance_entry_eq_product_sub_mean_mul_mean, hpop]
  set P := referenceCoordinateProductMean ψ f_ref n ωref a b
  set Ma := referenceCoordinateMean ψ f_ref n ωref a
  set Mb := referenceCoordinateMean ψ f_ref n ωref b
  set Ea := ∫ f, ψ f a ∂Pf
  set Eb := ∫ f, ψ f b ∂Pf
  set Eab := ∫ f, ψ f a * ψ f b ∂Pf
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : δ ≤ ε / (2 * (1 + B)) := min_le_right _ _
  have hEa : |Ea| ≤ B := by
    calc |Ea| ≤ ∫ f, |ψ f a| ∂Pf := abs_integral_le_integral_abs
      _ ≤ ∫ _f, B ∂Pf := integral_mono hInta.abs (integrable_const B) hbnd_a
      _ = B := by simp
  have hEb : |Eb| ≤ B := by
    calc |Eb| ≤ ∫ f, |ψ f b| ∂Pf := abs_integral_le_integral_abs
      _ ≤ ∫ _f, B ∂Pf := integral_mono hIntb.abs (integrable_const B) hbnd_b
      _ = B := by simp
  have hMa : |Ma| ≤ B + δ := by
    have hh : |Ma| ≤ |Ma - Ea| + |Ea| := by
      have := abs_add_le (Ma - Ea) Ea; rwa [sub_add_cancel] at this
    linarith [hωa]
  have hkey : |Ma * Mb - Ea * Eb| ≤ |Ma| * |Mb - Eb| + |Eb| * |Ma - Ea| := by
    have heq : Ma * Mb - Ea * Eb = Ma * (Mb - Eb) + Eb * (Ma - Ea) := by ring
    rw [heq]
    exact (abs_add_le _ _).trans (by rw [abs_mul, abs_mul])
  have htri : |P - Ma * Mb - (Eab - Ea * Eb)| ≤ |P - Eab| + |Ma * Mb - Ea * Eb| := by
    have heq : P - Ma * Mb - (Eab - Ea * Eb) = (P - Eab) + (-(Ma * Mb - Ea * Eb)) := by ring
    rw [heq]; exact (abs_add_le _ _).trans_eq (by rw [abs_neg])
  have h2 : |Ma * Mb - Ea * Eb| ≤ (B + δ) * δ + B * δ :=
    hkey.trans (add_le_add (mul_le_mul hMa hωb (abs_nonneg _) (by linarith))
      (mul_le_mul hEb hωa (abs_nonneg _) hB0))
  have hfinal : |P - Ma * Mb - (Eab - Ea * Eb)| ≤ δ + ((B + δ) * δ + B * δ) := by
    linarith [htri, hωprod, h2]
  refine hfinal.trans ?_
  have hstep : δ + ((B + δ) * δ + B * δ) ≤ δ * (2 * (1 + B)) := by nlinarith [hδ1, hδpos.le, hB0]
  refine hstep.trans ?_
  calc δ * (2 * (1 + B)) ≤ (ε / (2 * (1 + B))) * (2 * (1 + B)) :=
        mul_le_mul_of_nonneg_right hδε (by positivity)
    _ = ε := by field_simp

/-- Finite intersection of the scalar covariance-entry events.

Use `HighProbAtTop.finset_all` twice or induction over
`Finset.univ ×ˢ Finset.univ`.  The theorem deliberately accepts scalar-event
measurability because that is what the finite-intersection API requires.  Keep
the event equality explicit: after unfolding `referenceCovarianceEvent` and
`EntrywiseClose`, it is exactly the conjunction of the scalar entry events.

Implementation recipe (execute in this order):
1. Apply `HighProbAtTop.finset_all` to `Finset.univ : Finset (Fin d)` for the
   outer coordinate `a`.
2. For each `a`, apply it again to `Finset.univ : Finset (Fin d)` for `b`, using
   `hentry a b` and `hentryMeas a b`.
3. The resulting event is a nested finite conjunction.  Prove it equals
   `referenceCovarianceEvent ... ε` by extensionality and
   `simp [referenceCovarianceEvent, EntrywiseClose]`.
4. Rewrite by that function/event equality and return the finite-intersection
   result.  Do not reprove any probability estimate.
-/
theorem highProb_referenceCovarianceEvent_of_entries
    {d : Nat}
    (Pf : Measure (Model Q X))
    (μref : Nat → Measure Ωref) (hμref : ∀ n, IsProbabilityMeasure (μref n))
    (ψ : Model Q X → Vec d)
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (center : Vec d) {ε : Real}
    (hentry : ∀ a b : Fin d,
      HighProbAtTop μref hμref (fun n => {ωref |
        |referenceEmpiricalCovariance ψ f_ref n ωref a b -
          perspectiveCovarianceMatrix Pf ψ center a b| ≤ ε}))
    (hentryMeas : ∀ a b : Fin d, ∀ n,
      MeasurableSet {ωref |
        |referenceEmpiricalCovariance ψ f_ref n ωref a b -
          perspectiveCovarianceMatrix Pf ψ center a b| ≤ ε}) :
    HighProbAtTop μref hμref
      (referenceCovarianceEvent Pf ψ f_ref center ε) := by
  have key := HighProbAtTop.finset_all (Ω := Ωref)
    (Finset.univ : Finset (Fin d × Fin d))
    (fun p n => {ωref | |referenceEmpiricalCovariance ψ f_ref n ωref p.1 p.2 -
      perspectiveCovarianceMatrix Pf ψ center p.1 p.2| ≤ ε})
    (fun p _ => hentry p.1 p.2)
    (fun p _ n => hentryMeas p.1 p.2 n)
  have heq : (fun n => {ωref | ∀ p ∈ (Finset.univ : Finset (Fin d × Fin d)),
      ωref ∈ {ωref | |referenceEmpiricalCovariance ψ f_ref n ωref p.1 p.2 -
        perspectiveCovarianceMatrix Pf ψ center p.1 p.2| ≤ ε}})
      = referenceCovarianceEvent Pf ψ f_ref center ε := by
    funext n
    ext ωref
    simp only [referenceCovarianceEvent, EntrywiseClose, Set.mem_setOf_eq, Finset.mem_univ,
      forall_true_left, Prod.forall]
  rw [← heq]
  exact key

/-- Fixed-dimensional weak law for all covariance entries simultaneously.

This is the probability-heavy obligation in the spectral track.  A direct
proof is sufficient:

1. prove the empirical coordinate means converge to the population center;
2. prove the empirical coordinate products converge to their expectations;
3. expand the sample-centered covariance as second moment minus mean product;
4. combine the scalar limits and intersect over `Fin d × Fin d`.

Use `hcenter` when identifying the covariance limit.  There is no need for a
sharp matrix Bernstein inequality.  The purpose is to remove an unrealistic
global spectral hypothesis, not optimize constants.

Implementation recipe (execute in this order):
1. For each `a,b`, call
   `highProb_referenceCovarianceEntry_of_compact_iid` with the common tolerance
   `ε` and `hε`.
2. Prove each scalar event measurable with
   `measurableSet_referenceCovarianceEntryEvent`, using `hiid.measurable` for the
   reference maps.
3. Pass these two families to
   `highProb_referenceCovarianceEvent_of_entries`.
4. This theorem should be a short composition.  If it grows beyond a few dozen
   lines, missing details belong in the scalar-entry theorem.
-/
theorem highProb_referenceCovarianceEvent_of_compact_iid
    {d : Nat}
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μref : Nat → Measure Ωref) (hμref : ∀ n, IsProbabilityMeasure (μref n))
    (ψ : Model Q X → Vec d) (hψ : Measurable ψ)
    (hcompact : IsCompact (Set.range ψ))
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (hiid : IIDReferenceSampler Pf μref f_ref)
    (center : Vec d)
    (hcenter : ∀ j, ∫ f, (ψ f - center) j ∂Pf = 0)
    {ε : Real} (hε : 0 < ε) :
    HighProbAtTop μref hμref
      (referenceCovarianceEvent Pf ψ f_ref center ε) :=
  highProb_referenceCovarianceEvent_of_entries Pf μref hμref ψ f_ref center
    (fun a b => highProb_referenceCovarianceEntry_of_compact_iid Pf μref hμref ψ hψ
      hcompact f_ref hiid center hcenter a b hε)
    (fun a b n => measurableSet_referenceCovarianceEntryEvent Pf ψ hψ f_ref
      hiid.measurable center ε n a b)

/-- Convert the entrywise covariance event into the quadratic-form
floor needed by the reference-scatter theorem.

Unfold `referenceEmpiricalCovariance`, expand the quadratic form, and exchange
the finite sums.  The resulting expression is the average of squared inner
products with the sample-centered reference configuration.  Apply
`empiricalCovariance_quadratic_floor_of_entrywise` to the event membership.

Implementation recipe (execute in this order):
1. Unfold membership in `referenceCovarianceEvent` to obtain the `EntrywiseClose`
   premise needed by `empiricalCovariance_quadratic_floor_of_entrywise`.
2. Apply that theorem with
   `A := referenceEmpiricalCovariance ψ f_ref n ωref` and the given `x`.
3. Unfold `referenceEmpiricalCovariance` in the resulting quadratic form.
4. Exchange the finite sums over `a,b,i`; for each `i`, recognize
   `∑ a, x a * centerConfig ... i a` as the real inner product
   `⟪x, centerConfig ... i⟫_ℝ`.
5. Rewrite the product of the two identical sums as the square and normalize the
   outer `(n : Real)⁻¹`.
6. Use `ring` after the finite-sum rearrangement.  No probability argument is
   needed once `hω` is supplied.
-/
theorem reference_centered_quadratic_floor_of_event
    {d n : Nat}
    (Pf : Measure (Model Q X))
    (ψ : Model Q X → Vec d)
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    {κ : Real}
    (Hnondeg : PerspectiveNondegeneracy Pf ψ κ)
    (ωref : Ωref)
    (hω : ωref ∈ referenceCovarianceEvent Pf ψ f_ref (perspectiveMean Pf ψ)
      (covarianceEntryTolerance d κ) n)
    (x : Vec d) :
    (κ / 2) * ‖x‖ ^ 2 ≤
      (n : Real)⁻¹ * ∑ i : Fin n,
        ((∑ a : Fin d, x a * centerConfig
          (referencePerspectiveConfig ψ f_ref n ωref) i a)) ^ 2 := by
  change EntrywiseClose
    (referenceEmpiricalCovariance ψ f_ref n ωref)
    (perspectiveCovarianceMatrix Pf ψ (perspectiveMean Pf ψ))
    (covarianceEntryTolerance d κ) at hω
  have href :
      referenceEmpiricalCovariance ψ f_ref n ωref =
        centeredEmpiricalCovariance
          (referencePerspectiveConfig ψ f_ref n ωref) := by
    rfl
  rw [href] at hω
  apply centeredEmpiricalCovariance_quadratic_floor_of_entrywise
    (Pf := Pf) (ψ := ψ) Hnondeg
    (z := referencePerspectiveConfig ψ f_ref n ωref)
  exact hω

/-- Usable reference-scatter spectral floor.

The normalized quadratic floor is scaled by `n` into an unnormalized floor
`n(κ/2)‖x‖² ≤ ∑ᵢ ⟪x, zᵢ⟫²` and handed to the rectangular Gram bridge
`sortedEigenvalues_configGram_lower_of_quadratic_floor`: the configuration Gram
matrix is the codomain Gram operator `TT†` of the analysis map `T` of `zref`,
whose first `d` sorted eigenvalues dominate any quadratic floor of `T†T`.
For `κ ≤ 0` the claim is positive semidefiniteness; for `κ > 0` the floor
`κ/2 ≤ n·κ/2` uses `1 ≤ n`. -/
theorem sortedEigenvalues_reference_centeredGram_lower
    {d n : Nat} (hn : 0 < n)
    (zref : Config n d) {κ : Real}
    (hquad : ∀ x : Vec d,
      (κ / 2) * ‖x‖ ^ 2 ≤
        (n : Real)⁻¹ * ∑ i, ((∑ a : Fin d, x a * zref i a)) ^ 2)
    (i : Fin n) (hi : (i : Nat) < d) :
    κ / 2 ≤ sortedEigenvalues
      (configGramPosSemidef zref).isHermitian i := by
  rcases le_or_gt κ 0 with hκ | hκ
  · exact le_trans (by linarith) (sortedEigenvalues_nonneg (configGramPosSemidef zref) i)
  · have hnpos : (0 : Real) < (n : Real) := by exact_mod_cast hn
    have hn1 : (1 : Real) ≤ (n : Real) := by exact_mod_cast hn
    have hquad' : ∀ x : Vec d,
        ((n : Real) * (κ / 2)) * ‖x‖ ^ 2 ≤
          ∑ j : Fin n, (∑ a : Fin d, x a * zref j a) ^ 2 := by
      intro x
      calc ((n : Real) * (κ / 2)) * ‖x‖ ^ 2
          = (n : Real) * ((κ / 2) * ‖x‖ ^ 2) := by ring
        _ ≤ (n : Real) * ((n : Real)⁻¹ *
              ∑ j : Fin n, (∑ a : Fin d, x a * zref j a) ^ 2) :=
            mul_le_mul_of_nonneg_left (hquad x) hnpos.le
        _ = ∑ j : Fin n, (∑ a : Fin d, x a * zref j a) ^ 2 := by
            rw [← mul_assoc, mul_inv_cancel₀ hnpos.ne', one_mul]
    have hfloor := sortedEigenvalues_configGram_lower_of_quadratic_floor hquad' i hi
    have hgrow : κ / 2 ≤ (n : Real) * (κ / 2) := by nlinarith
    linarith

/-- Adding the target and recentering the enlarged cloud cannot decrease the
reference scatter in any perspective direction.

The proof is the online-variance route through the rectangular Gram bridge:
`quadratic_floor_of_sortedEigenvalues_configGram_lower` converts `href` (with
`d ≤ n`) back into the quadratic floor of the centered reference cloud;
`sum_sq_centered_le_augmented` — the exact add-one centered-scatter identity
`ForMathlib.centeredScatter_append` — shows the augmented centered
squared-projection sum dominates it by the nonnegative rank-one correction
`(n/(n+1)) ⟪x, target - centroid⟫²`; and
`sortedEigenvalues_configGram_lower_of_quadratic_floor` transfers the floor to
the first `d` sorted eigenvalues of the augmented centered Gram matrix.  The
premise `d ≤ n` is essential: without it the augmented cloud can introduce a
new index below `d` for which the reference cloud supplied no lower bound. -/
theorem augmented_centeredGram_floor_of_reference_floor
    {d n : Nat} (hn : 0 < n) (hdn : d ≤ n)
    (ψref : Fin n → Vec d) (target : Vec d) {α : Real}
    (href : ∀ i : Fin n, (i : Nat) < d →
      α ≤ sortedEigenvalues
        (configGramPosSemidef (centerConfig ψref)).isHermitian i)
    (i : Fin (n + 1)) (hi : (i : Nat) < d) :
    α ≤ sortedEigenvalues
      (configGramPosSemidef (centerConfig (Fin.lastCases target ψref))).isHermitian i := by
  have hquad_ref := quadratic_floor_of_sortedEigenvalues_configGram_lower hdn href
  have hquad_aug : ∀ x : Vec d,
      α * ‖x‖ ^ 2 ≤ ∑ j : Fin (n + 1),
        (∑ a : Fin d, x a * centerConfig (Fin.lastCases target ψref) j a) ^ 2 :=
    fun x => (hquad_ref x).trans (sum_sq_centered_le_augmented ψref target x)
  exact sortedEigenvalues_configGram_lower_of_quadratic_floor hquad_aug i hi

/-- A uniform perspective norm bound gives a deterministic linear-in-`n`
ceiling for every eigenvalue of the augmented centered Gram matrix.

Suggested proof route: top eigenvalue is at most the trace for a PSD matrix;
the trace is the sum of squared centered norms; each centered point has norm at
most `2B`.  Loose constants are preferred over adding hypotheses.

Implementation recipe (execute in this order):
1. Use PSD to bound every sorted eigenvalue by the largest eigenvalue, and bound
   the largest eigenvalue by the trace.  Search for
   `sortedEigenvalues_le_trace` or combine `eigenvalue_le_trace` with PSD.
2. Rewrite the trace of `configGram (centerConfig points)` as
   `∑ i, ‖centerConfig points i‖²` by expanding diagonal entries.
3. Prove the centroid has norm at most `B` because it is an average of points
   bounded by `B` (the batch is nonempty).
4. Hence each centered point has norm at most `2*B`; square to obtain
   `≤ 4*B²`.
5. Sum over `n+1` points and simplify the constant sum to the stated ceiling.
6. If a direct trace theorem is unavailable, use the Rayleigh quotient bound
   `λmax ≤ frobNorm` and prove the same loose ceiling.  Do not add a separate
   centroid bound hypothesis.
-/
theorem sortedEigenvalues_augmented_centeredGram_upper
    {d n : Nat}
    (points : Config (n + 1) d) {B : Real}
    (hBnonneg : 0 ≤ B)
    (hB : ∀ i, ‖points i‖ ≤ B)
    (i : Fin (n + 1)) :
    sortedEigenvalues
      (configGramPosSemidef (centerConfig points)).isHermitian i ≤
      4 * ((n + 1 : Nat) : Real) * B ^ 2 := by
  have hinner : ∀ x y : Vec d, @inner ℝ _ _ x y = ∑ k, x k * y k := by
    intro x y
    rw [PiLp.inner_apply]
    simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hcent : ‖configCentroid points‖ ≤ B := by
    rw [configCentroid, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ)⁻¹)]
    calc ((n + 1 : ℕ) : ℝ)⁻¹ * ‖∑ i, points i‖
        ≤ ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ i, ‖points i‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
      _ ≤ ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ _i : Fin (n + 1), B :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hB i) (by positivity)
      _ = B := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← mul_assoc, inv_mul_cancel₀ (by positivity : ((n + 1 : ℕ) : ℝ) ≠ 0), one_mul]
  have hcnorm : ∀ a, ‖centerConfig points a‖ ≤ 2 * B := by
    intro a
    calc ‖centerConfig points a‖ = ‖points a - configCentroid points‖ := rfl
      _ ≤ ‖points a‖ + ‖configCentroid points‖ := norm_sub_le _ _
      _ ≤ B + B := add_le_add (hB a) hcent
      _ = 2 * B := by ring
  have hentry : ∀ a b,
      |configGram (centerConfig points) a b| ≤ 4 * B ^ 2 := by
    intro a b
    have h1 : configGram (centerConfig points) a b
        = @inner ℝ _ _ (centerConfig points a) (centerConfig points b) := by
      simp only [configGram]
      exact (hinner _ _).symm
    rw [h1]
    calc |@inner ℝ _ _ (centerConfig points a) (centerConfig points b)|
        ≤ ‖centerConfig points a‖ * ‖centerConfig points b‖ := abs_real_inner_le_norm _ _
      _ ≤ 2 * B * (2 * B) := mul_le_mul (hcnorm a) (hcnorm b) (norm_nonneg _) (by positivity)
      _ = 4 * B ^ 2 := by ring
  calc sortedEigenvalues (configGramPosSemidef (centerConfig points)).isHermitian i
      ≤ ((n + 1 : ℕ) : ℝ) * (4 * B ^ 2) :=
        sortedEigenvalues_le_of_entry_le
          (configGramPosSemidef (centerConfig points)).isHermitian hentry i
    _ = 4 * ((n + 1 : Nat) : ℝ) * B ^ 2 := by ring

set_option maxHeartbeats 1000000 in
/-- Assemble the covariance weak law and deterministic Gram lemmas into the
high-probability spectral certificate consumed by the new Quench capstone.

This theorem dispatches the old global `hfloor`, `hceiling`, and caller-chosen
`ceiling` inputs; the only lower-spectrum assumption remaining is
`PerspectiveNondegeneracy`.  The certificate event is the entrywise covariance
event (tolerance `covarianceEntryTolerance d κ` about the population mean)
intersected with the deterministic dimension gate `d ≤ n ∧ 0 < n`, which is
eventually true and needed by the augmentation floor.  On the event, the
`floor` field chains `reference_centered_quadratic_floor_of_event`,
`sortedEigenvalues_reference_centeredGram_lower`, and
`augmented_centeredGram_floor_of_reference_floor`, then rewrites the augmented
centered Gram matrix to the population CMDS matrix via
`centeredAugmentedPerspectiveConfig_gram_eq`.  The `ceiling_bound` field is
`sortedEigenvalues_augmented_centeredGram_upper` with the compactness envelope
`B`, giving `ceiling n := 4(n+1)B²`. -/
theorem exists_growingSpectralSubevents_of_compact_iid_nondegenerate
    {d m p : Nat}
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μref : Nat → Measure Ωref) (hμref : ∀ n, IsProbabilityMeasure (μref n))
    (ψ : Model Q X → Vec d) (hψ : Measurable ψ)
    (hcompact : IsCompact (Set.range ψ))
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (hiid : IIDReferenceSampler Pf μref f_ref)
    (μbar : ∀ n, Ωref → Model Q X → Fin (n + 1) → Acharyya2024.Mat m p)
    (hrealize : PerspectiveResponseRealization ψ f_ref μbar)
    {κ : Real} (Hnondeg : PerspectiveNondegeneracy Pf ψ κ) :
    ∃ B : Real, 0 ≤ B ∧ (∀ f, ‖ψ f‖ ≤ B) ∧
      Nonempty (GrowingSpectralSubevents μref hμref
        (fun n ωref f => responseDist (μbar n ωref f))
        (centeredAugmentedPerspectiveConfig ψ f_ref)
        (centeredAugmentedPerspectiveConfig_gram_eq
          ψ f_ref μbar hrealize)
        (κ / 2)
        (fun n => 4 * ((n + 1 : Nat) : Real) * B ^ 2)) := by
  obtain ⟨B, hB0, hBbound⟩ := exists_perspective_norm_bound_of_isCompact_range ψ hcompact
  refine ⟨B, hB0, hBbound, ?_⟩
  have hε : 0 < covarianceEntryTolerance d κ := by
    have := Hnondeg.kappa_pos
    unfold covarianceEntryTolerance
    positivity
  set center := perspectiveMean Pf ψ with hcenter_def
  set ε := covarianceEntryTolerance d κ with hε_def
  -- The certificate event: covariance closeness plus the deterministic dimension gate.
  set event : Nat → Set Ωref := fun n =>
    referenceCovarianceEvent Pf ψ f_ref center ε n ∩ {_ωref | d ≤ n ∧ 0 < n}
    with hevent_def
  have hcovMeas : ∀ n, MeasurableSet (referenceCovarianceEvent Pf ψ f_ref center ε n) :=
    fun n => measurableSet_referenceCovarianceEvent Pf ψ hψ f_ref hiid.measurable center ε n
  have hgateMeas : ∀ n : Nat, MeasurableSet ({_ωref | d ≤ n ∧ 0 < n} : Set Ωref) :=
    fun n => MeasurableSet.const _
  have hcovHP : HighProbAtTop μref hμref
      (referenceCovarianceEvent Pf ψ f_ref center ε) :=
    highProb_referenceCovarianceEvent_of_compact_iid Pf μref hμref ψ hψ hcompact
      f_ref hiid center Hnondeg.center_is_mean hε
  have hgateHP : HighProbAtTop μref hμref
      (fun n => ({_ωref | d ≤ n ∧ 0 < n} : Set Ωref)) := by
    intro δ hδ
    refine ⟨d + 1, fun n hn => ?_⟩
    haveI := hμref n
    have hset : ({_ωref | d ≤ n ∧ 0 < n} : Set Ωref) = Set.univ := by
      have h1 : d ≤ n := by omega
      have h2 : 0 < n := by omega
      ext ωref
      simp [h1, h2]
    show μref n ({_ωref | d ≤ n ∧ 0 < n} : Set Ωref) ≥ 1 - δ
    rw [hset, measure_univ]
    exact tsub_le_self
  -- Transfer between the population CMDS matrix and the centered augmented Gram matrix.
  have hmat : ∀ (n : Nat) (ωref : Ωref) (f : Model Q X),
      disMatToMatrix (classicalMDSMatrix (responseDist (μbar n ωref f))) =
        disMatToMatrix (configGram
          (centeredAugmentedPerspectiveConfig ψ f_ref n ωref f)) :=
    fun n ωref f => Matrix.ext fun i j =>
      (centeredAugmentedPerspectiveConfig_gram_eq ψ f_ref μbar hrealize n ωref f i j).symm
  refine ⟨⟨event, ?_, ?_, ?_, ?_⟩⟩
  · exact fun n => (hcovMeas n).inter (hgateMeas n)
  · exact HighProbAtTop.inter hcovHP hgateHP hcovMeas hgateMeas
  · -- Spectral floor on the first `d` eigenvalues of the augmented CMDS matrix.
    rintro n ωref ⟨hcov, hdn, hn0⟩ f i hi
    have hquadref := reference_centered_quadratic_floor_of_event Pf ψ f_ref Hnondeg ωref hcov
    have href : ∀ j : Fin n, (j : Nat) < d →
        κ / 2 ≤ sortedEigenvalues (configGramPosSemidef
          (centerConfig (referencePerspectiveConfig ψ f_ref n ωref))).isHermitian j :=
      fun j hj => sortedEigenvalues_reference_centeredGram_lower hn0
        (centerConfig (referencePerspectiveConfig ψ f_ref n ωref)) hquadref j hj
    have haug := augmented_centeredGram_floor_of_reference_floor hn0 hdn
      (referencePerspectiveConfig ψ f_ref n ωref) (ψ f) href i hi
    have haugcfg : augmentedPerspectiveConfig ψ f_ref n ωref f =
        Fin.lastCases (ψ f) (referencePerspectiveConfig ψ f_ref n ωref) := by
      funext j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · show ψ (augmentedModelAt f_ref n ωref f (Fin.last n)) = _
        rw [Fin.lastCases_last]
        show ψ (Fin.lastCases f (f_ref n ωref) (Fin.last n)) = ψ f
        rw [Fin.lastCases_last]
      · show ψ (augmentedModelAt f_ref n ωref f j.castSucc) = _
        rw [Fin.lastCases_castSucc]
        show ψ (Fin.lastCases f (f_ref n ωref) j.castSucc) = _
        rw [Fin.lastCases_castSucc]
        rfl
    have hcfgmat : disMatToMatrix (configGram (centerConfig
          (Fin.lastCases (ψ f) (referencePerspectiveConfig ψ f_ref n ωref)))) =
        disMatToMatrix (classicalMDSMatrix (responseDist (μbar n ωref f))) := by
      rw [← haugcfg]
      exact (hmat n ωref f).symm
    convert haug using 2
    exact hcfgmat.symm
  · -- Trace-style deterministic ceiling for every eigenvalue.
    rintro n ωref - f i
    have hpoints : ∀ j, ‖augmentedPerspectiveConfig ψ f_ref n ωref f j‖ ≤ B :=
      fun j => hBbound _
    have hupper := sortedEigenvalues_augmented_centeredGram_upper
      (augmentedPerspectiveConfig ψ f_ref n ωref f) hB0 hpoints i
    convert hupper using 2
    exact hmat n ωref f

end DkpsQuench2026

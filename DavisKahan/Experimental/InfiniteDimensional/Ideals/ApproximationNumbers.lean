/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.Core.UnboundedSpectral
import DavisKahan.Experimental.InfiniteDimensional.Ideals.Rectangular

/-!
# Approximation numbers and strong spectral cutoffs

The zero-based approximation number `a n T` is the distance from `T` to maps
of rank at most `n`.  Thus `a 0 T = ‖T‖`.  Finite Ky Fan gauges are sums of
the first approximation numbers.  These are the finite-dimensional probes used
in the cutoff passage of Davis--Kahan Theorem 5.2.
-/

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open scoped InnerProductSpace Topology
open Filter

universe u v w

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Strong operator convergence expressed pointwise. -/
def StronglyTendsto {ι : Type w} (T : ι → E →L[𝕜] E)
    (l : Filter ι) (S : E →L[𝕜] E) : Prop :=
  ∀ x, Tendsto (fun i => T i x) l (𝓝 (S x))

/-- Orthogonal projection predicate for bounded operators. -/
def IsOrthogonalProjectionMap (P : E →L[𝕜] E) : Prop :=
  P ∘L P = P ∧ P.IsSymmetric

/-- Zero-based approximation singular value: distance to rank at most `n`. -/
noncomputable def approximationSingularValue
    (n : ℕ) (K : E →L[𝕜] F) : ℝ :=
  sInf {r : ℝ | ∃ R : E →L[𝕜] F,
    Module.finrank 𝕜 (LinearMap.range R.toLinearMap) ≤ n ∧ ‖K - R‖ ≤ r}

private theorem approximationSet_nonempty
    (n : ℕ) (K : E →L[𝕜] F) :
    {r : ℝ | ∃ R : E →L[𝕜] F,
      Module.finrank 𝕜 (LinearMap.range R.toLinearMap) ≤ n ∧ ‖K - R‖ ≤ r}.Nonempty := by
  refine ⟨‖K‖, 0, by simp, ?_⟩
  simpa using le_rfl

private theorem approximationSet_bddBelow
    (n : ℕ) (K : E →L[𝕜] F) :
    BddBelow {r : ℝ | ∃ R : E →L[𝕜] F,
      Module.finrank 𝕜 (LinearMap.range R.toLinearMap) ≤ n ∧ ‖K - R‖ ≤ r} := by
  refine ⟨0, ?_⟩
  rintro r ⟨R, -, hR⟩
  exact (norm_nonneg (K - R)).trans hR

/-- Approximation singular values are nonnegative. -/
theorem approximationSingularValue_nonneg
    (n : ℕ) (K : E →L[𝕜] F) :
    0 ≤ approximationSingularValue n K := by
  unfold approximationSingularValue
  exact csInf_nonneg (by
    rintro r ⟨R, -, hR⟩
    exact (norm_nonneg (K - R)).trans hR)

/-- An individual rank approximation bounds the approximation number. -/
theorem approximationSingularValue_le_of_rank
    (n : ℕ) (K R : E →L[𝕜] F)
    (hR : Module.finrank 𝕜 (LinearMap.range R.toLinearMap) ≤ n) :
    approximationSingularValue n K ≤ ‖K - R‖ := by
  unfold approximationSingularValue
  exact csInf_le (approximationSet_bddBelow n K) ⟨R, hR, le_rfl⟩

/-- Every value strictly above the infimum is realized up to that value. -/
theorem exists_rank_approximation_lt
    (n : ℕ) (K : E →L[𝕜] F) {r : ℝ}
    (hr : approximationSingularValue n K < r) :
    ∃ R : E →L[𝕜] F,
      Module.finrank 𝕜 (LinearMap.range R.toLinearMap) ≤ n ∧ ‖K - R‖ < r := by
  unfold approximationSingularValue at hr
  obtain ⟨q, hq, hqr⟩ := exists_lt_of_csInf_lt
    (approximationSet_nonempty n K) hr
  rcases hq with ⟨R, hRrank, hRnorm⟩
  exact ⟨R, hRrank, hRnorm.trans_lt hqr⟩

/-- The zero-based first approximation singular value is the operator norm. -/
theorem approximationSingularValue_zero
    (K : E →L[𝕜] F) :
    approximationSingularValue 0 K = ‖K‖ := by
  apply le_antisymm
  · simpa using approximationSingularValue_le_of_rank 0 K 0 (by simp)
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨R, hRrank, hR⟩ := exists_rank_approximation_lt 0 K
      (show approximationSingularValue 0 K <
          approximationSingularValue 0 K + ε by linarith)
    have hRzero : R = 0 := by
      apply ContinuousLinearMap.ext
      intro x
      have hrange : LinearMap.range R.toLinearMap = ⊥ :=
        Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hRrank)
      have : R x ∈ LinearMap.range R.toLinearMap :=
        LinearMap.mem_range_self _ x
      simpa [hrange] using this
    subst R
    simpa using le_of_lt hR

/-- Approximation singular values are absolutely homogeneous. -/
theorem approximationSingularValue_smul
    (n : ℕ) (c : 𝕜) (K : E →L[𝕜] F) :
    approximationSingularValue n (c • K) =
      ‖c‖ * approximationSingularValue n K := by
  have scale_le : ∀ (a : 𝕜) (T : E →L[𝕜] F),
      approximationSingularValue n (a • T) ≤
        ‖a‖ * approximationSingularValue n T := by
    intro a T
    by_cases ha : a = 0
    · subst a
      simp [approximationSingularValue_nonneg]
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨R, hRrank, hR⟩ := exists_rank_approximation_lt n T
      (show approximationSingularValue n T <
          approximationSingularValue n T + ε / ‖a‖ by positivity)
    have hrank : Module.finrank 𝕜
        (LinearMap.range (a • R).toLinearMap) ≤ n :=
      (finrank_range_smul_le a R).trans hRrank
    calc
      approximationSingularValue n (a • T)
          ≤ ‖a • T - a • R‖ :=
        approximationSingularValue_le_of_rank n _ _ hrank
      _ = ‖a‖ * ‖T - R‖ := by rw [← smul_sub, norm_smul]
      _ < ‖a‖ * (approximationSingularValue n T + ε / ‖a‖) := by
        gcongr
      _ = ‖a‖ * approximationSingularValue n T + ε := by
        field_simp [norm_ne_zero_iff.mpr ha]
  by_cases hc : c = 0
  · subst c
    simp [approximationSingularValue_nonneg]
  apply le_antisymm
  · exact scale_le c K
  · have hback := scale_le c⁻¹ (c • K)
    rw [inv_smul_smul₀ hc, norm_inv] at hback
    have hcNorm : 0 < ‖c‖ := norm_pos_iff.mpr hc
    nlinarith [mul_inv_cancel₀ (ne_of_gt hcNorm)]

/-- Approximation singular values decrease with the index. -/
theorem approximationSingularValue_antitone
    (K : E →L[𝕜] F) :
    Antitone (fun n => approximationSingularValue n K) := by
  intro m n hmn
  unfold approximationSingularValue
  apply csInf_le_csInf
  · exact approximationSet_nonempty m K
  · exact approximationSet_bddBelow n K
  · rintro r ⟨R, hRrank, hRnorm⟩
    exact ⟨R, hRrank.trans hmn, hRnorm⟩

/-- Every approximation singular value is bounded by operator norm. -/
theorem approximationSingularValue_le_opNorm
    (n : ℕ) (K : E →L[𝕜] F) :
    approximationSingularValue n K ≤ ‖K‖ := by
  simpa using approximationSingularValue_le_of_rank n K 0 (by simp)

/-- Adjoint invariance of approximation singular values. -/
theorem approximationSingularValue_adjoint
    (n : ℕ) (K : E →L[𝕜] F) :
    approximationSingularValue n K.adjoint =
      approximationSingularValue n K := by
  have adjoint_le : ∀ (T : E →L[𝕜] F),
      approximationSingularValue n T.adjoint ≤
        approximationSingularValue n T := by
    intro T
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨R, hRrank, hR⟩ := exists_rank_approximation_lt n T
      (show approximationSingularValue n T <
          approximationSingularValue n T + ε by linarith)
    have hrank : Module.finrank 𝕜
        (LinearMap.range R.adjoint.toLinearMap) ≤ n := by
      simpa [finrank_range_adjoint] using hRrank
    calc
      approximationSingularValue n T.adjoint
          ≤ ‖T.adjoint - R.adjoint‖ :=
        approximationSingularValue_le_of_rank n _ _ hrank
      _ = ‖T - R‖ := by
        rw [← ContinuousLinearMap.adjoint_sub, ContinuousLinearMap.norm_adjoint]
      _ < approximationSingularValue n T + ε := hR
  apply le_antisymm
  · exact adjoint_le K
  · have h := adjoint_le K.adjoint
    simpa using h

/-- Two-sided ideal inequality for approximation singular values. -/
theorem approximationSingularValue_comp_le
    {G H : Type v}
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (n : ℕ) (L : F →L[𝕜] G) (K : E →L[𝕜] F)
    (R : H →L[𝕜] E) :
    approximationSingularValue n (L ∘L K ∘L R)
      ≤ ‖L‖ * approximationSingularValue n K * ‖R‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨S, hSrank, hS⟩ := exists_rank_approximation_lt n K
    (show approximationSingularValue n K <
        approximationSingularValue n K +
          ε / ((‖L‖ + 1) * (‖R‖ + 1)) by positivity)
  have hrank : Module.finrank 𝕜
      (LinearMap.range (L ∘L S ∘L R).toLinearMap) ≤ n :=
    (finrank_range_comp_left_right_le L S R).trans hSrank
  calc
    approximationSingularValue n (L ∘L K ∘L R)
        ≤ ‖L ∘L K ∘L R - L ∘L S ∘L R‖ :=
      approximationSingularValue_le_of_rank n _ _ hrank
    _ = ‖L ∘L (K - S) ∘L R‖ := by module
    _ ≤ ‖L‖ * ‖K - S‖ * ‖R‖ :=
      ContinuousLinearMap.opNorm_comp_comp_le _ _ _
    _ ≤ ‖L‖ * approximationSingularValue n K * ‖R‖ + ε := by
      have hL : ‖L‖ ≤ ‖L‖ + 1 := by linarith [norm_nonneg L]
      have hR : ‖R‖ ≤ ‖R‖ + 1 := by linarith [norm_nonneg R]
      nlinarith [hS, norm_nonneg L, norm_nonneg R]

/-- Orthogonal projections have operator norm at most one. -/
theorem opNorm_le_one_of_isOrthogonalProjectionMap
    {P : E →L[𝕜] E} (hP : IsOrthogonalProjectionMap P) : ‖P‖ ≤ 1 := by
  exact ContinuousLinearMap.opNorm_le_one_of_isSymmetricProjection hP.2 hP.1

/-- Continuity of each fixed approximation number under strongly convergent
orthogonal cutoffs. -/
theorem approximationSingularValue_comp_strongProjection_tendsto
    {ι : Type w} {P : ι → E →L[𝕜] E} {l : Filter ι}
    (hPproj : ∀ i, IsOrthogonalProjectionMap (P i))
    (hP : StronglyTendsto P l (ContinuousLinearMap.id 𝕜 E))
    (n : ℕ) (K : E →L[𝕜] F) :
    Tendsto
      (fun i => approximationSingularValue n (K ∘L P i))
      l (𝓝 (approximationSingularValue n K)) := by
  rw [Metric.tendsto_iff]
  intro ε hε
  -- The upper estimate follows from the ideal inequality and `‖P i‖ ≤ 1`.
  have hupper : ∀ i,
      approximationSingularValue n (K ∘L P i) ≤
        approximationSingularValue n K := by
    intro i
    simpa using approximationSingularValue_comp_le n
      (ContinuousLinearMap.id 𝕜 F) K (P i) |>.trans
        (by gcongr; exact opNorm_le_one_of_isOrthogonalProjectionMap (hPproj i))
  -- For the lower estimate use the min--max characterization on an
  -- `(n+1)`-dimensional almost maximizing subspace.  Strong convergence is
  -- uniform on its compact unit sphere, so `P i` is eventually uniformly
  -- close to the identity there.
  obtain ⟨M, hMdim, hMmin⟩ :=
    approximationSingularValue_minmax_almost_attained K n (ε / 2) (by positivity)
  have hUniform : Tendsto
      (fun i => ‖(P i - 1).domRestrict M‖) l (𝓝 0) :=
    finiteDimensional_uniform_of_strong_tendsto M hMdim hP
  filter_upwards [hUniform.eventually (Metric.ball_mem_nhds 0 (ε / (2 * (‖K‖ + 1)))
    (by positivity))] with i hi
  have hlower : approximationSingularValue n K - ε <
      approximationSingularValue n (K ∘L P i) := by
    apply lt_of_lt_of_le hMmin
    exact minmax_stability_on_subspace K (P i) M hMdim hi
  rw [Real.dist_eq]
  exact abs_lt.2 ⟨by linarith, by linarith [hupper i]⟩

/-- Finite Ky Fan gauge built from approximation singular values. -/
noncomputable def kyFanApproximationGauge
    (k : ℕ) (K : E →L[𝕜] F) : ℝ :=
  ∑ n ∈ Finset.range k, approximationSingularValue n K

/-- Ky Fan approximation gauges are absolutely homogeneous. -/
theorem kyFanApproximationGauge_smul
    (k : ℕ) (c : 𝕜) (K : E →L[𝕜] F) :
    kyFanApproximationGauge k (c • K) =
      ‖c‖ * kyFanApproximationGauge k K := by
  simp [kyFanApproximationGauge, approximationSingularValue_smul,
    Finset.mul_sum]

/-- Ky Fan approximation gauges are nonnegative. -/
theorem kyFanApproximationGauge_nonneg
    (k : ℕ) (K : E →L[𝕜] F) :
    0 ≤ kyFanApproximationGauge k K := by
  exact Finset.sum_nonneg fun n hn => approximationSingularValue_nonneg n K

/-- Ky Fan approximation gauges are invariant under adjoint. -/
theorem kyFanApproximationGauge_adjoint
    (k : ℕ) (K : E →L[𝕜] F) :
    kyFanApproximationGauge k K.adjoint =
      kyFanApproximationGauge k K := by
  simp [kyFanApproximationGauge, approximationSingularValue_adjoint]

/-- Ky Fan gauges converge under strong orthogonal cutoffs. -/
theorem kyFanApproximationGauge_comp_strongProjection_tendsto
    {ι : Type w} {P : ι → E →L[𝕜] E} {l : Filter ι}
    (hPproj : ∀ i, IsOrthogonalProjectionMap (P i))
    (hP : StronglyTendsto P l (ContinuousLinearMap.id 𝕜 E))
    (k : ℕ) (K : E →L[𝕜] F) :
    Tendsto
      (fun i => kyFanApproximationGauge k (K ∘L P i))
      l (𝓝 (kyFanApproximationGauge k K)) := by
  unfold kyFanApproximationGauge
  exact tendsto_finset_sum _ fun n hn =>
    approximationSingularValue_comp_strongProjection_tendsto hPproj hP n K

/-- A rectangular ideal family fully symmetric under finite Ky Fan dominance. -/
structure KyFanDominantIdealFamily (𝕜 : Type u) [RCLike 𝕜] where
  toRectangularSymmetricIdealFamily :
    RectangularSymmetricIdealFamily (𝕜 := 𝕜)
  majorization_mem_and_gauge_le :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      {A B : E →L[𝕜] F},
      toRectangularSymmetricIdealFamily.Mem B →
      (∀ k, kyFanApproximationGauge k A ≤
        kyFanApproximationGauge k B) →
      toRectangularSymmetricIdealFamily.Mem A ∧
        toRectangularSymmetricIdealFamily.gauge A ≤
          toRectangularSymmetricIdealFamily.gauge B

abbrev UnitaryInvariantIdealFamily
    (𝕜 : Type u) [RCLike 𝕜] :=
  KyFanDominantIdealFamily (𝕜 := 𝕜)

namespace KyFanDominantIdealFamily

/-- Operator norm; the `k=1` Fan inequality is exactly norm dominance. -/
noncomputable def operatorNorm :
    KyFanDominantIdealFamily (𝕜 := 𝕜) where
  toRectangularSymmetricIdealFamily :=
    RectangularSymmetricIdealFamily.operatorNorm
  majorization_mem_and_gauge_le := by
    intro E F _ _ _ _ A B hB h
    refine ⟨trivial, ?_⟩
    have h1 := h 1
    simpa [kyFanApproximationGauge, approximationSingularValue_zero] using h1

/-- Compact operators with operator norm.  Fan dominance transfers convergence
of approximation numbers to zero. -/
noncomputable def compactOperatorNorm :
    KyFanDominantIdealFamily (𝕜 := 𝕜) where
  toRectangularSymmetricIdealFamily :=
    RectangularSymmetricIdealFamily.compactOperatorNorm
  majorization_mem_and_gauge_le := by
    intro E F _ _ _ _ A B hB h
    have hpoint : ∀ n, approximationSingularValue n A ≤
        approximationSingularValue n B := by
      intro n
      have hs := h (n+1)
      have hs0 := h n
      simpa [kyFanApproximationGauge, Finset.sum_range_succ] using sub_le_sub hs hs0
    have htozeroB : Tendsto (fun n => approximationSingularValue n B) atTop (𝓝 0) :=
      approximationSingularValue_tendsto_zero_iff_compact.mpr hB
    have htozeroA : Tendsto (fun n => approximationSingularValue n A) atTop (𝓝 0) :=
      squeeze_zero' (fun n => approximationSingularValue_nonneg n A) hpoint htozeroB
    have hA : IsCompactOperator A :=
      approximationSingularValue_tendsto_zero_iff_compact.mp htozeroA
    refine ⟨hA, ?_⟩
    have h1 := h 1
    simpa [kyFanApproximationGauge, approximationSingularValue_zero] using h1

/-- Fixed positive Ky Fan gauge. -/
noncomputable def kyFan (k : ℕ) (hk : 0 < k) :
    KyFanDominantIdealFamily (𝕜 := 𝕜) where
  toRectangularSymmetricIdealFamily :=
    RectangularSymmetricIdealFamily.kyFan k hk
  majorization_mem_and_gauge_le := by
    intro E F _ _ _ _ A B hB h
    exact ⟨trivial, h k⟩

/-- Hilbert--Schmidt norm, obtained from weak majorization and the `ℓ²` gauge. -/
noncomputable def hilbertSchmidt :
    KyFanDominantIdealFamily (𝕜 := 𝕜) where
  toRectangularSymmetricIdealFamily :=
    RectangularSymmetricIdealFamily.hilbertSchmidt
  majorization_mem_and_gauge_le := by
    intro E F _ _ _ _ A B hB h
    exact hilbertSchmidt_mem_and_norm_le_of_kyFan_dominance hB h

/-- Trace norm, the maximal fully symmetric sequence gauge. -/
noncomputable def traceClass :
    KyFanDominantIdealFamily (𝕜 := 𝕜) where
  toRectangularSymmetricIdealFamily :=
    RectangularSymmetricIdealFamily.traceClass
  majorization_mem_and_gauge_le := by
    intro E F _ _ _ _ A B hB h
    exact traceClass_mem_and_norm_le_of_kyFan_dominance hB h

/-- Schatten `p` norm for `1 ≤ p`. -/
noncomputable def schatten (p : ℝ) (hp : 1 ≤ p) :
    KyFanDominantIdealFamily (𝕜 := 𝕜) where
  toRectangularSymmetricIdealFamily :=
    RectangularSymmetricIdealFamily.schatten p hp
  majorization_mem_and_gauge_le := by
    intro E F _ _ _ _ A B hB h
    exact schatten_mem_and_norm_le_of_kyFan_dominance hp hB h

end KyFanDominantIdealFamily

/-- Infinite-dimensional Fan dominance. -/
theorem mem_and_gauge_le_of_all_kyFanApproximationGauge_le
    (N : KyFanDominantIdealFamily (𝕜 := 𝕜))
    {A B : E →L[𝕜] F}
    (hB : N.toRectangularSymmetricIdealFamily.Mem B)
    (h : ∀ k, kyFanApproximationGauge k A ≤
      kyFanApproximationGauge k B) :
    N.toRectangularSymmetricIdealFamily.Mem A ∧
      N.toRectangularSymmetricIdealFamily.gauge A ≤
        N.toRectangularSymmetricIdealFamily.gauge B :=
  N.majorization_mem_and_gauge_le hB h

/-- Scaled Fan dominance in the form used by the Sylvester theorem. -/
theorem mem_and_scaled_gauge_le_of_all_scaled_kyFan_le
    (N : KyFanDominantIdealFamily (𝕜 := 𝕜))
    {A B : E →L[𝕜] F} {δ : ℝ}
    (hδ : 0 < δ)
    (hB : N.toRectangularSymmetricIdealFamily.Mem B)
    (h : ∀ k, δ * kyFanApproximationGauge k A ≤
      kyFanApproximationGauge k B) :
    N.toRectangularSymmetricIdealFamily.Mem A ∧
      δ * N.toRectangularSymmetricIdealFamily.gauge A ≤
        N.toRectangularSymmetricIdealFamily.gauge B := by
  let c : 𝕜 := (δ : 𝕜)
  have hcNorm : ‖c‖ = δ := by simp [c, abs_of_pos hδ]
  have hscaled : ∀ k, kyFanApproximationGauge k (c • A) ≤
      kyFanApproximationGauge k B := by
    intro k
    simpa [kyFanApproximationGauge_smul, hcNorm] using h k
  obtain ⟨hmemScaled, hgaugeScaled⟩ :=
    N.majorization_mem_and_gauge_le hB hscaled
  have hc : c ≠ 0 := by simpa [c] using ne_of_gt hδ
  have hmemA : N.toRectangularSymmetricIdealFamily.Mem A := by
    have := N.toRectangularSymmetricIdealFamily.smul_mem c⁻¹ hmemScaled
    simpa [inv_smul_smul₀ hc] using this
  refine ⟨hmemA, ?_⟩
  have hscaleGauge := N.toRectangularSymmetricIdealFamily.gauge_smul c hmemA
  rw [hcNorm] at hscaleGauge
  linarith

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib

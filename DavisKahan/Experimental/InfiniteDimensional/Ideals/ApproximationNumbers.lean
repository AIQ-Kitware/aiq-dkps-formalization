/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.Core.UnboundedSpectral
import DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.ApproximationNumberMinMax
import Mathlib.Topology.Algebra.Module.FiniteDimension
import ForMathlib.Analysis.Normed.Operator.ApproximationNumberHilbert
import ForMathlib.Analysis.InnerProductSpace.RectangularUnitarilyInvariantNorm

/-!
# Approximation numbers and strong spectral cutoffs

This module supplies the infinite-dimensional finite-Ky-Fan layer used by the
unbounded Davis--Kahan cutoff proof.  Approximation numbers are no longer an
opaque placeholder: they are the real coercions of the finite-rank infima in
`ForMathlib.Analysis.Normed.Operator.ApproximationNumber`.

The algebraic s-number laws, adjoint invariance, fixed-Ky-Fan norm construction,
completeness, and scaled Fan-dominance assembly are proved here.  The remaining
analytic seams are Ky Fan's addition inequality and convergence under strong
orthogonal cutoffs.
-/

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open scoped InnerProductSpace
open scoped Topology
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

/-- Zero-based approximation singular value, defined as the operator-norm
 distance to maps of rank at most `n`. -/
noncomputable def approximationSingularValue
    (n : ℕ) (K : E →L[𝕜] F) : ℝ :=
  K.approximationNumber n

/-- Approximation singular values are nonnegative. -/
theorem approximationSingularValue_nonneg
    (n : ℕ) (K : E →L[𝕜] F) :
    0 ≤ approximationSingularValue n K := by
  exact_mod_cast K.approximationNumber_nonneg n

/-- Approximation singular values of the zero map vanish. -/
@[simp]
theorem approximationSingularValue_zero_map (n : ℕ) :
    approximationSingularValue n (0 : E →L[𝕜] F) = 0 := by
  have h := congrArg (fun x : NNReal => (x : ℝ))
    (ContinuousLinearMap.zero_approximationNumber
      (𝕜 := 𝕜) (E := E) (F := F) n)
  simpa only [approximationSingularValue, NNReal.coe_zero] using h

/-- The zero-based first approximation singular value is the operator norm. -/
@[simp]
theorem approximationSingularValue_zero
    (K : E →L[𝕜] F) :
    approximationSingularValue 0 K = ‖K‖ := by
  have h := congrArg (fun x : NNReal => (x : ℝ))
    K.approximationNumber_zero
  simpa only [approximationSingularValue, coe_nnnorm] using h

/-- Approximation singular values are absolutely homogeneous. -/
theorem approximationSingularValue_smul
    (n : ℕ) (c : 𝕜) (K : E →L[𝕜] F) :
    approximationSingularValue n (c • K) =
      ‖c‖ * approximationSingularValue n K := by
  have h := congrArg (fun x : NNReal => (x : ℝ))
    (ContinuousLinearMap.approximationNumber_smul c K n)
  simpa only [approximationSingularValue, NNReal.coe_mul, coe_nnnorm] using h

/-- Approximation singular values decrease with the index. -/
theorem approximationSingularValue_antitone
    (K : E →L[𝕜] F) :
    Antitone (fun n => approximationSingularValue n K) := by
  intro n m hnm
  exact_mod_cast K.antitone_approximationNumber hnm

/-- Every approximation singular value is controlled by operator norm. -/
theorem approximationSingularValue_le_opNorm
    (n : ℕ) (K : E →L[𝕜] F) :
    approximationSingularValue n K ≤ ‖K‖ := by
  exact_mod_cast K.approximationNumber_le_nnnorm n

/-- Perturbation inequality at a fixed approximation index. -/
theorem approximationSingularValue_add_le
    (n : ℕ) (K L : E →L[𝕜] F) :
    approximationSingularValue n (K + L) ≤
      approximationSingularValue n K + ‖L‖ := by
  exact_mod_cast K.approximationNumber_add_le L n

/-- Adjoint invariance of approximation singular values on Hilbert spaces. -/
theorem approximationSingularValue_adjoint
    (n : ℕ) (K : E →L[𝕜] F) :
    approximationSingularValue n K.adjoint =
      approximationSingularValue n K := by
  have h := congrArg (fun x : NNReal => (x : ℝ))
    (K.approximationNumber_adjoint n)
  simpa only [approximationSingularValue] using h

/-- Ideal inequality for approximation singular values. -/
theorem approximationSingularValue_comp_le
    {G H : Type v}
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (n : ℕ) (L : F →L[𝕜] G) (K : E →L[𝕜] F)
    (R : H →L[𝕜] E) :
    approximationSingularValue n (L ∘L K ∘L R)
      ≤ ‖L‖ * approximationSingularValue n K * ‖R‖ := by
  have h := ContinuousLinearMap.approximationNumber_comp_comp_le L K R n
  exact_mod_cast h

/-- On finite-dimensional Hilbert spaces, each singular value is bounded by
the corresponding approximation singular value. This is the real-valued
adapter for the lower Eckart--Young theorem. -/
theorem singularValues_le_approximationSingularValue
    {E₀ F₀ : Type v}
    [NormedAddCommGroup E₀] [InnerProductSpace 𝕜 E₀]
    [FiniteDimensional 𝕜 E₀]
    [NormedAddCommGroup F₀] [InnerProductSpace 𝕜 F₀]
    [FiniteDimensional 𝕜 F₀]
    (A : E₀ →ₗ[𝕜] F₀) (n : ℕ) :
    A.singularValues n ≤
      approximationSingularValue n A.toContinuousLinearMap := by
  have h := ContinuousLinearMap.singularValues_le_approximationNumber
    A.toContinuousLinearMap n
  exact_mod_cast h

/-- On finite-dimensional Hilbert spaces, approximation singular values are
exactly the ordinary singular values. -/
theorem approximationSingularValue_eq_singularValues
    {E₀ F₀ : Type v}
    [NormedAddCommGroup E₀] [InnerProductSpace 𝕜 E₀]
    [FiniteDimensional 𝕜 E₀]
    [NormedAddCommGroup F₀] [InnerProductSpace 𝕜 F₀]
    [FiniteDimensional 𝕜 F₀]
    (A : E₀ →ₗ[𝕜] F₀) (n : ℕ) :
    approximationSingularValue n A.toContinuousLinearMap =
      A.singularValues n := by
  have hNN : A.toContinuousLinearMap.approximationNumber n =
      (⟨A.singularValues n, A.singularValues_nonneg n⟩ : NNReal) := by
    simpa only [LinearMap.coe_toContinuousLinearMap] using
      (ContinuousLinearMap.approximationNumber_eq_singularValues
        A.toContinuousLinearMap n)
  change (A.toContinuousLinearMap.approximationNumber n : ℝ) =
    A.singularValues n
  exact congrArg (fun x : NNReal => x.1) hNN

/-- An orthogonal projection does not increase vector norms. -/
theorem IsOrthogonalProjectionMap.norm_apply_le
    {P : E →L[𝕜] E} (hP : IsOrthogonalProjectionMap P) (x : E) :
    ‖P x‖ ≤ ‖x‖ := by
  have hPP : P (P x) = P x := by
    have h := congrArg (fun T : E →L[𝕜] E => T x) hP.1
    simpa only [ContinuousLinearMap.comp_apply] using h
  have hPQ : P (x - P x) = 0 := by
    rw [map_sub, hPP, sub_self]
  have horth : ⟪P x, x - P x⟫_𝕜 = 0 := by
    calc
      ⟪P x, x - P x⟫_𝕜 = ⟪x, P (x - P x)⟫_𝕜 :=
        hP.2 x (x - P x)
      _ = 0 := by simp only [hPQ, inner_zero_right]
  have hpyth : ‖P x‖ ^ 2 + ‖x - P x‖ ^ 2 = ‖x‖ ^ 2 := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      (P x) (x - P x) horth
    rw [show P x + (x - P x) = x by abel] at h
    rw [sq, sq, sq]
    linarith
  nlinarith [sq_nonneg ‖x - P x‖, norm_nonneg (P x), norm_nonneg x]

/-- An orthogonal projection has operator norm at most one. -/
theorem IsOrthogonalProjectionMap.norm_le_one
    {P : E →L[𝕜] E} (hP : IsOrthogonalProjectionMap P) :
    ‖P‖ ≤ 1 := by
  apply P.opNorm_le_bound zero_le_one
  intro x
  simpa only [one_mul] using hP.norm_apply_le x

/-- On a finite-dimensional source, pointwise convergence of bounded linear
maps to zero upgrades to convergence in operator norm. -/
theorem tendsto_opNorm_zero_of_finiteDimensional
    {ι : Type w} {l : Filter ι}
    {V G : Type v}
    [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    [FiniteDimensional 𝕜 V]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    (T : ι → V →L[𝕜] G)
    (hT : ∀ x, Tendsto (fun i => T i x) l (𝓝 0)) :
    Tendsto (fun i => ‖T i‖) l (𝓝 0) := by
  let b := Module.Basis.ofVectorSpace 𝕜 V
  let e := b.equivFunL.toContinuousLinearMap
  let C : ι → ℝ := fun i =>
    ‖e‖ * ∑ j, ‖T i (b j)‖
  have hsum : Tendsto (fun i => ∑ j, ‖T i (b j)‖) l (𝓝 0) := by
    have hsum' := tendsto_finsetSum Finset.univ
      (fun j _ => (hT (b j)).norm)
    simpa only [norm_zero, Finset.sum_const_zero] using hsum'
  have hC : Tendsto C l (𝓝 0) := by
    simpa only [C, mul_zero] using tendsto_const_nhds.mul hsum
  have hbound : ∀ i, ‖T i‖ ≤ C i := by
    intro i
    apply (T i).opNorm_le_bound
    · exact mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    · intro x
      calc
        ‖T i x‖ = ‖T i (∑ j, b.repr x j • b j)‖ := by
          rw [b.sum_repr]
        _ = ‖∑ j, b.repr x j • T i (b j)‖ := by
          rw [map_sum]
          simp only [map_smul]
        _ ≤ ∑ j, ‖b.repr x j • T i (b j)‖ :=
          norm_sum_le _ _
        _ = ∑ j, ‖b.repr x j‖ * ‖T i (b j)‖ := by
          apply Finset.sum_congr rfl
          intro j hj
          exact norm_smul _ _
        _ ≤ ∑ j, (‖e‖ * ‖x‖) * ‖T i (b j)‖ := by
          apply Finset.sum_le_sum
          intro j hj
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          calc
            ‖b.repr x j‖ = ‖e x j‖ := by rfl
            _ ≤ ‖e x‖ := norm_le_pi_norm (e x) j
            _ ≤ ‖e‖ * ‖x‖ := e.le_opNorm x
        _ = (‖e‖ * ‖x‖) * ∑ j, ‖T i (b j)‖ := by
          rw [Finset.mul_sum]
        _ = C i * ‖x‖ := by
          dsimp only [C]
          ring
  exact squeeze_zero (fun i => norm_nonneg (T i)) hbound hC

section ComplexStrongCutoff

variable {E₀ F₀ : Type v}
  [NormedAddCommGroup E₀] [InnerProductSpace ℂ E₀] [CompleteSpace E₀]
  [NormedAddCommGroup F₀] [InnerProductSpace ℂ F₀] [CompleteSpace F₀]

/-- Complex-Hilbert-space cutoff convergence, obtained from the generalized
Courant--Fischer localization theorem and uniform convergence on each finite
witness subspace. -/
theorem approximationSingularValue_comp_strongProjection_tendsto_complex
    {ι : Type w} {P : ι → E₀ →L[ℂ] E₀} {l : Filter ι}
    (hPproj : ∀ i, IsOrthogonalProjectionMap (P i))
    (hP : StronglyTendsto P l (ContinuousLinearMap.id ℂ E₀))
    (n : ℕ) (K : E₀ →L[ℂ] F₀) :
    Tendsto
      (fun i => approximationSingularValue n (K ∘L P i))
      l (𝓝 (approximationSingularValue n K)) := by
  have hUpper : ∀ i,
      approximationSingularValue n (K ∘L P i) ≤
        approximationSingularValue n K := by
    intro i
    have hnormNN : ‖P i‖₊ ≤ (1 : NNReal) := by
      exact_mod_cast (hPproj i).norm_le_one
    have hNN : (K ∘L P i).approximationNumber n ≤
        K.approximationNumber n := by
      calc
        (K ∘L P i).approximationNumber n
            ≤ K.approximationNumber n * ‖P i‖₊ :=
          K.approximationNumber_comp_right_le (P i) n
        _ ≤ K.approximationNumber n * 1 :=
          mul_le_mul_of_nonneg_left hnormNN bot_le
        _ = K.approximationNumber n := by rw [mul_one]
    exact_mod_cast hNN
  have hLower : ∀ r : ℝ,
      r < approximationSingularValue n K →
      ∀ᶠ i in l, r < approximationSingularValue n (K ∘L P i) := by
    intro r hr
    by_cases hr0 : 0 ≤ r
    · obtain ⟨s, hrs, v, hv, hV⟩ :=
        SpectraBridge.exists_linearIndependent_lowerBound_of_lt_approximationNumber
          K n hr0 hr
      let c : ℝ := (r + s) / 2
      have hrc : r < c := by dsimp only [c]; linarith
      have hcs : c < s := by dsimp only [c]; linarith
      have hc0 : 0 ≤ c := hr0.trans hrc.le
      let V : Submodule ℂ E₀ := Submodule.span ℂ (Set.range v)
      let b : Module.Basis (Fin (n + 1)) ℂ V := Module.Basis.span hv
      letI : FiniteDimensional ℂ V := b.finiteDimensional_of_finite
      let D : ι → V →L[ℂ] F₀ := fun i =>
        (K ∘L P i ∘L V.subtypeL) - (K ∘L V.subtypeL)
      have hDpoint : ∀ x : V, Tendsto (fun i => D i x) l (𝓝 0) := by
        intro x
        have hKP : Tendsto (fun i => K (P i (V.subtypeL x))) l
            (𝓝 (K (V.subtypeL x))) :=
          (K.continuous.tendsto (V.subtypeL x)).comp (hP (V.subtypeL x))
        have hconst : Tendsto (fun _ : ι => K (V.subtypeL x)) l
            (𝓝 (K (V.subtypeL x))) := tendsto_const_nhds
        change Tendsto
          (fun i => K (P i (V.subtypeL x)) - K (V.subtypeL x))
          l (𝓝 0)
        simpa only [sub_self] using hKP.sub hconst
      have hDnorm : Tendsto (fun i => ‖D i‖) l (𝓝 0) :=
        tendsto_opNorm_zero_of_finiteDimensional D hDpoint
      have hsmall : ∀ᶠ i in l, ‖D i‖ < s - c :=
        hDnorm.eventually (Iio_mem_nhds (sub_pos.mpr hcs))
      filter_upwards [hsmall] with i hi
      have hcNN : (⟨c, hc0⟩ : NNReal) ≤
          (K ∘L P i).approximationNumber n := by
        apply ContinuousLinearMap.lowerBound_le_approximationNumber_of_linearIndependent
          (K ∘L P i) n v hv
        intro x hxV hxNorm
        have hDx : ‖D i ⟨x, hxV⟩‖ ≤ ‖D i‖ := by
          have h := (D i).le_opNorm ⟨x, hxV⟩
          change ‖D i ⟨x, hxV⟩‖ ≤ ‖D i‖ * ‖x‖ at h
          rw [hxNorm, mul_one] at h
          exact h
        have hDapply : D i ⟨x, hxV⟩ = K (P i x) - K x := by
          rfl
        have htri : ‖K x‖ ≤ ‖K (P i x)‖ + ‖D i ⟨x, hxV⟩‖ := by
          rw [hDapply]
          have h := norm_sub_le (K (P i x)) (K (P i x) - K x)
          convert h using 1 <;> abel
        have hsx : s ≤ ‖K x‖ := by
          have := hV x hxV
          simpa only [hxNorm, mul_one] using this
        apply NNReal.coe_le_coe.mpr
        change c ≤ ‖K (P i x)‖
        linarith
      have hcReal : c ≤ approximationSingularValue n (K ∘L P i) := by
        exact_mod_cast hcNN
      exact hrc.trans_le hcReal
    · have hrneg : r < 0 := lt_of_not_ge hr0
      filter_upwards [] with i
      exact hrneg.trans_le
        (approximationSingularValue_nonneg n (K ∘L P i))
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hlower := hLower
    (approximationSingularValue n K - ε) (by linarith)
  filter_upwards [hlower] with i hi
  rw [Real.dist_eq, abs_lt]
  constructor
  · linarith
  · have := hUpper i
    linarith

end ComplexStrongCutoff

/-- Continuity of each approximation number under strongly convergent
orthogonal cutoffs. -/
theorem approximationSingularValue_comp_strongProjection_tendsto
    {ι : Type w} {P : ι → E →L[𝕜] E} {l : Filter ι}
    (hPproj : ∀ i, IsOrthogonalProjectionMap (P i))
    (hP : StronglyTendsto P l (ContinuousLinearMap.id 𝕜 E))
    (n : ℕ) (K : E →L[𝕜] F) :
    Tendsto
      (fun i => approximationSingularValue n (K ∘L P i))
      l (𝓝 (approximationSingularValue n K)) := by
  sorry

/-- Finite Ky Fan gauge built from approximation singular values. -/
noncomputable def kyFanApproximationGauge
    (k : ℕ) (K : E →L[𝕜] F) : ℝ :=
  ∑ n ∈ Finset.range k, approximationSingularValue n K


section ComplexKyFanStrongCutoff

variable {E₀ F₀ : Type v}
  [NormedAddCommGroup E₀] [InnerProductSpace ℂ E₀] [CompleteSpace E₀]
  [NormedAddCommGroup F₀] [InnerProductSpace ℂ F₀] [CompleteSpace F₀]

/-- Finite Ky Fan approximation gauges converge under complex strong
orthogonal cutoffs. -/
theorem kyFanApproximationGauge_comp_strongProjection_tendsto_complex
    {ι : Type w} {P : ι → E₀ →L[ℂ] E₀} {l : Filter ι}
    (hPproj : ∀ i, IsOrthogonalProjectionMap (P i))
    (hP : StronglyTendsto P l (ContinuousLinearMap.id ℂ E₀))
    (k : ℕ) (K : E₀ →L[ℂ] F₀) :
    Tendsto
      (fun i => kyFanApproximationGauge k (K ∘L P i))
      l (𝓝 (kyFanApproximationGauge k K)) := by
  simp only [kyFanApproximationGauge]
  exact tendsto_finsetSum (Finset.range k)
    (fun n hn => approximationSingularValue_comp_strongProjection_tendsto_complex
      hPproj hP n K)

end ComplexKyFanStrongCutoff

/-- Every finite-dimensional rectangular Ky Fan singular-value prefix is
bounded by the corresponding approximation-number prefix. -/
theorem rectangularKyFanSum_le_kyFanApproximationGauge
    {E₀ F₀ : Type v}
    [NormedAddCommGroup E₀] [InnerProductSpace 𝕜 E₀]
    [FiniteDimensional 𝕜 E₀]
    [NormedAddCommGroup F₀] [InnerProductSpace 𝕜 F₀]
    [FiniteDimensional 𝕜 F₀]
    (k : ℕ) (A : E₀ →ₗ[𝕜] F₀) :
    ForMathlib.DavisKahanTheory.RectangularUnitarilyInvariantNorm.rectangularKyFanSum k A ≤
      kyFanApproximationGauge k A.toContinuousLinearMap := by
  unfold ForMathlib.DavisKahanTheory.RectangularUnitarilyInvariantNorm.rectangularKyFanSum
    kyFanApproximationGauge
  rw [Fin.sum_univ_eq_sum_range]
  exact Finset.sum_le_sum fun n _ =>
    singularValues_le_approximationSingularValue A n

/-- Finite-dimensional Ky Fan prefixes agree exactly with the corresponding
approximation-number prefixes. -/
theorem rectangularKyFanSum_eq_kyFanApproximationGauge
    {E₀ F₀ : Type v}
    [NormedAddCommGroup E₀] [InnerProductSpace 𝕜 E₀]
    [FiniteDimensional 𝕜 E₀]
    [NormedAddCommGroup F₀] [InnerProductSpace 𝕜 F₀]
    [FiniteDimensional 𝕜 F₀]
    (k : ℕ) (A : E₀ →ₗ[𝕜] F₀) :
    ForMathlib.DavisKahanTheory.RectangularUnitarilyInvariantNorm.rectangularKyFanSum k A =
      kyFanApproximationGauge k A.toContinuousLinearMap := by
  unfold ForMathlib.DavisKahanTheory.RectangularUnitarilyInvariantNorm.rectangularKyFanSum
    kyFanApproximationGauge
  rw [Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun n _ =>
    (approximationSingularValue_eq_singularValues A n).symm

/-- The approximation-number Ky Fan triangle inequality on finite-dimensional
Hilbert spaces, obtained by transporting the established rectangular theorem. -/
theorem kyFanApproximationGauge_add_le_finiteDimensional
    {E₀ F₀ : Type v}
    [NormedAddCommGroup E₀] [InnerProductSpace 𝕜 E₀]
    [FiniteDimensional 𝕜 E₀]
    [NormedAddCommGroup F₀] [InnerProductSpace 𝕜 F₀]
    [FiniteDimensional 𝕜 F₀]
    (k : ℕ) (A B : E₀ →ₗ[𝕜] F₀) :
    kyFanApproximationGauge k (A + B).toContinuousLinearMap ≤
      kyFanApproximationGauge k A.toContinuousLinearMap +
        kyFanApproximationGauge k B.toContinuousLinearMap := by
  rw [← rectangularKyFanSum_eq_kyFanApproximationGauge k (A + B),
    ← rectangularKyFanSum_eq_kyFanApproximationGauge k A,
    ← rectangularKyFanSum_eq_kyFanApproximationGauge k B]
  exact (ForMathlib.DavisKahanTheory.RectangularUnitarilyInvariantNorm.kyFan
    (𝕜 := 𝕜) (E := E₀) (F := F₀) k).add_le A B

/-- The zero-term Ky Fan gauge vanishes. -/
@[simp]
theorem kyFanApproximationGauge_zero :
    kyFanApproximationGauge 0 (0 : E →L[𝕜] F) = 0 := by
  simp [kyFanApproximationGauge]

/-- Every finite Ky Fan gauge vanishes on the zero operator. -/
@[simp]
theorem kyFanApproximationGauge_zero_map (k : ℕ) :
    kyFanApproximationGauge k (0 : E →L[𝕜] F) = 0 := by
  simp [kyFanApproximationGauge]

/-- The first positive Ky Fan gauge is operator norm. -/
@[simp]
theorem kyFanApproximationGauge_one (K : E →L[𝕜] F) :
    kyFanApproximationGauge 1 K = ‖K‖ := by
  simp [kyFanApproximationGauge]

/-- Ky Fan approximation gauges are absolutely homogeneous. -/
theorem kyFanApproximationGauge_smul
    (k : ℕ) (c : 𝕜) (K : E →L[𝕜] F) :
    kyFanApproximationGauge k (c • K) =
      ‖c‖ * kyFanApproximationGauge k K := by
  simp only [kyFanApproximationGauge, approximationSingularValue_smul]
  rw [Finset.mul_sum]

/-- Ky Fan approximation gauges are nonnegative. -/
theorem kyFanApproximationGauge_nonneg
    (k : ℕ) (K : E →L[𝕜] F) :
    0 ≤ kyFanApproximationGauge k K := by
  exact Finset.sum_nonneg fun n hn => approximationSingularValue_nonneg n K

/-- Ky Fan's addition inequality for approximation numbers. -/
theorem kyFanApproximationGauge_add_le
    (k : ℕ) (K L : E →L[𝕜] F) :
    kyFanApproximationGauge k (K + L) ≤
      kyFanApproximationGauge k K + kyFanApproximationGauge k L := by
  sorry

/-- Ky Fan approximation gauges are invariant under adjoint. -/
theorem kyFanApproximationGauge_adjoint
    (k : ℕ) (K : E →L[𝕜] F) :
    kyFanApproximationGauge k K.adjoint =
      kyFanApproximationGauge k K := by
  simp only [kyFanApproximationGauge, approximationSingularValue_adjoint]

/-- Two-sided ideal inequality for finite Ky Fan gauges. -/
theorem kyFanApproximationGauge_comp_le
    {G H : Type v}
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (k : ℕ) (L : F →L[𝕜] G) (K : E →L[𝕜] F)
    (R : H →L[𝕜] E) :
    kyFanApproximationGauge k (L ∘L K ∘L R) ≤
      ‖L‖ * kyFanApproximationGauge k K * ‖R‖ := by
  calc
    kyFanApproximationGauge k (L ∘L K ∘L R)
        ≤ ∑ n ∈ Finset.range k,
          (‖L‖ * approximationSingularValue n K * ‖R‖) := by
      apply Finset.sum_le_sum
      intro n hn
      exact approximationSingularValue_comp_le n L K R
    _ = ‖L‖ * kyFanApproximationGauge k K * ‖R‖ := by
      simp only [kyFanApproximationGauge, Finset.mul_sum, Finset.sum_mul]

/-- The operator norm is the first term of every positive finite Ky Fan gauge. -/
theorem opNorm_le_kyFanApproximationGauge
    {k : ℕ} (hk : 0 < k) (K : E →L[𝕜] F) :
    ‖K‖ ≤ kyFanApproximationGauge k K := by
  rw [← approximationSingularValue_zero K]
  exact Finset.single_le_sum
    (fun n hn => approximationSingularValue_nonneg n K)
    (Finset.mem_range.mpr hk)

/-- A finite Ky Fan gauge is bounded by `k` times operator norm. -/
theorem kyFanApproximationGauge_le_nat_mul_opNorm
    (k : ℕ) (K : E →L[𝕜] F) :
    kyFanApproximationGauge k K ≤ (k : ℝ) * ‖K‖ := by
  calc
    kyFanApproximationGauge k K
        ≤ ∑ n ∈ Finset.range k, ‖K‖ := by
      apply Finset.sum_le_sum
      intro n hn
      exact approximationSingularValue_le_opNorm n K
    _ = (k : ℝ) * ‖K‖ := by simp

/-- Ky Fan gauges converge under strong orthogonal cutoffs. -/
theorem kyFanApproximationGauge_comp_strongProjection_tendsto
    {ι : Type w} {P : ι → E →L[𝕜] E} {l : Filter ι}
    (hPproj : ∀ i, IsOrthogonalProjectionMap (P i))
    (hP : StronglyTendsto P l (ContinuousLinearMap.id 𝕜 E))
    (k : ℕ) (K : E →L[𝕜] F) :
    Tendsto
      (fun i => kyFanApproximationGauge k (K ∘L P i))
      l (𝓝 (kyFanApproximationGauge k K)) := by
  simp only [kyFanApproximationGauge]
  exact tendsto_finsetSum (Finset.range k)
    (fun n hn => approximationSingularValue_comp_strongProjection_tendsto
      hPproj hP n K)

/-- A rectangular ideal family whose gauge is fully symmetric with respect
    to all finite Ky Fan approximation gauges. -/
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

/-- Source-facing name for the infinite-dimensional unitarily invariant norm
families supported by the Davis--Kahan cutoff proof. -/
abbrev UnitaryInvariantIdealFamily
    (𝕜 : Type u) [RCLike 𝕜] :=
  KyFanDominantIdealFamily (𝕜 := 𝕜)

namespace KyFanDominantIdealFamily

/-- The ordinary operator norm with its finite-Ky-Fan dominance property. -/
noncomputable def operatorNorm :
    KyFanDominantIdealFamily (𝕜 := 𝕜) where
  toRectangularSymmetricIdealFamily :=
    RectangularSymmetricIdealFamily.operatorNorm
  majorization_mem_and_gauge_le := by
    intro E F _ _ _ _ _ _ A B hB hmajor
    refine ⟨trivial, ?_⟩
    change ‖A‖ ≤ ‖B‖
    simpa using hmajor 1

/-- Completeness of a fixed positive finite Ky Fan gauge. -/
theorem kyFan_gauge_complete (k : ℕ) (hk : 0 < k)
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (A : ℕ → E →L[𝕜] F)
    (hCauchy : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ m n, N ≤ m → N ≤ n →
      kyFanApproximationGauge k (A m - A n) < ε) :
    ∃ L : E →L[𝕜] F, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n, N ≤ n →
      kyFanApproximationGauge k (A n - L) < ε := by
  have hopCauchy : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ m n, N ≤ m → N ≤ n →
      ‖A m - A n‖ < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hCauchy ε hε
    refine ⟨N, ?_⟩
    intro m n hm hn
    exact lt_of_le_of_lt
      (opNorm_le_kyFanApproximationGauge hk (A m - A n))
      (hN m n hm hn)
  obtain ⟨L, hLmem, hL⟩ :=
    RectangularSymmetricIdealFamily.operatorNorm.gauge_complete
      A (fun n => trivial) hopCauchy
  refine ⟨L, ?_⟩
  intro ε hε
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  obtain ⟨N, hN⟩ := hL (ε / (k : ℝ)) (div_pos hε hkR)
  refine ⟨N, ?_⟩
  intro n hn
  calc
    kyFanApproximationGauge k (A n - L)
        ≤ (k : ℝ) * ‖A n - L‖ :=
      kyFanApproximationGauge_le_nat_mul_opNorm k (A n - L)
    _ < (k : ℝ) * (ε / (k : ℝ)) :=
      mul_lt_mul_of_pos_left (hN n hn) hkR
    _ = ε := by field_simp

/-- A fixed positive finite Ky Fan gauge with its own dominance property. -/
noncomputable def kyFan (k : ℕ) (hk : 0 < k) :
    KyFanDominantIdealFamily (𝕜 := 𝕜) where
  toRectangularSymmetricIdealFamily := {
    Mem := fun _ => True
    gauge := kyFanApproximationGauge k
    zero_mem := trivial
    add_mem := by intros; trivial
    smul_mem := by intros; trivial
    adjoint_mem := by intros; trivial
    comp_mem := by intros; trivial
    gauge_nonneg := by
      intro E F _ _ _ _ _ _ A hA
      exact kyFanApproximationGauge_nonneg k A
    gauge_zero := by
      intro E F _ _ _ _ _ _
      exact kyFanApproximationGauge_zero_map k
    gauge_eq_zero := by
      intro E F _ _ _ _ _ _ A hA hzero
      apply norm_eq_zero.mp
      exact le_antisymm
        ((opNorm_le_kyFanApproximationGauge hk A).trans_eq hzero)
        (norm_nonneg A)
    gauge_add_le := by
      intro E F _ _ _ _ _ _ A B hA hB
      exact kyFanApproximationGauge_add_le k A B
    gauge_smul := by
      intro E F _ _ _ _ _ _ c A hA
      exact kyFanApproximationGauge_smul k c A
    gauge_adjoint := by
      intro E F _ _ _ _ _ _ A hA
      exact kyFanApproximationGauge_adjoint k A
    gauge_comp_le := by
      intro E F G H _ _ _ _ _ _ _ _ _ _ _ _ L A R hA
      exact kyFanApproximationGauge_comp_le k L A R
    opNorm_le_gauge := by
      intro E F _ _ _ _ _ _ A hA
      exact opNorm_le_kyFanApproximationGauge hk A
    gauge_complete := by
      intro E F _ _ _ _ _ _ A hmem hCauchy
      obtain ⟨L, hL⟩ := kyFan_gauge_complete k hk A hCauchy
      exact ⟨L, trivial, hL⟩
  }
  majorization_mem_and_gauge_le := by
    intro E F _ _ _ _ _ _ A B hB hmajor
    exact ⟨trivial, hmajor k⟩

/-- Every bounded operator belongs to the fixed finite Ky Fan family. -/
@[simp]
theorem kyFan_mem (k : ℕ) (hk : 0 < k) (K : E →L[𝕜] F) :
    (kyFan (𝕜 := 𝕜) k hk).toRectangularSymmetricIdealFamily.Mem K :=
  trivial

/-- The concrete gauge of the fixed finite Ky Fan family. -/
@[simp]
theorem kyFan_gauge (k : ℕ) (hk : 0 < k) (K : E →L[𝕜] F) :
    (kyFan (𝕜 := 𝕜) k hk).toRectangularSymmetricIdealFamily.gauge K =
      kyFanApproximationGauge k K :=
  rfl

end KyFanDominantIdealFamily

/-- Infinite-dimensional Fan dominance, exposed from the stronger family. -/
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

/-- Scaled Fan dominance in the exact form consumed by the Sylvester theorem. -/
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
  let d : 𝕜 := (δ : 𝕜)
  have hd : d ≠ 0 := RCLike.ofReal_ne_zero.mpr hδ.ne'
  have hdnorm : ‖d‖ = δ := by
    simp [d, abs_of_pos hδ]
  have hscaled : ∀ k,
      kyFanApproximationGauge k (d • A) ≤
        kyFanApproximationGauge k B := by
    intro k
    rw [kyFanApproximationGauge_smul, hdnorm]
    exact h k
  obtain ⟨hdA, hgauge⟩ := N.majorization_mem_and_gauge_le hB hscaled
  have hA : N.toRectangularSymmetricIdealFamily.Mem A := by
    have hinv := N.toRectangularSymmetricIdealFamily.smul_mem d⁻¹ hdA
    rw [← mul_smul, inv_mul_cancel₀ hd, one_smul] at hinv
    exact hinv
  refine ⟨hA, ?_⟩
  have hhom := N.toRectangularSymmetricIdealFamily.gauge_smul d hA
  rw [hdnorm] at hhom
  linarith

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib

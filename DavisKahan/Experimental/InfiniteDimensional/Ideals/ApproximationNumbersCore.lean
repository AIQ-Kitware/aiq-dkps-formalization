/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.Core.UnboundedSpectral
import DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.ApproximationNumberMinMax
import Mathlib.Topology.Algebra.Module.FiniteDimension
import ForMathlib.Analysis.Normed.Operator.ApproximationNumberAdjoint
import ForMathlib.Analysis.Normed.Operator.ApproximationNumberSingularValues
import ForMathlib.Analysis.Normed.Operator.ApproximationNumberMinMax
import ForMathlib.Analysis.InnerProductSpace.RectangularUnitarilyInvariantNorm

/-!
# Approximation-number foundation and scalar-specific analytic endpoints

This lower module contains the approximation-number definitions, scalar-generic
algebraic laws, finite-dimensional Ky Fan bridge, and the accepted complex
strong-cutoff and infinite-dimensional Ky Fan arguments. It intentionally does
not import the real localization module, so the real proof can depend on this
foundation without creating an import cycle.

The public aggregate and downstream ideal-family construction remain in
`ApproximationNumbers`.
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


section ComplexKyFanTriangle

variable {E₀ F₀ : Type v}
  [NormedAddCommGroup E₀] [InnerProductSpace ℂ E₀] [CompleteSpace E₀]
  [NormedAddCommGroup F₀] [InnerProductSpace ℂ F₀] [CompleteSpace F₀]

/-- Restricting a complex operator to a larger source subspace can only
increase its approximation numbers. -/
theorem approximationSingularValue_restrict_mono_complex
    (T : E₀ →L[ℂ] F₀) (n : ℕ) {U V : Submodule ℂ E₀}
    (hUV : U ≤ V) :
    approximationSingularValue n (T ∘L U.subtypeL) ≤
      approximationSingularValue n (T ∘L V.subtypeL) := by
  let J : U →L[ℂ] V :=
    (Submodule.inclusion hUV).mkContinuous 1 (fun x => by
      change ‖((x : U) : E₀)‖ ≤ 1 * ‖x‖
      simp)
  have hJnorm : ‖J‖₊ ≤ (1 : NNReal) := by
    exact_mod_cast (J.opNorm_le_bound zero_le_one fun x => by
      change ‖((x : U) : E₀)‖ ≤ 1 * ‖x‖
      simp)
  have hcomp : T ∘L U.subtypeL = (T ∘L V.subtypeL) ∘L J := by
    ext x
    rfl
  have hNN : (T ∘L U.subtypeL).approximationNumber n ≤
      (T ∘L V.subtypeL).approximationNumber n := by
    rw [hcomp]
    calc
      ((T ∘L V.subtypeL) ∘L J).approximationNumber n
          ≤ (T ∘L V.subtypeL).approximationNumber n * ‖J‖₊ :=
        (T ∘L V.subtypeL).approximationNumber_comp_right_le J n
      _ ≤ (T ∘L V.subtypeL).approximationNumber n * 1 :=
        mul_le_mul_of_nonneg_left hJnorm bot_le
      _ = (T ∘L V.subtypeL).approximationNumber n := by rw [mul_one]
  change ((T ∘L U.subtypeL).approximationNumber n : ℝ) ≤
    ((T ∘L V.subtypeL).approximationNumber n : ℝ)
  exact_mod_cast hNN

/-- Projecting the codomain onto a subspace already containing the operator
range preserves every approximation singular value. -/
theorem approximationSingularValue_orthogonalProjectionOnto_comp_eq
    {V G : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (W : Submodule ℂ G) [W.HasOrthogonalProjection]
    (A : V →L[ℂ] G) (hA : ∀ x, A x ∈ W) (n : ℕ) :
    approximationSingularValue n (W.orthogonalProjectionOnto ∘L A) =
      approximationSingularValue n A := by
  let AW : V →L[ℂ] W := W.orthogonalProjectionOnto ∘L A
  have hfactor : W.subtypeL ∘L AW = A := by
    ext x
    change W.starProjection (A x) = A x
    exact W.starProjection_eq_self_iff.mpr (hA x)
  have hproj : ‖W.orthogonalProjectionOnto‖₊ ≤ (1 : NNReal) := by
    exact_mod_cast W.orthogonalProjectionOnto_norm_le
  have hsub : ‖W.subtypeL‖₊ ≤ (1 : NNReal) := by
    exact_mod_cast W.norm_subtypeL_le
  have hNN : AW.approximationNumber n = A.approximationNumber n := by
    apply le_antisymm
    · calc
        AW.approximationNumber n
            ≤ ‖W.orthogonalProjectionOnto‖₊ * A.approximationNumber n :=
          ContinuousLinearMap.approximationNumber_comp_left_le
            W.orthogonalProjectionOnto A n
        _ ≤ 1 * A.approximationNumber n :=
          mul_le_mul_of_nonneg_right hproj bot_le
        _ = A.approximationNumber n := by rw [one_mul]
    · rw [← hfactor]
      calc
        (W.subtypeL ∘L AW).approximationNumber n
            ≤ ‖W.subtypeL‖₊ * AW.approximationNumber n :=
          ContinuousLinearMap.approximationNumber_comp_left_le W.subtypeL AW n
        _ ≤ 1 * AW.approximationNumber n :=
          mul_le_mul_of_nonneg_right hsub bot_le
        _ = AW.approximationNumber n := by rw [one_mul]
  change (AW.approximationNumber n : ℝ) = (A.approximationNumber n : ℝ)
  exact congrArg (fun x : NNReal => (x : ℝ)) hNN

/-- Projecting the codomain onto a subspace containing the range preserves
all finite Ky Fan approximation gauges. -/
theorem kyFanApproximationGauge_orthogonalProjectionOnto_comp_eq
    {V G : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (W : Submodule ℂ G) [W.HasOrthogonalProjection]
    (A : V →L[ℂ] G) (hA : ∀ x, A x ∈ W) (k : ℕ) :
    kyFanApproximationGauge k (W.orthogonalProjectionOnto ∘L A) =
      kyFanApproximationGauge k A := by
  unfold kyFanApproximationGauge
  exact Finset.sum_congr rfl fun n _ =>
    approximationSingularValue_orthogonalProjectionOnto_comp_eq W A hA n

/-- The Ky Fan approximation-gauge triangle inequality when the source is
finite-dimensional and the complex Hilbert codomain is arbitrary. -/
theorem kyFanApproximationGauge_add_le_finiteSource_complex
    {V G : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (k : ℕ) (A B : V →L[ℂ] G) :
    kyFanApproximationGauge k (A + B) ≤
      kyFanApproximationGauge k A + kyFanApproximationGauge k B := by
  letI : CompleteSpace V := FiniteDimensional.complete ℂ V
  let C : V × V →L[ℂ] G :=
    A ∘L ContinuousLinearMap.fst ℂ V V +
      B ∘L ContinuousLinearMap.snd ℂ V V
  let W : Submodule ℂ G := C.range
  letI : FiniteDimensional ℂ W := by
    apply FiniteDimensional.of_surjective C.rangeRestrict.toLinearMap
    intro y
    rcases y.property with ⟨x, hx⟩
    exact ⟨x, Subtype.ext hx⟩
  letI : CompleteSpace W := FiniteDimensional.complete ℂ W
  letI : W.HasOrthogonalProjection :=
    Submodule.HasOrthogonalProjection.ofCompleteSpace W
  have hA : ∀ x, A x ∈ W := by
    intro x
    change A x ∈ C.range
    refine ⟨(x, 0), ?_⟩
    simp [C]
  have hB : ∀ x, B x ∈ W := by
    intro x
    change B x ∈ C.range
    refine ⟨(0, x), ?_⟩
    simp [C]
  have hAB : ∀ x, (A + B) x ∈ W := by
    intro x
    exact W.add_mem (hA x) (hB x)
  let AW : V →L[ℂ] W := W.orthogonalProjectionOnto ∘L A
  let BW : V →L[ℂ] W := W.orthogonalProjectionOnto ∘L B
  have hsum : W.orthogonalProjectionOnto ∘L (A + B) = AW + BW := by
    ext x
    simp [AW, BW]
  have hAWcont : AW.toLinearMap.toContinuousLinearMap = AW := by
    ext x
    rfl
  have hBWcont : BW.toLinearMap.toContinuousLinearMap = BW := by
    ext x
    rfl
  have hsumcont :
      (AW.toLinearMap + BW.toLinearMap).toContinuousLinearMap = AW + BW := by
    ext x
    rfl
  have htri := kyFanApproximationGauge_add_le_finiteDimensional
    (𝕜 := ℂ) k AW.toLinearMap BW.toLinearMap
  rw [hsumcont, hAWcont, hBWcont] at htri
  calc
    kyFanApproximationGauge k (A + B) =
        kyFanApproximationGauge k (W.orthogonalProjectionOnto ∘L (A + B)) :=
      (kyFanApproximationGauge_orthogonalProjectionOnto_comp_eq
        W (A + B) hAB k).symm
    _ = kyFanApproximationGauge k (AW + BW) := by rw [hsum]
    _ ≤ kyFanApproximationGauge k AW + kyFanApproximationGauge k BW := htri
    _ = kyFanApproximationGauge k A + kyFanApproximationGauge k B := by
      rw [kyFanApproximationGauge_orthogonalProjectionOnto_comp_eq W A hA k,
        kyFanApproximationGauge_orthogonalProjectionOnto_comp_eq W B hB k]

/-- Every positive tolerance admits a finite source restriction whose
approximation number is within that tolerance of the ambient complex value. -/
theorem exists_finiteRestrictionApproximationNumber_add_gt
    (T : E₀ →L[ℂ] F₀) (n : ℕ) (ε : NNReal) (hε : 0 < ε) :
    ∃ v : Fin (n + 1) → E₀,
      T.approximationNumber n <
        (T ∘L (Submodule.span ℂ (Set.range v)).subtypeL).approximationNumber n + ε := by
  by_cases hsmall : T.approximationNumber n < ε
  · refine ⟨fun _ => 0, hsmall.trans_le ?_⟩
    exact le_add_of_nonneg_left bot_le
  · have hεle : ε ≤ T.approximationNumber n := le_of_not_gt hsmall
    have ha0 : 0 < T.approximationNumber n := hε.trans_le hεle
    have hsub : T.approximationNumber n - ε < T.approximationNumber n :=
      tsub_lt_self ha0 hε
    obtain ⟨v, hv⟩ :=
      SpectraBridge.exists_finiteRestrictionApproximationNumber_gt_of_lt
        T n hsub
    refine ⟨v, ?_⟩
    calc
      T.approximationNumber n =
          (T.approximationNumber n - ε) + ε :=
        (tsub_add_cancel_of_le hεle).symm
      _ < (T ∘L (Submodule.span ℂ (Set.range v)).subtypeL).approximationNumber n + ε :=
        add_lt_add_left hv ε

/-- Infinite-dimensional Ky Fan addition inequality over complex Hilbert
spaces, obtained from simultaneous finite-dimensional localization. -/
theorem kyFanApproximationGauge_add_le_complex
    (k : ℕ) (K L : E₀ →L[ℂ] F₀) :
    kyFanApproximationGauge k (K + L) ≤
      kyFanApproximationGauge k K + kyFanApproximationGauge k L := by
  classical
  by_cases hk : k = 0
  · subst k
    simp [kyFanApproximationGauge]
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  apply le_of_forall_pos_le_add
  intro ε hε
  let δr : ℝ := ε / (k : ℝ)
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hkpos
  have hδr : 0 < δr := div_pos hε hkreal
  let δ : NNReal := ⟨δr, hδr.le⟩
  have hδ : 0 < δ := by
    change 0 < δr
    exact hδr
  choose v hv using fun n =>
    exists_finiteRestrictionApproximationNumber_add_gt (K + L) n δ hδ
  let β : Type := Σ n : Fin k, Fin (n.1 + 1)
  let w : β → E₀ := fun p => v p.1.1 p.2
  let V : Submodule ℂ E₀ := Submodule.span ℂ (Set.range w)
  letI : FiniteDimensional ℂ V :=
    Module.Finite.span_of_finite ℂ (Set.finite_range w)
  letI : CompleteSpace V := FiniteDimensional.complete ℂ V
  let KV : V →L[ℂ] F₀ := K ∘L V.subtypeL
  let LV : V →L[ℂ] F₀ := L ∘L V.subtypeL
  have hsumRestrict : (K + L) ∘L V.subtypeL = KV + LV := by
    ext x
    rfl
  have hterm : ∀ n ∈ Finset.range k,
      approximationSingularValue n (K + L) ≤
        approximationSingularValue n (KV + LV) + (δ : ℝ) := by
    intro n hn
    let U : Submodule ℂ E₀ := Submodule.span ℂ (Set.range (v n))
    have hUV : U ≤ V := by
      apply Submodule.span_le.mpr
      rintro x ⟨j, rfl⟩
      apply Submodule.subset_span
      exact ⟨(⟨⟨n, Finset.mem_range.mp hn⟩, j⟩ : β), rfl⟩
    have hmono := approximationSingularValue_restrict_mono_complex
      (K + L) n hUV
    have hvNN : (K + L).approximationNumber n <
        ((K + L) ∘L U.subtypeL).approximationNumber n + δ := by
      simpa only [U] using hv n
    have hvReal : approximationSingularValue n (K + L) <
        approximationSingularValue n ((K + L) ∘L U.subtypeL) + (δ : ℝ) := by
      change ((K + L).approximationNumber n : ℝ) <
        (((K + L) ∘L U.subtypeL).approximationNumber n : ℝ) + (δ : ℝ)
      exact_mod_cast hvNN
    calc
      approximationSingularValue n (K + L)
          ≤ approximationSingularValue n ((K + L) ∘L U.subtypeL) + (δ : ℝ) :=
        le_of_lt hvReal
      _ ≤ approximationSingularValue n ((K + L) ∘L V.subtypeL) + (δ : ℝ) :=
        add_le_add_left hmono (δ : ℝ)
      _ = approximationSingularValue n (KV + LV) + (δ : ℝ) := by
        rw [hsumRestrict]
  have hlocal : kyFanApproximationGauge k (K + L) ≤
      kyFanApproximationGauge k (KV + LV) + ε := by
    unfold kyFanApproximationGauge
    calc
      ∑ n ∈ Finset.range k, approximationSingularValue n (K + L)
          ≤ ∑ n ∈ Finset.range k,
              (approximationSingularValue n (KV + LV) + (δ : ℝ)) :=
        Finset.sum_le_sum hterm
      _ = (∑ n ∈ Finset.range k, approximationSingularValue n (KV + LV)) +
          (k : ℝ) * (δ : ℝ) := by
        rw [Finset.sum_add_distrib]
        simp [nsmul_eq_mul]
      _ = (∑ n ∈ Finset.range k, approximationSingularValue n (KV + LV)) + ε := by
        change _ + (k : ℝ) * δr = _ + ε
        rw [mul_div_cancel₀ ε hkreal.ne']
  have htri := kyFanApproximationGauge_add_le_finiteSource_complex k KV LV
  have hKrestrict : kyFanApproximationGauge k KV ≤ kyFanApproximationGauge k K := by
    unfold kyFanApproximationGauge
    apply Finset.sum_le_sum
    intro n hn
    change ((K ∘L V.subtypeL).approximationNumber n : ℝ) ≤
      (K.approximationNumber n : ℝ)
    exact_mod_cast SpectraBridge.approximationNumber_comp_subtypeL_le K n V
  have hLrestrict : kyFanApproximationGauge k LV ≤ kyFanApproximationGauge k L := by
    unfold kyFanApproximationGauge
    apply Finset.sum_le_sum
    intro n hn
    change ((L ∘L V.subtypeL).approximationNumber n : ℝ) ≤
      (L.approximationNumber n : ℝ)
    exact_mod_cast SpectraBridge.approximationNumber_comp_subtypeL_le L n V
  calc
    kyFanApproximationGauge k (K + L)
        ≤ kyFanApproximationGauge k (KV + LV) + ε := hlocal
    _ ≤ (kyFanApproximationGauge k KV + kyFanApproximationGauge k LV) + ε :=
      add_le_add_left htri ε
    _ ≤ (kyFanApproximationGauge k K + kyFanApproximationGauge k L) + ε :=
      add_le_add_left (add_le_add hKrestrict hLrestrict) ε

end ComplexKyFanTriangle

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

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib

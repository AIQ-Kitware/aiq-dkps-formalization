/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.Core.UnboundedSpectral
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
  exact tendsto_finset_sum (Finset.range k)
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
    simp [d, RCLike.norm_ofReal, abs_of_pos hδ]
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

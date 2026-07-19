/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.Ideals.ApproximationNumbersCore
import DavisKahan.Experimental.InfiniteDimensional.Ideals.ApproximationNumbersRealRoadmap

/-!
# Scalar-generic approximation-number endpoints and ideal families

This public module assembles the lower approximation-number foundation with
its complex and real analytic endpoints. The scalar-generic endpoint wrappers
and the downstream Ky Fan dominant ideal families live here, above both
scalar-specific implementations, avoiding the former real-proof import cycle.
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

/-- Analytic capability asserting strong-cutoff convergence for approximation
numbers over a scalar field.  This is separated from `RCLike`: the latter is
an open algebraic typeclass, while this property is currently established for
the standard real and complex scalar fields. -/
class HasApproximationNumberStrongCutoff
    (𝕜 : Type u) [RCLike 𝕜] : Prop where
  tendsto_comp_strongProjection :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      {ι : Type w} {P : ι → E →L[𝕜] E} {l : Filter ι},
      (∀ i, IsOrthogonalProjectionMap (P i)) →
      StronglyTendsto P l (ContinuousLinearMap.id 𝕜 E) →
      ∀ (n : ℕ) (K : E →L[𝕜] F),
        Tendsto
          (fun i => approximationSingularValue n (K ∘L P i))
          l (𝓝 (approximationSingularValue n K))

/-- Analytic capability asserting the finite Ky Fan triangle inequality over
a scalar field. -/
class HasKyFanApproximationGaugeTriangle
    (𝕜 : Type u) [RCLike 𝕜] : Prop where
  add_le :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      (k : ℕ) (K L : E →L[𝕜] F),
      kyFanApproximationGauge k (K + L) ≤
        kyFanApproximationGauge k K + kyFanApproximationGauge k L

instance realHasApproximationNumberStrongCutoff :
    HasApproximationNumberStrongCutoff ℝ where
  tendsto_comp_strongProjection :=
    approximationSingularValue_comp_strongProjection_tendsto_real

instance complexHasApproximationNumberStrongCutoff :
    HasApproximationNumberStrongCutoff ℂ where
  tendsto_comp_strongProjection :=
    approximationSingularValue_comp_strongProjection_tendsto_complex

instance realHasKyFanApproximationGaugeTriangle :
    HasKyFanApproximationGaugeTriangle ℝ where
  add_le := kyFanApproximationGauge_add_le_real

instance complexHasKyFanApproximationGaugeTriangle :
    HasKyFanApproximationGaugeTriangle ℂ where
  add_le := kyFanApproximationGauge_add_le_complex

/-- Continuity of each approximation number under strongly convergent
orthogonal cutoffs. -/
theorem approximationSingularValue_comp_strongProjection_tendsto
    [HasApproximationNumberStrongCutoff 𝕜]
    {ι : Type w} {P : ι → E →L[𝕜] E} {l : Filter ι}
    (hPproj : ∀ i, IsOrthogonalProjectionMap (P i))
    (hP : StronglyTendsto P l (ContinuousLinearMap.id 𝕜 E))
    (n : ℕ) (K : E →L[𝕜] F) :
    Tendsto
      (fun i => approximationSingularValue n (K ∘L P i))
      l (𝓝 (approximationSingularValue n K)) :=
  HasApproximationNumberStrongCutoff.tendsto_comp_strongProjection
    (𝕜 := 𝕜) hPproj hP n K

/-- Ky Fan's addition inequality for approximation numbers. -/
theorem kyFanApproximationGauge_add_le
    [HasKyFanApproximationGaugeTriangle 𝕜]
    (k : ℕ) (K L : E →L[𝕜] F) :
    kyFanApproximationGauge k (K + L) ≤
      kyFanApproximationGauge k K + kyFanApproximationGauge k L :=
  HasKyFanApproximationGaugeTriangle.add_le (𝕜 := 𝕜) k K L


/-- Ky Fan gauges converge under strong orthogonal cutoffs. -/
theorem kyFanApproximationGauge_comp_strongProjection_tendsto
    [HasApproximationNumberStrongCutoff 𝕜]
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
noncomputable def kyFan [HasKyFanApproximationGaugeTriangle 𝕜]
    (k : ℕ) (hk : 0 < k) :
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
theorem kyFan_mem [HasKyFanApproximationGaugeTriangle 𝕜]
    (k : ℕ) (hk : 0 < k) (K : E →L[𝕜] F) :
    (kyFan (𝕜 := 𝕜) k hk).toRectangularSymmetricIdealFamily.Mem K :=
  trivial

/-- The concrete gauge of the fixed finite Ky Fan family. -/
@[simp]
theorem kyFan_gauge [HasKyFanApproximationGaugeTriangle 𝕜]
    (k : ℕ) (hk : 0 < k) (K : E →L[𝕜] F) :
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

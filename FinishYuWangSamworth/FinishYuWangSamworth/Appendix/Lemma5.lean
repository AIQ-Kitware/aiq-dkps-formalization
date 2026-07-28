/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import FinishYuWangSamworth.Rectangular.FrobeniusGram

/-!
# Yu--Wang--Samworth Appendix Lemma 5

The paper states the result for matrices with orthonormal columns or rows.  The
basis-free formulation is a two-sided ideal estimate for the rectangular
Frobenius norm.  Orthonormal-column matrices have operator norm at most one;
for the row case the displayed recovery identity gives the reverse inequality.
This formulation is both source recognizable and reusable across dimensions.
-/

namespace TauCeti
namespace DavisKahanTheory

open scoped InnerProductSpace ENNReal
open DavisKahan.Experimental.ExactSinTheta

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]
variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [FiniteDimensional 𝕜 G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [FiniteDimensional 𝕜 H]

private theorem isPaperHilbertSchmidt_finite_appendix
    (A : E →L[𝕜] F) [CompleteSpace E] [CompleteSpace F] :
    IsPaperHilbertSchmidt A := by
  unfold IsPaperHilbertSchmidt
  rw [paperHilbertSchmidtEnergy_eq_ofReal_sum_sq_singularValues]
  exact ENNReal.ofReal_ne_top

/-- Basis-free two-sided Frobenius ideal inequality underlying Lemma 5. -/
theorem rectangularFrobenius_twoSided_comp_le
    (L : F →ₗ[𝕜] G) (A : E →ₗ[𝕜] F) (R : H →ₗ[𝕜] E) :
    RectangularUnitarilyInvariantNorm.frobenius (L ∘ₗ A ∘ₗ R) ≤
      ‖L.toContinuousLinearMap‖ *
        RectangularUnitarilyInvariantNorm.frobenius A *
          ‖R.toContinuousLinearMap‖ := by
  letI : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  letI : CompleteSpace F := FiniteDimensional.complete 𝕜 F
  letI : CompleteSpace G := FiniteDimensional.complete 𝕜 G
  letI : CompleteSpace H := FiniteDimensional.complete 𝕜 H
  have hA : IsPaperHilbertSchmidt A.toContinuousLinearMap :=
    isPaperHilbertSchmidt_finite_appendix A.toContinuousLinearMap
  have h := paperHilbertSchmidtNorm_comp_le
    L.toContinuousLinearMap hA R.toContinuousLinearMap
  rw [paperHilbertSchmidtNorm_eq_rectangularFrobenius,
    paperHilbertSchmidtNorm_eq_rectangularFrobenius] at h
  have hcomp :
      (L.toContinuousLinearMap ∘L A.toContinuousLinearMap ∘L
        R.toContinuousLinearMap).toLinearMap = L ∘ₗ A ∘ₗ R := by
    ext x
    rfl
  rwa [hcomp] at h

/-- Lemma 5, orthonormal-column/contraction form:
`‖U⋆ A W‖_F ≤ ‖A‖_F`. -/
theorem yuWangSamworth_lemma5_columns
    {P : Type*} [NormedAddCommGroup P] [InnerProductSpace 𝕜 P]
      [FiniteDimensional 𝕜 P]
    {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace 𝕜 Q]
      [FiniteDimensional 𝕜 Q]
    (A : E →ₗ[𝕜] F) (U : P →ₗ[𝕜] F) (W : Q →ₗ[𝕜] E)
    (hU : ‖U.toContinuousLinearMap‖ ≤ 1)
    (hW : ‖W.toContinuousLinearMap‖ ≤ 1) :
    RectangularUnitarilyInvariantNorm.frobenius
        (U.adjoint ∘ₗ A ∘ₗ W) ≤
      RectangularUnitarilyInvariantNorm.frobenius A := by
  have h := rectangularFrobenius_twoSided_comp_le U.adjoint A W
  have hUnorm :
      ‖U.adjoint.toContinuousLinearMap‖ = ‖U.toContinuousLinearMap‖ := by
    simp only [LinearMap.adjoint_toContinuousLinearMap,
      LinearIsometryEquiv.norm_map]
  rw [hUnorm] at h
  have hF : 0 ≤ RectangularUnitarilyInvariantNorm.frobenius A :=
    (RectangularUnitarilyInvariantNorm.frobenius (𝕜 := 𝕜)).nonneg A
  calc
    RectangularUnitarilyInvariantNorm.frobenius (U.adjoint ∘ₗ A ∘ₗ W)
        ≤ ‖U.toContinuousLinearMap‖ *
            RectangularUnitarilyInvariantNorm.frobenius A *
              ‖W.toContinuousLinearMap‖ := h
    _ ≤ 1 * RectangularUnitarilyInvariantNorm.frobenius A *
          ‖W.toContinuousLinearMap‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hU hF) (norm_nonneg _)
    _ ≤ 1 * RectangularUnitarilyInvariantNorm.frobenius A * 1 := by
      exact mul_le_mul_of_nonneg_left hW (by simpa using hF)
    _ = RectangularUnitarilyInvariantNorm.frobenius A := by ring

/-- Lemma 5 with the source's orthonormal-column hypotheses expressed
coordinate-freely as pointwise norm preservation. -/
theorem yuWangSamworth_lemma5_isometricColumns
    {P : Type*} [NormedAddCommGroup P] [InnerProductSpace 𝕜 P]
      [FiniteDimensional 𝕜 P]
    {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace 𝕜 Q]
      [FiniteDimensional 𝕜 Q]
    (A : E →ₗ[𝕜] F) (U : P →ₗ[𝕜] F) (W : Q →ₗ[𝕜] E)
    (hU : ∀ x : P, ‖U x‖ = ‖x‖)
    (hW : ∀ x : Q, ‖W x‖ = ‖x‖) :
    RectangularUnitarilyInvariantNorm.frobenius
        (U.adjoint ∘ₗ A ∘ₗ W) ≤
      RectangularUnitarilyInvariantNorm.frobenius A := by
  have hUnorm : ‖U.toContinuousLinearMap‖ ≤ 1 := by
    refine U.toContinuousLinearMap.opNorm_le_bound zero_le_one ?_
    intro x
    change ‖U x‖ ≤ 1 * ‖x‖
    calc
      ‖U x‖ = ‖x‖ := hU x
      _ ≤ 1 * ‖x‖ := by simp
  have hWnorm : ‖W.toContinuousLinearMap‖ ≤ 1 := by
    refine W.toContinuousLinearMap.opNorm_le_bound zero_le_one ?_
    intro x
    change ‖W x‖ ≤ 1 * ‖x‖
    calc
      ‖W x‖ = ‖x‖ := hW x
      _ ≤ 1 * ‖x‖ := by simp
  exact yuWangSamworth_lemma5_columns A U W hUnorm hWnorm

/-- Lemma 5, orthonormal-row form.  The explicit recovery identity is the
coordinate-free content of the row-orthonormal hypotheses. -/
theorem yuWangSamworth_lemma5_rows
    {P : Type*} [NormedAddCommGroup P] [InnerProductSpace 𝕜 P]
      [FiniteDimensional 𝕜 P]
    {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace 𝕜 Q]
      [FiniteDimensional 𝕜 Q]
    (A : E →ₗ[𝕜] F) (U : P →ₗ[𝕜] F) (W : Q →ₗ[𝕜] E)
    (hU : ‖U.toContinuousLinearMap‖ ≤ 1)
    (hW : ‖W.toContinuousLinearMap‖ ≤ 1)
    (hrecover : U ∘ₗ (U.adjoint ∘ₗ A ∘ₗ W) ∘ₗ W.adjoint = A) :
    RectangularUnitarilyInvariantNorm.frobenius
        (U.adjoint ∘ₗ A ∘ₗ W) =
      RectangularUnitarilyInvariantNorm.frobenius A := by
  apply le_antisymm
  · exact yuWangSamworth_lemma5_columns A U W hU hW
  · have h := rectangularFrobenius_twoSided_comp_le
      U (U.adjoint ∘ₗ A ∘ₗ W) W.adjoint
    have hWnorm :
        ‖W.adjoint.toContinuousLinearMap‖ = ‖W.toContinuousLinearMap‖ := by
      simp only [LinearMap.adjoint_toContinuousLinearMap,
        LinearIsometryEquiv.norm_map]
    rw [hrecover, hWnorm] at h
    have hC : 0 ≤ RectangularUnitarilyInvariantNorm.frobenius
        (U.adjoint ∘ₗ A ∘ₗ W) :=
      (RectangularUnitarilyInvariantNorm.frobenius (𝕜 := 𝕜)).nonneg _
    calc
      RectangularUnitarilyInvariantNorm.frobenius A
          ≤ ‖U.toContinuousLinearMap‖ *
              RectangularUnitarilyInvariantNorm.frobenius
                (U.adjoint ∘ₗ A ∘ₗ W) *
                ‖W.toContinuousLinearMap‖ := h
      _ ≤ 1 * RectangularUnitarilyInvariantNorm.frobenius
            (U.adjoint ∘ₗ A ∘ₗ W) * ‖W.toContinuousLinearMap‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hU hC) (norm_nonneg _)
      _ ≤ 1 * RectangularUnitarilyInvariantNorm.frobenius
            (U.adjoint ∘ₗ A ∘ₗ W) * 1 := by
        exact mul_le_mul_of_nonneg_left hW (by simpa using hC)
      _ = RectangularUnitarilyInvariantNorm.frobenius
            (U.adjoint ∘ₗ A ∘ₗ W) := by ring

end DavisKahanTheory
end TauCeti

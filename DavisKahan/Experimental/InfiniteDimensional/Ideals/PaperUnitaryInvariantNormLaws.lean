/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.Ideals.PaperUnitaryInvariantNorm

/-!
# Operator laws for the source-defined unitarily invariant norms

`PaperUnitaryInvariantNorm` is the literal coherent symmetric-gauge object used
in Davis--Kahan 1970.  This file proves that its canonical prefix-supremum
extension has all of the operator properties used in the paper: normalization,
absolute homogeneity, triangle inequality, adjoint invariance, two-sided
unitary invariance, contraction compatibility, and the ideal property.

Thus the universal theorem quantified over `PaperUnitaryInvariantNorm` does not
hide an independently postulated operator ideal.  The ideal and its norm are
constructed from the single source gauge exactly as in the paper.
-/

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open scoped InnerProductSpace BigOperators ENNReal

noncomputable section

universe u v

namespace PaperUnitaryInvariantNorm

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F G : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]

/-- The source norm of the zero operator is zero. -/
@[simp]
theorem extendedGauge_zero (N : PaperUnitaryInvariantNorm) :
    N.extendedGauge (0 : E →L[𝕜] F) = 0 := by
  apply le_antisymm
  · apply iSup_le
    intro n
    simp [extendedGauge, prefixGauge, approximationPrefix,
      approximationSingularValue_zero_map, finiteGauge_def]
  · exact bot_le

/-- Absolute homogeneity of the extended source norm. -/
theorem extendedGauge_smul (N : PaperUnitaryInvariantNorm)
    (c : 𝕜) (A : E →L[𝕜] F) :
    N.extendedGauge (c • A) = ENNReal.ofReal ‖c‖ * N.extendedGauge A := by
  by_cases hc : c = 0
  · subst c
    simp
  · unfold extendedGauge
    rw [ENNReal.mul_iSup]
    apply iSup_congr
    intro n
    rw [← ENNReal.ofReal_mul (norm_nonneg c)]
    congr 1
    unfold prefixGauge approximationPrefix
    have hprefix :
        (fun i : Fin n => approximationSingularValue (i : ℕ) (c • A)) =
          ‖c‖ • (fun i : Fin n => approximationSingularValue (i : ℕ) A) := by
      funext i
      rw [approximationSingularValue_smul]
      simp [smul_eq_mul]
    rw [hprefix, N.finiteGauge_smul]
    simp [abs_of_nonneg (norm_nonneg c)]

/-- Triangle inequality for each finite prefix gauge. -/
theorem prefixGauge_add_le (N : PaperUnitaryInvariantNorm)
    (n : ℕ) (A B : E →L[𝕜] F) :
    N.prefixGauge n (A + B) ≤ N.prefixGauge n A + N.prefixGauge n B := by
  let x : Fin n → ℝ := N.approximationPrefix n (A + B)
  let y : Fin n → ℝ :=
    N.approximationPrefix n A + N.approximationPrefix n B
  have hmajor : N.finiteGauge n x ≤ N.finiteGauge n y := by
    apply (N.finiteNorm n).gauge_le_gauge_of_prefix_sums_le
      (EuclideanSpace.basisFun (Fin n) ℂ)
    · intro i j hij
      exact approximationSingularValue_antitone (A + B) (Fin.le_def.mp hij)
    · intro i
      exact approximationSingularValue_nonneg _ _
    · intro i
      exact add_nonneg (approximationSingularValue_nonneg _ _)
        (approximationSingularValue_nonneg _ _)
    · intro m
      rcases le_or_gt m n with hm | hm
      · simpa [x, y, approximationPrefix, Finset.sum_add_distrib,
          sum_filter_lt_eq_sum_fin hm,
          PaperUnitaryInvariantNorm.sum_approximationPrefix] using
          kyFanApproximationGauge_add_le m A B
      · have huniv :
          (Finset.univ.filter fun i : Fin n => (i : ℕ) < m) = Finset.univ :=
          Finset.filter_true_of_mem fun i _ => lt_trans i.isLt hm
        rw [huniv, huniv]
        simpa [x, y, Finset.sum_add_distrib,
          PaperUnitaryInvariantNorm.sum_approximationPrefix] using
          kyFanApproximationGauge_add_le n A B
  exact hmajor.trans (N.finiteGauge_add_le _ _)

/-- Triangle inequality of the canonical infinite-dimensional extension. -/
theorem extendedGauge_add_le (N : PaperUnitaryInvariantNorm)
    (A B : E →L[𝕜] F) :
    N.extendedGauge (A + B) ≤ N.extendedGauge A + N.extendedGauge B := by
  apply iSup_le
  intro n
  calc
    ENNReal.ofReal (N.prefixGauge n (A + B)) ≤
        ENNReal.ofReal (N.prefixGauge n A + N.prefixGauge n B) :=
      ENNReal.ofReal_le_ofReal (N.prefixGauge_add_le n A B)
    _ = ENNReal.ofReal (N.prefixGauge n A) +
        ENNReal.ofReal (N.prefixGauge n B) := by
      rw [ENNReal.ofReal_add (N.finiteGauge_nonneg _) (N.finiteGauge_nonneg _)]
    _ ≤ N.extendedGauge A + N.extendedGauge B :=
      add_le_add
        (le_iSup (fun m => ENNReal.ofReal (N.prefixGauge m A)) n)
        (le_iSup (fun m => ENNReal.ofReal (N.prefixGauge m B)) n)

/-- Adjoint invariance of the source norm. -/
theorem extendedGauge_adjoint (N : PaperUnitaryInvariantNorm)
    (A : E →L[𝕜] F) :
    N.extendedGauge A.adjoint = N.extendedGauge A := by
  exact N.gauge_eq_of_sameApproximationSingularValues
    (fun n => approximationSingularValue_adjoint A n)

/-- Unitary equivalences on either side preserve the complete source norm. -/
theorem extendedGauge_unitary
    (N : PaperUnitaryInvariantNorm)
    (U : F ≃ₗᵢ[𝕜] F) (V : E ≃ₗᵢ[𝕜] E) (A : E →L[𝕜] F) :
    N.extendedGauge
      (U.toContinuousLinearEquiv.toContinuousLinearMap ∘L A ∘L
        V.toContinuousLinearEquiv.toContinuousLinearMap) =
      N.extendedGauge A := by
  exact N.gauge_eq_of_sameApproximationSingularValues
    (SameApproximationSingularValues.comp_isometricEquiv U V A)

/-- The two-sided ideal estimate at the extended-value level. -/
theorem extendedGauge_comp_le (N : PaperUnitaryInvariantNorm)
    (L : F →L[𝕜] G) (A : E →L[𝕜] F) (R : E →L[𝕜] E) :
    N.extendedGauge (L ∘L A ∘L R) ≤
      ENNReal.ofReal ‖L‖ * N.extendedGauge A * ENNReal.ofReal ‖R‖ := by
  apply N.extendedGauge_le_of_all_kyFan_le
  intro k
  calc
    kyFanApproximationGauge k (L ∘L A ∘L R)
        ≤ ‖L‖ * kyFanApproximationGauge k A * ‖R‖ :=
      kyFanApproximationGauge_comp_le k L A R
    _ = kyFanApproximationGauge k
        (((‖L‖ * ‖R‖ : ℝ) : 𝕜) • A) := by
      rw [kyFanApproximationGauge_smul]
      simp [abs_of_nonneg, norm_nonneg, mul_assoc, mul_left_comm]

/-- Membership is a two-sided operator ideal. -/
theorem comp_mem (N : PaperUnitaryInvariantNorm)
    {A : E →L[𝕜] F} (hA : N.Mem A)
    (L : F →L[𝕜] G) (R : E →L[𝕜] E) :
    N.Mem (L ∘L A ∘L R) := by
  have hle := N.extendedGauge_comp_le L A R
  intro htop
  rw [htop] at hle
  have hfinite :
      ENNReal.ofReal ‖L‖ * N.extendedGauge A * ENNReal.ofReal ‖R‖ ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top
      · exact ENNReal.ofReal_ne_top
      · exact hA
    · exact ENNReal.ofReal_ne_top
  exact hfinite (top_le_iff.mp hle)

/-- The real gauge is absolutely homogeneous on its ideal. -/
theorem gauge_smul (N : PaperUnitaryInvariantNorm)
    (c : 𝕜) {A : E →L[𝕜] F} (hA : N.Mem A) :
    N.gauge (c • A) = ‖c‖ * N.gauge A := by
  rw [gauge, N.extendedGauge_smul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (norm_nonneg c)]

/-- The real gauge is subadditive on its canonical ideal. -/
theorem gauge_add_le (N : PaperUnitaryInvariantNorm)
    {A B : E →L[𝕜] F} (hA : N.Mem A) (hB : N.Mem B) :
    N.gauge (A + B) ≤ N.gauge A + N.gauge B := by
  have hAB : N.Mem (A + B) := by
    intro htop
    have hle := N.extendedGauge_add_le A B
    rw [htop] at hle
    exact ENNReal.add_ne_top.mpr ⟨hA, hB⟩ (top_le_iff.mp hle)
  exact ENNReal.toReal_le_toReal (N.extendedGauge_add_le A B)
    hAB (ENNReal.add_ne_top.mpr ⟨hA, hB⟩)

/-- Exact ideal inequality for the real-valued source norm. -/
theorem gauge_comp_le (N : PaperUnitaryInvariantNorm)
    {A : E →L[𝕜] F} (hA : N.Mem A)
    (L : F →L[𝕜] G) (R : E →L[𝕜] E) :
    N.gauge (L ∘L A ∘L R) ≤ ‖L‖ * N.gauge A * ‖R‖ := by
  have hcomp := N.comp_mem hA L R
  have hle := N.extendedGauge_comp_le L A R
  have hto := ENNReal.toReal_le_toReal hle hcomp (by
    apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top
      · exact ENNReal.ofReal_ne_top
      · exact hA
    · exact ENNReal.ofReal_ne_top)
  simpa [gauge, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (norm_nonneg _)] using hto

/-- The canonical source norm satisfies the contraction-compatibility law
used in the paper. -/
theorem gauge_comp_le_of_contractions (N : PaperUnitaryInvariantNorm)
    {A : E →L[𝕜] F} (hA : N.Mem A)
    (L : F →L[𝕜] G) (R : E →L[𝕜] E)
    (hL : ‖L‖ ≤ 1) (hR : ‖R‖ ≤ 1) :
    N.gauge (L ∘L A ∘L R) ≤ N.gauge A := by
  refine (N.gauge_comp_le hA L R).trans ?_
  have hnonneg := ENNReal.toReal_nonneg
  nlinarith [norm_nonneg L, norm_nonneg R,
    N.finiteGauge_nonneg (N.approximationPrefix 1 A)]

end PaperUnitaryInvariantNorm

end

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib

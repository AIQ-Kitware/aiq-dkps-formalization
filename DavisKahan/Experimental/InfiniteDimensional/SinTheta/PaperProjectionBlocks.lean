/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import ForMathlib.Analysis.InnerProductSpace.ProjectionBlocks
import DavisKahan.Experimental.InfiniteDimensional.Ideals.PaperUnitaryInvariantNorm

/-!
# Projection-block lemmas from Davis--Kahan section 6

This file formalizes the two elementary projection lemmas used verbatim in the
paper's proof of the symmetric sine theorem.

* `paperDiagonalPair` is `Omega K Gamma + OmegaComplement K GammaComplement`.
  Its reflection identity is the displayed proof of Lemma 6.2.
* `paperCrossSineSum` is the sum of the two complementary cross projections.
  Right composition by the target reflection turns it into the projector
  difference.  Since the reflection is an involutive isometry, the two
  operators have identical complete approximation-singular-value sequences.

The results are proved both for the existing ideal-family interface and for the
literal paper norm represented by `PaperUnitaryInvariantNorm`.
-/

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open scoped InnerProductSpace

noncomputable section

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- The pair of diagonal projection blocks from Davis--Kahan Lemma 6.2. -/
def paperDiagonalPair (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (K : E →L[𝕜] E) : E →L[𝕜] E :=
  U.starProjection ∘L K ∘L V.starProjection +
    Uᗮ.starProjection ∘L K ∘L Vᗮ.starProjection

/-- The reflection identity displayed in the proof of Davis--Kahan Lemma 6.2. -/
theorem two_smul_paperDiagonalPair_eq_add_reflections
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (K : E →L[𝕜] E) :
    (2 : 𝕜) • paperDiagonalPair U V K =
      K + U.reflectionOperator ∘L K ∘L V.reflectionOperator := by
  ext x
  simp only [paperDiagonalPair, ContinuousLinearMap.comp_apply, add_apply,
    smul_apply]
  simp_rw [Submodule.starProjection_orthogonal_apply,
    Submodule.reflectionOperator_apply]
  simp only [map_sub, map_smul]
  module

/-- Ideal membership for the diagonal pair. -/
theorem paperDiagonalPair_mem
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {K : E →L[𝕜] E} (hK : N.Mem K) :
    N.Mem (paperDiagonalPair U V K) := by
  exact N.add_mem
    (N.comp_mem U.starProjection V.starProjection hK)
    (N.comp_mem Uᗮ.starProjection Vᗮ.starProjection hK)

/-- **Davis--Kahan Lemma 6.2 for an arbitrary rectangular symmetric ideal.** -/
theorem paperDiagonalPair_gauge_le
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {K : E →L[𝕜] E} (hK : N.Mem K) :
    N.gauge (paperDiagonalPair U V K) ≤ N.gauge K := by
  have hB : N.Mem (paperDiagonalPair U V K) :=
    paperDiagonalPair_mem N U V hK
  have hJ : N.Mem
      (U.reflectionOperator ∘L K ∘L V.reflectionOperator) :=
    N.comp_mem U.reflectionOperator V.reflectionOperator hK
  have hJle :
      N.gauge (U.reflectionOperator ∘L K ∘L V.reflectionOperator) ≤
        N.gauge K :=
    N.gauge_comp_le_of_contractions _ _ hK
      (Submodule.norm_reflectionOperator_le_one U)
      (Submodule.norm_reflectionOperator_le_one V)
  have hsum : N.gauge
      (K + U.reflectionOperator ∘L K ∘L V.reflectionOperator) ≤
        N.gauge K + N.gauge
          (U.reflectionOperator ∘L K ∘L V.reflectionOperator) :=
    N.gauge_add_le hK hJ
  have htwo : N.gauge ((2 : 𝕜) • paperDiagonalPair U V K) =
      2 * N.gauge (paperDiagonalPair U V K) := by
    rw [N.gauge_smul (2 : 𝕜) hB]
    norm_num
  rw [two_smul_paperDiagonalPair_eq_add_reflections U V K, htwo] at hsum
  linarith

/-- Lemma 6.2 simultaneously for every finite Ky Fan approximation gauge. -/
theorem paperDiagonalPair_all_kyFan_le
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (K : E →L[𝕜] E) :
    ∀ k : ℕ,
      kyFanApproximationGauge k (paperDiagonalPair U V K) ≤
        kyFanApproximationGauge k K := by
  intro k
  by_cases hk0 : k = 0
  · subst k
    simp [kyFanApproximationGauge]
  · have hk : 0 < k := Nat.pos_of_ne_zero hk0
    let N := KyFanDominantIdealFamily.kyFan (𝕜 := 𝕜) k hk
    have h := paperDiagonalPair_gauge_le
      N.toRectangularSymmetricIdealFamily U V
      (KyFanDominantIdealFamily.kyFan_mem (𝕜 := 𝕜) k hk K)
    simpa only [N, KyFanDominantIdealFamily.kyFan_gauge] using h

/-- Literal source-norm form of Davis--Kahan Lemma 6.2. -/
theorem paperDiagonalPair_paperNorm_le
    (N : PaperUnitaryInvariantNorm)
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (K : E →L[𝕜] E) :
    N.extendedGauge (paperDiagonalPair U V K) ≤ N.extendedGauge K :=
  N.extendedGauge_le_of_all_kyFan_le
    (paperDiagonalPair_all_kyFan_le U V K)

/-- Real-valued source-norm form on the canonical ideal. -/
theorem paperDiagonalPair_paperGauge_le
    (N : PaperUnitaryInvariantNorm)
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {K : E →L[𝕜] E} (hK : N.Mem K) :
    N.Mem (paperDiagonalPair U V K) ∧
      N.gauge (paperDiagonalPair U V K) ≤ N.gauge K := by
  have hle := paperDiagonalPair_paperNorm_le N U V K
  have hB : N.Mem (paperDiagonalPair U V K) := by
    intro htop
    rw [htop] at hle
    exact hK (top_le_iff.mp hle)
  refine ⟨hB, ?_⟩
  exact ENNReal.toReal_le_toReal hle
    (by simpa [PaperUnitaryInvariantNorm.Mem] using hB)
    (by simpa [PaperUnitaryInvariantNorm.Mem] using hK)

/-- Right composition with a subspace reflection preserves every approximation
singular value. -/
theorem sameApproximationSingularValues_comp_reflection_right
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (A : E →L[𝕜] E) :
    SameApproximationSingularValues
      (A ∘L U.reflectionOperator) A := by
  intro n
  have hright (T : E →L[𝕜] E) :
      approximationSingularValue n (T ∘L U.reflectionOperator) ≤
        approximationSingularValue n T := by
    have hraw := congrArg (fun x : NNReal => (x : ℝ))
      (T.approximationNumber_comp_right_le U.reflectionOperator n)
    have hle :
        approximationSingularValue n (T ∘L U.reflectionOperator) ≤
          approximationSingularValue n T * ‖U.reflectionOperator‖ := by
      simpa only [approximationSingularValue, NNReal.coe_mul, coe_nnnorm]
        using hraw
    exact hle.trans (mul_le_of_le_one_right
      (approximationSingularValue_nonneg n T)
      (Submodule.norm_reflectionOperator_le_one U))
  apply le_antisymm
  · exact hright A
  · have hcomp :
        (A ∘L U.reflectionOperator) ∘L U.reflectionOperator = A := by
      rw [← ContinuousLinearMap.comp_assoc,
        U.reflectionOperator_involutive]
      simp
    rw [← hcomp]
    exact hright (A ∘L U.reflectionOperator)

/-- Left composition with a subspace reflection preserves every approximation
singular value. -/
theorem sameApproximationSingularValues_comp_reflection_left
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (A : E →L[𝕜] E) :
    SameApproximationSingularValues
      (U.reflectionOperator ∘L A) A := by
  intro n
  have hleft (T : E →L[𝕜] E) :
      approximationSingularValue n (U.reflectionOperator ∘L T) ≤
        approximationSingularValue n T := by
    have hraw := congrArg (fun x : NNReal => (x : ℝ))
      (T.approximationNumber_comp_left_le U.reflectionOperator n)
    have hle :
        approximationSingularValue n (U.reflectionOperator ∘L T) ≤
          ‖U.reflectionOperator‖ * approximationSingularValue n T := by
      simpa only [approximationSingularValue, NNReal.coe_mul, coe_nnnorm]
        using hraw
    exact hle.trans (mul_le_of_le_one_left
      (approximationSingularValue_nonneg n T)
      (Submodule.norm_reflectionOperator_le_one U))
  apply le_antisymm
  · exact hleft A
  · have hcomp :
        U.reflectionOperator ∘L (U.reflectionOperator ∘L A) = A := by
      rw [ContinuousLinearMap.comp_assoc,
        U.reflectionOperator_involutive]
      simp
    rw [← hcomp]
    exact hleft (U.reflectionOperator ∘L A)

/-- Sum of the two cross-projection blocks appearing in Proposition 6.1. -/
def paperCrossSineSum (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[𝕜] E :=
  Uᗮ.starProjection ∘L V.starProjection +
    U.starProjection ∘L Vᗮ.starProjection

/-- The cross-block sum is the projector difference followed by the target
reflection. -/
theorem paperCrossSineSum_eq_projectionDiff_comp_reflection
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    paperCrossSineSum U V =
      (V.starProjection - U.starProjection) ∘L V.reflectionOperator := by
  ext x
  simp only [paperCrossSineSum, ContinuousLinearMap.comp_apply, add_apply,
    sub_apply]
  rw [Submodule.reflectionOperator_apply]
  simp_rw [Submodule.starProjection_orthogonal_apply]
  simp only [map_sub, map_smul]
  have hVidem : V.starProjection (V.starProjection x) = V.starProjection x :=
    congrArg (fun T : E →L[𝕜] E => T x) V.isIdempotentElem_starProjection
  have hUadd := U.starProjection_add_starProjection_orthogonal
    (V.starProjection x)
  rw [hVidem]
  module

/-- The cross-block sum has exactly the complete singular-value sequence of the
projector difference. -/
theorem paperCrossSineSum_same_projectionDiff
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    SameApproximationSingularValues
      (paperCrossSineSum U V) (V.starProjection - U.starProjection) := by
  rw [paperCrossSineSum_eq_projectionDiff_comp_reflection]
  exact sameApproximationSingularValues_comp_reflection_right V _

end

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib

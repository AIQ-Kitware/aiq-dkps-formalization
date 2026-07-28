/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import FinishYuWangSamworth.Rectangular.FrobeniusGram

/-!
# Exact Yu--Wang--Samworth Theorem 4

This module packages the rectangular theorem through the two Gram operators.
The proof is deliberately factored into three layers:

1. a generic transport theorem applies the already formalized symmetric
   Yu--Wang--Samworth theorem to any pair of self-adjoint Gram operators;
2. the right and left wrappers supply only their operator/Frobenius Gram
   perturbation estimates;
3. source-shaped corollaries rewrite the population operator norm as the top
   singular value `σ₁`.

Thus the right and left statements cannot drift apart, and the paper's
`min (sqrt d * ||Ahat-A||_op) ||Ahat-A||_F` numerator is assembled only once.
-/

namespace TauCeti
namespace DavisKahanTheory

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- Ordered-index correspondence for right singular blocks, expressed through
squared singular values of the right Gram operators. -/
def CorrespondingRightSingularBlock (A Â : E →ₗ[𝕜] F)
    (U V : Submodule 𝕜 E) : Prop :=
  CorrespondingEigenblock (isSymmetric_rightGram A)
    (isSymmetric_rightGram Â) U V

/-- Ordered-index correspondence for left singular blocks. -/
def CorrespondingLeftSingularBlock (A Â : E →ₗ[𝕜] F)
    (U V : Submodule 𝕜 F) : Prop :=
  CorrespondingEigenblock (isSymmetric_leftGram A)
    (isSymmetric_leftGram Â) U V

/-- Population squared-singular-value gap for a right singular block. -/
def RightSingularPopulationGap (A : E →ₗ[𝕜] F)
    (U : Submodule 𝕜 E) (Δ : ℝ) : Prop :=
  PopulationGap (rightGram A) U Δ

/-- Population squared-singular-value gap for a left singular block. -/
def LeftSingularPopulationGap (A : E →ₗ[𝕜] F)
    (U : Submodule 𝕜 F) (Δ : ℝ) : Prop :=
  PopulationGap (leftGram A) U Δ

private theorem correspondingEigenblock_reduces_population
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [FiniteDimensional 𝕜 H]
    {G Ĝ : H →ₗ[𝕜] H} (hG : G.IsSymmetric) (hĜ : Ĝ.IsSymmetric)
    {U V : Submodule 𝕜 H}
    (hcorr : CorrespondingEigenblock hG hĜ U V) : Reduces G U := by
  obtain ⟨n, hn, s, hU, -⟩ := hcorr
  rw [hU]
  exact reduces_spanIndices hG hn ↑s

private theorem correspondingEigenblock_reduces_perturbed
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [FiniteDimensional 𝕜 H]
    {G Ĝ : H →ₗ[𝕜] H} (hG : G.IsSymmetric) (hĜ : Ĝ.IsSymmetric)
    {U V : Submodule 𝕜 H}
    (hcorr : CorrespondingEigenblock hG hĜ U V) : Reduces Ĝ V := by
  obtain ⟨n, hn, s, -, hV⟩ := hcorr
  rw [hV]
  exact reduces_spanIndices hĜ hn ↑s

private theorem correspondingEigenblock_finrank_eq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [FiniteDimensional 𝕜 H]
    {G Ĝ : H →ₗ[𝕜] H} (hG : G.IsSymmetric) (hĜ : Ĝ.IsSymmetric)
    {U V : Submodule 𝕜 H}
    (hcorr : CorrespondingEigenblock hG hĜ U V) :
    finrank 𝕜 U = finrank 𝕜 V := by
  obtain ⟨n, hn, s, hU, hV⟩ := hcorr
  rw [hU, hV, (hG.eigenvectorBasis hn).finrank_spanIndices,
    (hĜ.eigenvectorBasis hn).finrank_spanIndices]

/-- The minimum in Theorem 2 transports through a common Gram coefficient
without choosing an operator/Frobenius branch globally. -/
private theorem gram_min_le_scaled_min {d : ℕ}
    {gramOp gramFrob c perturbOp perturbFrob : ℝ}
    (hop : gramOp ≤ c * perturbOp)
    (hfrob : gramFrob ≤ c * perturbFrob) :
    min (Real.sqrt d * gramOp) gramFrob ≤
      c * min (Real.sqrt d * perturbOp) perturbFrob := by
  have hop' :
      Real.sqrt d * gramOp ≤ c * (Real.sqrt d * perturbOp) := by
    calc
      Real.sqrt d * gramOp ≤ Real.sqrt d * (c * perturbOp) :=
        mul_le_mul_of_nonneg_left hop (Real.sqrt_nonneg d)
      _ = c * (Real.sqrt d * perturbOp) := by ring
  rcases le_total (Real.sqrt d * perturbOp) perturbFrob with hmin | hmin
  · rw [min_eq_left hmin]
    exact (min_le_left _ _).trans hop'
  · rw [min_eq_right hmin]
    exact (min_le_right _ _).trans hfrob

/-- Generic Gram transport for the sine-distance part of Theorem 4. -/
private theorem yuWangSamworth_gram_sinTheta_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [FiniteDimensional 𝕜 H]
    {G Ĝ : H →ₗ[𝕜] H} (hG : G.IsSymmetric) (hĜ : Ĝ.IsSymmetric)
    {U V : Submodule 𝕜 H} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection]
    (hcorr : CorrespondingEigenblock hG hĜ U V)
    {d : ℕ} (hrank : finrank 𝕜 U = d)
    {Δ c perturbOp perturbFrob : ℝ} (hΔ : 0 < Δ)
    (hgap : PopulationGap G U Δ)
    (hop : ‖(Ĝ - G).toContinuousLinearMap‖ ≤ c * perturbOp)
    (hfrob : UnitarilyInvariantNorm.frobenius 𝕜 H (Ĝ - G) ≤
      c * perturbFrob) :
    sinThetaFrobenius U V ≤
      2 * c * min (Real.sqrt d * perturbOp) perturbFrob / Δ := by
  have hbase := yuWangSamworth_sinTheta_le hG hĜ
    (correspondingEigenblock_reduces_population hG hĜ hcorr)
    (correspondingEigenblock_reduces_perturbed hG hĜ hcorr)
    hcorr hrank hΔ hgap
  refine hbase.trans ?_
  have hmin := gram_min_le_scaled_min (d := d) hop hfrob
  calc
    2 * min (Real.sqrt d * ‖(Ĝ - G).toContinuousLinearMap‖)
          (UnitarilyInvariantNorm.frobenius 𝕜 H (Ĝ - G)) / Δ
        ≤ 2 * (c * min (Real.sqrt d * perturbOp) perturbFrob) / Δ := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hmin (by norm_num)) hΔ.le
    _ = 2 * c * min (Real.sqrt d * perturbOp) perturbFrob / Δ := by ring

/-- Generic Gram transport for the aligned-frame part of Theorem 4. -/
private theorem yuWangSamworth_gram_alignedBasis_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [FiniteDimensional 𝕜 H]
    {G Ĝ : H →ₗ[𝕜] H} (hG : G.IsSymmetric) (hĜ : Ĝ.IsSymmetric)
    {U V : Submodule 𝕜 H} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection]
    (hcorr : CorrespondingEigenblock hG hĜ U V)
    {d : ℕ} (hrankU : finrank 𝕜 U = d)
    {Δ c perturbOp perturbFrob : ℝ} (hΔ : 0 < Δ)
    (hgap : PopulationGap G U Δ)
    (hop : ‖(Ĝ - G).toContinuousLinearMap‖ ≤ c * perturbOp)
    (hfrob : UnitarilyInvariantNorm.frobenius 𝕜 H (Ĝ - G) ≤
      c * perturbFrob) :
    ∃ (u v : Fin d → H), Orthonormal 𝕜 u ∧ Orthonormal 𝕜 v ∧
      Submodule.span 𝕜 (Set.range u) = U ∧
      Submodule.span 𝕜 (Set.range v) = V ∧
      Real.sqrt (∑ i, ‖v i - u i‖ ^ 2) ≤
        2 * Real.sqrt 2 * c *
          min (Real.sqrt d * perturbOp) perturbFrob / Δ := by
  have hrankV : finrank 𝕜 V = d := by
    rw [← hrankU]
    exact (correspondingEigenblock_finrank_eq hG hĜ hcorr).symm
  obtain ⟨u, v, hu, hv, hspanU, hspanV, hbase⟩ :=
    yuWangSamworth_alignedBasis_le hG hĜ
      (correspondingEigenblock_reduces_population hG hĜ hcorr)
      (correspondingEigenblock_reduces_perturbed hG hĜ hcorr)
      hcorr hrankU hrankV hΔ hgap
  refine ⟨u, v, hu, hv, hspanU, hspanV, hbase.trans ?_⟩
  have hmin := gram_min_le_scaled_min (d := d) hop hfrob
  calc
    2 * Real.sqrt 2 *
          min (Real.sqrt d * ‖(Ĝ - G).toContinuousLinearMap‖)
            (UnitarilyInvariantNorm.frobenius 𝕜 H (Ĝ - G)) / Δ
        ≤ 2 * Real.sqrt 2 *
            (c * min (Real.sqrt d * perturbOp) perturbFrob) / Δ := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hmin (by positivity)) hΔ.le
    _ = 2 * Real.sqrt 2 * c *
          min (Real.sqrt d * perturbOp) perturbFrob / Δ := by ring

/-- Exact right-singular-subspace Theorem 4, in intrinsic operator-norm form. -/
theorem yuWangSamworth_rightSingularSubspace_opNormCoefficient_le
    {A Â : E →ₗ[𝕜] F} {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcorr : CorrespondingRightSingularBlock A Â U V)
    {d : ℕ} (hrank : finrank 𝕜 U = d)
    {Δ : ℝ} (hΔ : 0 < Δ) (hgap : RightSingularPopulationGap A U Δ) :
    sinThetaFrobenius U V ≤
      2 * (2 * ‖A.toContinuousLinearMap‖ +
          ‖(Â - A).toContinuousLinearMap‖) *
        min (Real.sqrt d * ‖(Â - A).toContinuousLinearMap‖)
          (RectangularUnitarilyInvariantNorm.frobenius (Â - A)) / Δ := by
  apply yuWangSamworth_gram_sinTheta_le
    (isSymmetric_rightGram A) (isSymmetric_rightGram Â)
    (by simpa only [CorrespondingRightSingularBlock] using hcorr)
    hrank hΔ
    (by simpa only [RightSingularPopulationGap] using hgap)
  · exact opNorm_rightGram_sub_le_paperCoefficient A Â
  · exact frobenius_rightGram_sub_le_paperCoefficient A Â

/-- Exact left-singular-subspace Theorem 4, in intrinsic operator-norm form. -/
theorem yuWangSamworth_leftSingularSubspace_opNormCoefficient_le
    {A Â : E →ₗ[𝕜] F} {U V : Submodule 𝕜 F}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcorr : CorrespondingLeftSingularBlock A Â U V)
    {d : ℕ} (hrank : finrank 𝕜 U = d)
    {Δ : ℝ} (hΔ : 0 < Δ) (hgap : LeftSingularPopulationGap A U Δ) :
    sinThetaFrobenius U V ≤
      2 * (2 * ‖A.toContinuousLinearMap‖ +
          ‖(Â - A).toContinuousLinearMap‖) *
        min (Real.sqrt d * ‖(Â - A).toContinuousLinearMap‖)
          (RectangularUnitarilyInvariantNorm.frobenius (Â - A)) / Δ := by
  apply yuWangSamworth_gram_sinTheta_le
    (isSymmetric_leftGram A) (isSymmetric_leftGram Â)
    (by simpa only [CorrespondingLeftSingularBlock] using hcorr)
    hrank hΔ
    (by simpa only [LeftSingularPopulationGap] using hgap)
  · exact opNorm_leftGram_sub_le_paperCoefficient A Â
  · exact frobenius_leftGram_sub_le_paperCoefficient A Â

/-- Right-singular aligned-frame conclusion with the intrinsic coefficient. -/
theorem yuWangSamworth_rightSingularAlignedBasis_opNormCoefficient_le
    {A Â : E →ₗ[𝕜] F} {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcorr : CorrespondingRightSingularBlock A Â U V)
    {d : ℕ} (hrank : finrank 𝕜 U = d)
    {Δ : ℝ} (hΔ : 0 < Δ) (hgap : RightSingularPopulationGap A U Δ) :
    ∃ (u v : Fin d → E), Orthonormal 𝕜 u ∧ Orthonormal 𝕜 v ∧
      Submodule.span 𝕜 (Set.range u) = U ∧
      Submodule.span 𝕜 (Set.range v) = V ∧
      Real.sqrt (∑ i, ‖v i - u i‖ ^ 2) ≤
        2 * Real.sqrt 2 *
          (2 * ‖A.toContinuousLinearMap‖ +
            ‖(Â - A).toContinuousLinearMap‖) *
          min (Real.sqrt d * ‖(Â - A).toContinuousLinearMap‖)
            (RectangularUnitarilyInvariantNorm.frobenius (Â - A)) / Δ := by
  apply yuWangSamworth_gram_alignedBasis_le
    (isSymmetric_rightGram A) (isSymmetric_rightGram Â)
    (by simpa only [CorrespondingRightSingularBlock] using hcorr)
    hrank hΔ
    (by simpa only [RightSingularPopulationGap] using hgap)
  · exact opNorm_rightGram_sub_le_paperCoefficient A Â
  · exact frobenius_rightGram_sub_le_paperCoefficient A Â

/-- Left-singular aligned-frame conclusion with the intrinsic coefficient. -/
theorem yuWangSamworth_leftSingularAlignedBasis_opNormCoefficient_le
    {A Â : E →ₗ[𝕜] F} {U V : Submodule 𝕜 F}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcorr : CorrespondingLeftSingularBlock A Â U V)
    {d : ℕ} (hrank : finrank 𝕜 U = d)
    {Δ : ℝ} (hΔ : 0 < Δ) (hgap : LeftSingularPopulationGap A U Δ) :
    ∃ (u v : Fin d → F), Orthonormal 𝕜 u ∧ Orthonormal 𝕜 v ∧
      Submodule.span 𝕜 (Set.range u) = U ∧
      Submodule.span 𝕜 (Set.range v) = V ∧
      Real.sqrt (∑ i, ‖v i - u i‖ ^ 2) ≤
        2 * Real.sqrt 2 *
          (2 * ‖A.toContinuousLinearMap‖ +
            ‖(Â - A).toContinuousLinearMap‖) *
          min (Real.sqrt d * ‖(Â - A).toContinuousLinearMap‖)
            (RectangularUnitarilyInvariantNorm.frobenius (Â - A)) / Δ := by
  apply yuWangSamworth_gram_alignedBasis_le
    (isSymmetric_leftGram A) (isSymmetric_leftGram Â)
    (by simpa only [CorrespondingLeftSingularBlock] using hcorr)
    hrank hΔ
    (by simpa only [LeftSingularPopulationGap] using hgap)
  · exact opNorm_leftGram_sub_le_paperCoefficient A Â
  · exact frobenius_leftGram_sub_le_paperCoefficient A Â

/-- In positive finite domain dimension, the population operator norm is its
top singular value. -/
theorem opNorm_eq_topSingularValue [Nontrivial E] (A : E →ₗ[𝕜] F) :
    ‖A.toContinuousLinearMap‖ = A.singularValues 0 := by
  apply le_antisymm
  · refine A.toContinuousLinearMap.opNorm_le_bound
      (A.singularValues_nonneg 0) fun x => ?_
    exact norm_apply_le_singularValues_zero_mul A rfl Module.finrank_pos x
  · obtain ⟨x, hx, hAx⟩ :=
      exists_norm_apply_eq_singularValues_zero A rfl Module.finrank_pos
    rw [← hAx]
    calc
      ‖A x‖ = ‖A.toContinuousLinearMap x‖ := rfl
      _ ≤ ‖A.toContinuousLinearMap‖ * ‖x‖ :=
        A.toContinuousLinearMap.le_opNorm x
      _ = ‖A.toContinuousLinearMap‖ := by rw [hx, mul_one]

/-- Literal source-coefficient form of the right-singular sine bound. -/
theorem yuWangSamworth_rightSingularSubspace_le
    {A Â : E →ₗ[𝕜] F} {U V : Submodule 𝕜 E} [Nontrivial E]
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcorr : CorrespondingRightSingularBlock A Â U V)
    {d : ℕ} (hrank : finrank 𝕜 U = d)
    {Δ : ℝ} (hΔ : 0 < Δ) (hgap : RightSingularPopulationGap A U Δ) :
    sinThetaFrobenius U V ≤
      2 * (2 * A.singularValues 0 +
          ‖(Â - A).toContinuousLinearMap‖) *
        min (Real.sqrt d * ‖(Â - A).toContinuousLinearMap‖)
          (RectangularUnitarilyInvariantNorm.frobenius (Â - A)) / Δ := by
  simpa only [opNorm_eq_topSingularValue A] using
    yuWangSamworth_rightSingularSubspace_opNormCoefficient_le
      hcorr hrank hΔ hgap

/-- Literal source-coefficient form of the left-singular sine bound. -/
theorem yuWangSamworth_leftSingularSubspace_le
    {A Â : E →ₗ[𝕜] F} {U V : Submodule 𝕜 F} [Nontrivial E]
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcorr : CorrespondingLeftSingularBlock A Â U V)
    {d : ℕ} (hrank : finrank 𝕜 U = d)
    {Δ : ℝ} (hΔ : 0 < Δ) (hgap : LeftSingularPopulationGap A U Δ) :
    sinThetaFrobenius U V ≤
      2 * (2 * A.singularValues 0 +
          ‖(Â - A).toContinuousLinearMap‖) *
        min (Real.sqrt d * ‖(Â - A).toContinuousLinearMap‖)
          (RectangularUnitarilyInvariantNorm.frobenius (Â - A)) / Δ := by
  simpa only [opNorm_eq_topSingularValue A] using
    yuWangSamworth_leftSingularSubspace_opNormCoefficient_le
      hcorr hrank hΔ hgap

/-- Literal source-coefficient right aligned-frame conclusion. -/
theorem yuWangSamworth_rightSingularAlignedBasis_le
    {A Â : E →ₗ[𝕜] F} {U V : Submodule 𝕜 E} [Nontrivial E]
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcorr : CorrespondingRightSingularBlock A Â U V)
    {d : ℕ} (hrank : finrank 𝕜 U = d)
    {Δ : ℝ} (hΔ : 0 < Δ) (hgap : RightSingularPopulationGap A U Δ) :
    ∃ (u v : Fin d → E), Orthonormal 𝕜 u ∧ Orthonormal 𝕜 v ∧
      Submodule.span 𝕜 (Set.range u) = U ∧
      Submodule.span 𝕜 (Set.range v) = V ∧
      Real.sqrt (∑ i, ‖v i - u i‖ ^ 2) ≤
        2 * Real.sqrt 2 *
          (2 * A.singularValues 0 +
            ‖(Â - A).toContinuousLinearMap‖) *
          min (Real.sqrt d * ‖(Â - A).toContinuousLinearMap‖)
            (RectangularUnitarilyInvariantNorm.frobenius (Â - A)) / Δ := by
  simpa only [opNorm_eq_topSingularValue A] using
    yuWangSamworth_rightSingularAlignedBasis_opNormCoefficient_le
      hcorr hrank hΔ hgap

/-- Literal source-coefficient left aligned-frame conclusion. -/
theorem yuWangSamworth_leftSingularAlignedBasis_le
    {A Â : E →ₗ[𝕜] F} {U V : Submodule 𝕜 F} [Nontrivial E]
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcorr : CorrespondingLeftSingularBlock A Â U V)
    {d : ℕ} (hrank : finrank 𝕜 U = d)
    {Δ : ℝ} (hΔ : 0 < Δ) (hgap : LeftSingularPopulationGap A U Δ) :
    ∃ (u v : Fin d → F), Orthonormal 𝕜 u ∧ Orthonormal 𝕜 v ∧
      Submodule.span 𝕜 (Set.range u) = U ∧
      Submodule.span 𝕜 (Set.range v) = V ∧
      Real.sqrt (∑ i, ‖v i - u i‖ ^ 2) ≤
        2 * Real.sqrt 2 *
          (2 * A.singularValues 0 +
            ‖(Â - A).toContinuousLinearMap‖) *
          min (Real.sqrt d * ‖(Â - A).toContinuousLinearMap‖)
            (RectangularUnitarilyInvariantNorm.frobenius (Â - A)) / Δ := by
  simpa only [opNorm_eq_topSingularValue A] using
    yuWangSamworth_leftSingularAlignedBasis_opNormCoefficient_le
      hcorr hrank hΔ hgap

end DavisKahanTheory
end TauCeti

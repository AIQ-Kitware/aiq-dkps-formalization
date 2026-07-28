/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.SinTheta.Unbounded.Core
import DavisKahan.Sylvester.Unbounded.AllGap

/-!
# Genuine-spectrum all-gap unbounded sine-theta theorem

This leaf exposes the complete generalized and isometric unbounded sine-theta
statements with all three gap configurations phrased through the genuine
Spectra spectrum.  It reuses the domain-aware residual identity, lower-frame
normalization, and exact-angle identification already present in the canonical
unbounded development.

No continuation, graph-selection, Riccati, Section 8, aggregate, or public
facade file is imported or modified here.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

universe v

variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Generalized complementary-block theorem with a genuine all-gap spectral
hypothesis. -/
theorem generalizedSinTheta_unbounded_of_genuineSpectrumGap
    (N : UnitaryInvariantIdealFamily (𝕜 := ℂ))
    (D : UnboundedSinThetaData (𝕜 := ℂ) (E := E) (F := F) (G := G))
    (hA : D.A.IsSelfAdjoint)
    (hA₀ : D.A₀.IsSelfAdjoint)
    (hΛ₁ : D.Λ₁.IsSelfAdjoint)
    (hF₁ : IsometricEmbedding D.F₁)
    {δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε)
    (hframe : LowerFrameBound D.X ε)
    (hgap : GenuineUnboundedSylvesterGap D.A₀ D.Λ₁ δ)
    (hR : N.Mem D.residual) :
    N.Mem
        (sinThetaBlock D.X D.F₁ hframe hε) ∧
      δ * ε * N.gauge
          (sinThetaBlock D.X D.F₁ hframe hε)
        ≤ N.gauge D.residual := by
  have hEq := unbounded_adjoint_residual_block_identity D hA hA₀ hΛ₁
  have hC := adjointResidualBlock_mem_and_gauge_le N.toRectangularSymmetricIdealFamily D hF₁ hR
  have hRaw := davisKahan1970_sylvester_of_genuineSpectrumGap
    N hA₀ hΛ₁ hδ hgap hEq hC.1
  have hFrame := lowerFrame_sinThetaBlock_mem_and_gauge_le
    N.toRectangularSymmetricIdealFamily D.X D.F₁ hframe hε hRaw.1
  refine ⟨hFrame.1, ?_⟩
  calc
    δ * ε * N.gauge (sinThetaBlock D.X D.F₁ hframe hε)
        = δ * (ε * N.gauge (sinThetaBlock D.X D.F₁ hframe hε)) := by ring
    _ ≤ δ * N.gauge (D.X.adjoint ∘L D.F₁) :=
      mul_le_mul_of_nonneg_left hFrame.2 hδ.le
    _ ≤ N.gauge (-(D.residual.adjoint ∘L D.F₁)) := hRaw.2
    _ ≤ N.gauge D.residual := hC.2

/-- Exact directed-angle form of the genuine all-gap generalized theorem. -/
theorem generalizedSinTheta_unbounded_exact_of_genuineSpectrumGap
    (N : UnitaryInvariantIdealFamily (𝕜 := ℂ))
    (D : UnboundedSinThetaData (𝕜 := ℂ) (E := E) (F := F) (G := G))
    (F₀ : H →L[ℂ] E)
    (hA : D.A.IsSelfAdjoint)
    (hA₀ : D.A₀.IsSelfAdjoint)
    (hΛ₁ : D.Λ₁.IsSelfAdjoint)
    (hdecomp : OrthogonalExactDecomposition F₀ D.F₁)
    {δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε)
    (hframe : LowerFrameBound D.X ε)
    (hgap : GenuineUnboundedSylvesterGap D.A₀ D.Λ₁ δ)
    (hR : N.Mem D.residual) :
    N.Mem
        (directedSinThetaOperator D.X F₀ hframe hε) ∧
      δ * ε * N.gauge
          (directedSinThetaOperator D.X F₀ hframe hε)
        ≤ N.gauge D.residual := by
  have hBlock := generalizedSinTheta_unbounded_of_genuineSpectrumGap
    N D hA hA₀ hΛ₁ hdecomp.isometry₁ hδ hε hframe hgap hR
  have hAngle := sinThetaBlock_mem_and_gauge_eq_directedSinThetaOperator
    N.toRectangularSymmetricIdealFamily D.X F₀ D.F₁ hframe hε hdecomp hBlock.1
  refine ⟨hAngle.1, ?_⟩
  simp only [KyFanDominantIdealFamily.gauge]
  rw [hAngle.2]
  exact hBlock.2

/-- Exact isometric specialization of the genuine all-gap theorem. -/
theorem sinTheta_unbounded_exact_of_genuineSpectrumGap
    (N : UnitaryInvariantIdealFamily (𝕜 := ℂ))
    (D : UnboundedSinThetaData (𝕜 := ℂ) (E := E) (F := F) (G := G))
    (F₀ : H →L[ℂ] E)
    (hA : D.A.IsSelfAdjoint)
    (hA₀ : D.A₀.IsSelfAdjoint)
    (hΛ₁ : D.Λ₁.IsSelfAdjoint)
    (hX : IsometricEmbedding D.X)
    (hdecomp : OrthogonalExactDecomposition F₀ D.F₁)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : GenuineUnboundedSylvesterGap D.A₀ D.Λ₁ δ)
    (hR : N.Mem D.residual) :
    N.Mem
        ((ContinuousLinearMap.id ℂ E - F₀ ∘L F₀.adjoint) ∘L D.X) ∧
      δ * N.gauge
          ((ContinuousLinearMap.id ℂ E - F₀ ∘L F₀.adjoint) ∘L D.X)
        ≤ N.gauge D.residual := by
  have hEq := unbounded_adjoint_residual_block_identity D hA hA₀ hΛ₁
  have hC := adjointResidualBlock_mem_and_gauge_le N.toRectangularSymmetricIdealFamily D hdecomp.isometry₁ hR
  have hRaw := davisKahan1970_sylvester_of_genuineSpectrumGap
    N hA₀ hΛ₁ hδ hgap hEq hC.1
  have hAngle := isometricComplementaryBlock_mem_and_gauge_eq_directed
    N.toRectangularSymmetricIdealFamily D.X F₀ D.F₁ hX hdecomp hRaw.1
  refine ⟨hAngle.1, ?_⟩
  simp only [KyFanDominantIdealFamily.gauge]
  rw [hAngle.2]
  exact hRaw.2.trans hC.2

/-- Complete source-shaped input package for the generalized genuine all-gap
theorem. -/
structure GenuineGeneralSinThetaProblem
    (N : UnitaryInvariantIdealFamily (𝕜 := ℂ)) where
  data : UnboundedSinThetaData (𝕜 := ℂ) (E := E) (F := F) (G := G)
  exactMap : H →L[ℂ] E
  ambient_selfAdjoint : data.A.IsSelfAdjoint
  trial_selfAdjoint : data.A₀.IsSelfAdjoint
  complement_selfAdjoint : data.Λ₁.IsSelfAdjoint
  exact_decomposition : OrthogonalExactDecomposition exactMap data.F₁
  gap : ℝ
  frameLowerBound : ℝ
  gap_pos : 0 < gap
  frameLowerBound_pos : 0 < frameLowerBound
  lowerFrame : LowerFrameBound data.X frameLowerBound
  spectral_gap : GenuineUnboundedSylvesterGap data.A₀ data.Λ₁ gap
  residual_mem : N.Mem data.residual

namespace GenuineGeneralSinThetaProblem

/-- Source-shaped generalized genuine all-gap endpoint. -/
theorem result
    (N : UnitaryInvariantIdealFamily (𝕜 := ℂ))
    (P : GenuineGeneralSinThetaProblem (E := E) (F := F)
      (G := G) (H := H) N) :
    N.Mem
        (directedSinThetaOperator P.data.X P.exactMap
          P.lowerFrame P.frameLowerBound_pos) ∧
      P.gap * P.frameLowerBound *
          N.gauge
            (directedSinThetaOperator P.data.X P.exactMap
              P.lowerFrame P.frameLowerBound_pos)
        ≤ N.gauge P.data.residual :=
  generalizedSinTheta_unbounded_exact_of_genuineSpectrumGap
    N P.data P.exactMap P.ambient_selfAdjoint P.trial_selfAdjoint
      P.complement_selfAdjoint P.exact_decomposition P.gap_pos
      P.frameLowerBound_pos P.lowerFrame P.spectral_gap P.residual_mem

end GenuineGeneralSinThetaProblem

/-- Complete source-shaped input package for the isometric genuine all-gap
theorem. -/
structure GenuineIsometricSinThetaProblem
    (N : UnitaryInvariantIdealFamily (𝕜 := ℂ)) where
  data : UnboundedSinThetaData (𝕜 := ℂ) (E := E) (F := F) (G := G)
  exactMap : H →L[ℂ] E
  ambient_selfAdjoint : data.A.IsSelfAdjoint
  trial_selfAdjoint : data.A₀.IsSelfAdjoint
  complement_selfAdjoint : data.Λ₁.IsSelfAdjoint
  trial_isometry : IsometricEmbedding data.X
  exact_decomposition : OrthogonalExactDecomposition exactMap data.F₁
  gap : ℝ
  gap_pos : 0 < gap
  spectral_gap : GenuineUnboundedSylvesterGap data.A₀ data.Λ₁ gap
  residual_mem : N.Mem data.residual

namespace GenuineIsometricSinThetaProblem

/-- Source-shaped isometric genuine all-gap endpoint. -/
theorem result
    (N : UnitaryInvariantIdealFamily (𝕜 := ℂ))
    (P : GenuineIsometricSinThetaProblem (E := E) (F := F)
      (G := G) (H := H) N) :
    N.Mem
        ((ContinuousLinearMap.id ℂ E -
          P.exactMap ∘L P.exactMap.adjoint) ∘L P.data.X) ∧
      P.gap * N.gauge
          ((ContinuousLinearMap.id ℂ E -
            P.exactMap ∘L P.exactMap.adjoint) ∘L P.data.X)
        ≤ N.gauge P.data.residual :=
  sinTheta_unbounded_exact_of_genuineSpectrumGap
    N P.data P.exactMap P.ambient_selfAdjoint P.trial_selfAdjoint
      P.complement_selfAdjoint P.trial_isometry P.exact_decomposition
      P.gap_pos P.spectral_gap P.residual_mem

end GenuineIsometricSinThetaProblem

end ExactSinTheta
end Experimental
end DavisKahan
end TauCeti
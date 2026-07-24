/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.SinTheta.Unbounded.Core
import DavisKahan.Sylvester.Unbounded.IntervalExterior

/-!
# Source-shaped finite-interval unbounded sine-theta theorem

This module assembles the domain-aware residual identity, the genuine-spectrum
interval/exterior Sylvester estimate, lower-frame normalization, and exact-angle
identification.  It deliberately bypasses the older abstract unbounded spectral
facade, whose ordered half-line branch still depends on spectral-cutoff work.
-/

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open scoped InnerProductSpace

universe v

variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Genuine Spectra interval/exterior separation for two self-adjoint closed
operators.  Either orientation is permitted. -/
def GenuineUnboundedIntervalExteriorGap
    (A : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := F))
    (B : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := G))
    (β α δ : ℝ) : Prop :=
  (Spectra.Resolvent.spectrum A.toLinearPMap ⊆ Set.Icc β α ∧
    ∀ lam ∈ Set.Ioo (β - δ) (α + δ),
      lam ∉ Spectra.Resolvent.spectrum B.toLinearPMap) ∨
  (Spectra.Resolvent.spectrum B.toLinearPMap ⊆ Set.Icc β α ∧
    ∀ lam ∈ Set.Ioo (β - δ) (α + δ),
      lam ∉ Spectra.Resolvent.spectrum A.toLinearPMap)

/-- Generalized finite-interval unbounded sine-theta theorem at ideal-gauge
scope, using genuine Spectra hypotheses and no ordered half-line dependency. -/
theorem generalizedSinTheta_unbounded_of_genuineIntervalExteriorGap
    (N : RectangularSymmetricIdealFamily (𝕜 := ℂ))
    (D : UnboundedSinThetaData (𝕜 := ℂ) (E := E) (F := F) (G := G))
    (hA : D.A.IsSelfAdjoint)
    (hA₀ : D.A₀.IsSelfAdjoint)
    (hΛ₁ : D.Λ₁.IsSelfAdjoint)
    (hF₁ : IsometricEmbedding D.F₁)
    {β α δ ε : ℝ}
    (hβα : β ≤ α) (hδ : 0 < δ) (hε : 0 < ε)
    (hframe : LowerFrameBound D.X ε)
    (hgap : GenuineUnboundedIntervalExteriorGap D.A₀ D.Λ₁ β α δ)
    (hR : N.Mem D.residual) :
    N.Mem (sinThetaBlock D.X D.F₁ hframe hε) ∧
      δ * ε * N.gauge (sinThetaBlock D.X D.F₁ hframe hε)
        ≤ N.gauge D.residual := by
  have hEq := unbounded_adjoint_residual_block_identity D hA hA₀ hΛ₁
  have hC := adjointResidualBlock_mem_and_gauge_le N D hF₁ hR
  have hRaw : N.Mem (D.X.adjoint ∘L D.F₁) ∧
      δ * N.gauge (D.X.adjoint ∘L D.F₁) ≤
        N.gauge (-(D.residual.adjoint ∘L D.F₁)) := by
    rcases hgap with hgap | hgap
    · exact SpectraBridge.unbounded_sylvester_mem_and_gauge_le_of_spectra_intervalLeft_exteriorRight
        N hA₀ hΛ₁ hβα hδ hgap.1 hgap.2 hEq hC.1
    · exact SpectraBridge.unbounded_sylvester_mem_and_gauge_le_of_spectra_exteriorLeft_intervalRight
        N hA₀ hΛ₁ hβα hδ hgap.2 hgap.1 hEq hC.1
  have hFrame := lowerFrame_sinThetaBlock_mem_and_gauge_le
    N D.X D.F₁ hframe hε hRaw.1
  refine ⟨hFrame.1, ?_⟩
  calc
    δ * ε * N.gauge (sinThetaBlock D.X D.F₁ hframe hε)
        = δ * (ε * N.gauge (sinThetaBlock D.X D.F₁ hframe hε)) := by ring
    _ ≤ δ * N.gauge (D.X.adjoint ∘L D.F₁) :=
      mul_le_mul_of_nonneg_left hFrame.2 hδ.le
    _ ≤ N.gauge (-(D.residual.adjoint ∘L D.F₁)) := hRaw.2
    _ ≤ N.gauge D.residual := hC.2

/-- Exact directed-angle form of the genuine-spectrum finite-interval theorem. -/
theorem generalizedSinTheta_unbounded_exact_of_genuineIntervalExteriorGap
    (N : RectangularSymmetricIdealFamily (𝕜 := ℂ))
    (D : UnboundedSinThetaData (𝕜 := ℂ) (E := E) (F := F) (G := G))
    (F₀ : H →L[ℂ] E)
    (hA : D.A.IsSelfAdjoint)
    (hA₀ : D.A₀.IsSelfAdjoint)
    (hΛ₁ : D.Λ₁.IsSelfAdjoint)
    (hdecomp : OrthogonalExactDecomposition F₀ D.F₁)
    {β α δ ε : ℝ}
    (hβα : β ≤ α) (hδ : 0 < δ) (hε : 0 < ε)
    (hframe : LowerFrameBound D.X ε)
    (hgap : GenuineUnboundedIntervalExteriorGap D.A₀ D.Λ₁ β α δ)
    (hR : N.Mem D.residual) :
    N.Mem (directedSinThetaOperator D.X F₀ hframe hε) ∧
      δ * ε * N.gauge (directedSinThetaOperator D.X F₀ hframe hε)
        ≤ N.gauge D.residual := by
  have hBlock := generalizedSinTheta_unbounded_of_genuineIntervalExteriorGap
    N D hA hA₀ hΛ₁ hdecomp.isometry₁ hβα hδ hε hframe hgap hR
  have hAngle := sinThetaBlock_mem_and_gauge_eq_directedSinThetaOperator
    N D.X F₀ D.F₁ hframe hε hdecomp hBlock.1
  refine ⟨hAngle.1, ?_⟩
  rw [hAngle.2]
  exact hBlock.2

/-- Exact isometric specialization of the genuine-spectrum finite-interval
unbounded theorem. -/
theorem sinTheta_unbounded_exact_of_genuineIntervalExteriorGap
    (N : RectangularSymmetricIdealFamily (𝕜 := ℂ))
    (D : UnboundedSinThetaData (𝕜 := ℂ) (E := E) (F := F) (G := G))
    (F₀ : H →L[ℂ] E)
    (hA : D.A.IsSelfAdjoint)
    (hA₀ : D.A₀.IsSelfAdjoint)
    (hΛ₁ : D.Λ₁.IsSelfAdjoint)
    (hX : IsometricEmbedding D.X)
    (hdecomp : OrthogonalExactDecomposition F₀ D.F₁)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hgap : GenuineUnboundedIntervalExteriorGap D.A₀ D.Λ₁ β α δ)
    (hR : N.Mem D.residual) :
    N.Mem ((ContinuousLinearMap.id ℂ E - F₀ ∘L F₀.adjoint) ∘L D.X) ∧
      δ * N.gauge
        ((ContinuousLinearMap.id ℂ E - F₀ ∘L F₀.adjoint) ∘L D.X)
        ≤ N.gauge D.residual := by
  have hEq := unbounded_adjoint_residual_block_identity D hA hA₀ hΛ₁
  have hC := adjointResidualBlock_mem_and_gauge_le N D hdecomp.isometry₁ hR
  have hBlock : N.Mem (D.X.adjoint ∘L D.F₁) ∧
      δ * N.gauge (D.X.adjoint ∘L D.F₁) ≤ N.gauge D.residual := by
    have hRaw : N.Mem (D.X.adjoint ∘L D.F₁) ∧
        δ * N.gauge (D.X.adjoint ∘L D.F₁) ≤
          N.gauge (-(D.residual.adjoint ∘L D.F₁)) := by
      rcases hgap with hgap | hgap
      · exact SpectraBridge.unbounded_sylvester_mem_and_gauge_le_of_spectra_intervalLeft_exteriorRight
          N hA₀ hΛ₁ hβα hδ hgap.1 hgap.2 hEq hC.1
      · exact SpectraBridge.unbounded_sylvester_mem_and_gauge_le_of_spectra_exteriorLeft_intervalRight
          N hA₀ hΛ₁ hβα hδ hgap.2 hgap.1 hEq hC.1
    exact ⟨hRaw.1, hRaw.2.trans hC.2⟩
  have hAngle := isometricComplementaryBlock_mem_and_gauge_eq_directed
    N D.X F₀ D.F₁ hX hdecomp hBlock.1
  refine ⟨hAngle.1, ?_⟩
  rw [hAngle.2]
  exact hBlock.2

end ExactSinTheta
end Experimental
end DavisKahan
end TauCeti
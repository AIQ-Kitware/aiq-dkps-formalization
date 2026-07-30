/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
import DavisKahan.SpectralTheory.GapResolvent
import DavisKahan.OperatorIdeal.CanonicalRealView
import DavisKahan.SinTheta.Unbounded.GenuineGauge
import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent

/-!
# `sin Θ` endpoints from a spectrum gap

The resolvent construction lives in `DavisKahan.SpectralTheory.GapResolvent`;
these are the two `sin Θ` endpoints it feeds, in operator norm and in an
arbitrary unitarily invariant ideal gauge.  Both are Spectra-free since
2026-07-28 — the gap resolvent is now built from
`TauCeti.LinearPMap.exists_norm_le_two_sided_shifted_inverse_of_spectrum_gap`.
-/

namespace TauCeti
namespace DavisKahan
namespace Experimental

section SinTheta

open TauCeti.DavisKahan.Experimental.ExactSinTheta

universe v

variable {E F G : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- **The unbounded Davis--Kahan `sin Θ` theorem with genuine spectra.**  For
the paper-shaped unbounded data, if the quadratic form of the trial block
`A₀` lies in `[β, α]` and the Spectra resolvent-set spectrum of the
complementary block `Λ₁` avoids the open interval `(β - δ, α + δ)`, then
`δ ‖X⋆ ∘ F₁‖ ≤ ‖R⋆ ∘ F₁‖`.  The resolvent hypothesis of
`sinTheta_unbounded_opNorm` is discharged by the unbounded spectral theorem
from the Spectra library. -/
theorem sinTheta_unbounded_opNorm_of_spectrum_gap
    (D : UnboundedSinThetaData (𝕜 := ℂ) (E := E) (F := F) (G := G))
    (hA : D.A.IsSelfAdjoint) (hA₀ : D.A₀.IsSelfAdjoint)
    (hΛ₁ : D.Λ₁.IsSelfAdjoint)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hA₀low : SemiboundedBelow D.A₀ β) (hA₀high : SemiboundedAbove D.A₀ α)
    (hΛspec : ∀ lam ∈ Set.Ioo (β - δ) (α + δ),
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum D.Λ₁.toLinearPMap) :
    δ * ‖D.X.adjoint ∘L D.F₁‖ ≤ ‖D.residual.adjoint ∘L D.F₁‖ := by
  have hΛsa : IsSelfAdjoint D.Λ₁.toLinearPMap :=
    LinearPMap.isSelfAdjoint_def.mpr
      ((D.Λ₁.isSelfAdjoint_iff_toLinearPMap_adjoint_eq).mp hΛ₁)
  refine sinTheta_unbounded_opNorm D hA hA₀ hΛ₁ hβα hδ hA₀low hA₀high ?_
  refine twoSidedShiftedInverseBound_of_spectrum_gap hΛsa (by linarith) ?_
  intro lam hlam
  refine hΛspec lam ?_
  rw [Set.mem_Ioo] at hlam ⊢
  exact ⟨by linarith [hlam.1], by linarith [hlam.2]⟩

/-- Raw partial-map operator-norm sine-theta endpoint with the Spectra
resolvent-set gap discharge. -/
theorem linearPMap_sinTheta_unbounded_opNorm_of_spectrum_gap
    (D : UnboundedSinThetaDataPMap (𝕜 := ℂ) (E := E) (F := F) (G := G))
    (hA : _root_.IsSelfAdjoint D.A) (hA₀ : _root_.IsSelfAdjoint D.A₀)
    (hΛ₁ : _root_.IsSelfAdjoint D.Λ₁)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hA₀low : TauCeti.LinearPMap.SemiboundedBelow D.A₀ β)
    (hA₀high : TauCeti.LinearPMap.SemiboundedAbove D.A₀ α)
    (hΛspec : ∀ lam ∈ Set.Ioo (β - δ) (α + δ),
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum D.Λ₁) :
    δ * ‖D.X.adjoint ∘L D.F₁‖ ≤ ‖D.residual.adjoint ∘L D.F₁‖ := by
  have hΛsa : _root_.IsSelfAdjoint D.toClosed.Λ₁.toLinearPMap := by
    simpa only [UnboundedSinThetaDataPMap.toClosed,
      DavisKahanExt.ClosedOperator.ofLinearPMap_toLinearPMap] using hΛ₁
  refine linearPMap_sinTheta_unbounded_opNorm
    D hA hA₀ hΛ₁ hβα hδ hA₀low hA₀high ?_
  have hShift := twoSidedShiftedInverseBound_of_spectrum_gap
    (c := (α + β) / 2) (s := (α - β) / 2 + δ) hΛsa (by linarith) (by
    intro lam hlam
    refine hΛspec lam ?_
    rw [Set.mem_Ioo] at hlam ⊢
    exact ⟨by linarith [hlam.1], by linarith [hlam.2]⟩)
  change LinearPMap.TwoSidedShiftedInverseBound D.toClosed.Λ₁.toLinearPMap
    ((α + β) / 2) ((α - β) / 2 + δ) at hShift
  have hΛmap : D.toClosed.Λ₁.toLinearPMap = D.Λ₁ := rfl
  rwa [hΛmap] at hShift

/-- **The unbounded Davis--Kahan `sin Θ` theorem at unitary-invariant ideal
scope, with genuine spectra.**  Combines the ideal-gauge endpoint
`sinTheta_unbounded_gauge` with the spectral-theorem discharge of the
resolvent hypothesis: the only spectral inputs are the trial block's form
bounds and Spectra resolvent-set spectrum avoidance for the complementary
block. -/
theorem sinTheta_unbounded_gauge_of_spectrum_gap
    (N : TauCeti.SymmetricOperatorIdealFamily.{0, v} ℂ)
    [N.toOperatorIdealFamily.IsComplete]
    (D : UnboundedSinThetaData (𝕜 := ℂ) (E := E) (F := F) (G := G))
    (hA : D.A.IsSelfAdjoint) (hA₀ : D.A₀.IsSelfAdjoint)
    (hΛ₁ : D.Λ₁.IsSelfAdjoint)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hA₀low : SemiboundedBelow D.A₀ β) (hA₀high : SemiboundedAbove D.A₀ α)
    (hΛspec : ∀ lam ∈ Set.Ioo (β - δ) (α + δ),
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum D.Λ₁.toLinearPMap)
    (hC : N.Mem (D.residual.adjoint ∘L D.F₁)) :
    N.Mem (D.X.adjoint ∘L D.F₁) ∧
      δ * N.gaugeReal (D.X.adjoint ∘L D.F₁) ≤
        N.gaugeReal (D.residual.adjoint ∘L D.F₁) := by
  have hΛsa : IsSelfAdjoint D.Λ₁.toLinearPMap :=
    LinearPMap.isSelfAdjoint_def.mpr
      ((D.Λ₁.isSelfAdjoint_iff_toLinearPMap_adjoint_eq).mp hΛ₁)
  refine sinTheta_unbounded_gauge N D hA hA₀ hΛ₁ hβα hδ hA₀low hA₀high
    ?_ hC
  refine twoSidedShiftedInverseBound_of_spectrum_gap hΛsa (by linarith) ?_
  intro lam hlam
  refine hΛspec lam ?_
  rw [Set.mem_Ioo] at hlam ⊢
  exact ⟨by linarith [hlam.1], by linarith [hlam.2]⟩

/-- Raw partial-map ideal-gauge sine-theta endpoint with the Spectra
resolvent-set gap discharge. -/
theorem linearPMap_sinTheta_unbounded_gauge_of_spectrum_gap
    (N : TauCeti.SymmetricOperatorIdealFamily.{0, v} ℂ)
    [N.toOperatorIdealFamily.IsComplete]
    (D : UnboundedSinThetaDataPMap (𝕜 := ℂ) (E := E) (F := F) (G := G))
    (hA : _root_.IsSelfAdjoint D.A) (hA₀ : _root_.IsSelfAdjoint D.A₀)
    (hΛ₁ : _root_.IsSelfAdjoint D.Λ₁)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hA₀low : TauCeti.LinearPMap.SemiboundedBelow D.A₀ β)
    (hA₀high : TauCeti.LinearPMap.SemiboundedAbove D.A₀ α)
    (hΛspec : ∀ lam ∈ Set.Ioo (β - δ) (α + δ),
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum D.Λ₁)
    (hC : N.Mem (D.residual.adjoint ∘L D.F₁)) :
    N.Mem (D.X.adjoint ∘L D.F₁) ∧
      δ * N.gaugeReal (D.X.adjoint ∘L D.F₁) ≤
        N.gaugeReal (D.residual.adjoint ∘L D.F₁) := by
  have hΛsa : _root_.IsSelfAdjoint D.toClosed.Λ₁.toLinearPMap := by
    simpa only [UnboundedSinThetaDataPMap.toClosed,
      DavisKahanExt.ClosedOperator.ofLinearPMap_toLinearPMap] using hΛ₁
  refine linearPMap_sinTheta_unbounded_gauge
    N D hA hA₀ hΛ₁ hβα hδ hA₀low hA₀high ?_ hC
  have hShift := twoSidedShiftedInverseBound_of_spectrum_gap
    (c := (α + β) / 2) (s := (α - β) / 2 + δ) hΛsa (by linarith) (by
    intro lam hlam
    refine hΛspec lam ?_
    rw [Set.mem_Ioo] at hlam ⊢
    exact ⟨by linarith [hlam.1], by linarith [hlam.2]⟩)
  change LinearPMap.TwoSidedShiftedInverseBound D.toClosed.Λ₁.toLinearPMap
    ((α + β) / 2) ((α - β) / 2 + δ) at hShift
  have hΛmap : D.toClosed.Λ₁.toLinearPMap = D.Λ₁ := rfl
  rwa [hΛmap] at hShift

end SinTheta


end Experimental
end DavisKahan
end TauCeti

/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
import DavisKahan.Interop.Spectra.GapResolvent
import DavisKahan.SinTheta.Unbounded.GenuineGauge

/-!
# `sin Θ` endpoints from a Spectra spectrum gap

The resolvent construction lives in `DavisKahan.Interop.Spectra.GapResolvent`;
these are the two `sin Θ` endpoints it feeds, in operator norm and in an
arbitrary unitarily invariant ideal gauge.
-/

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace SpectraBridge

open Spectra.QuantumMechanics.SpectralTheory

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
      lam ∉ Spectra.Resolvent.spectrum D.Λ₁.toLinearPMap) :
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

/-- **The unbounded Davis--Kahan `sin Θ` theorem at unitary-invariant ideal
scope, with genuine spectra.**  Combines the ideal-gauge endpoint
`sinTheta_unbounded_gauge` with the spectral-theorem discharge of the
resolvent hypothesis: the only spectral inputs are the trial block's form
bounds and Spectra resolvent-set spectrum avoidance for the complementary
block. -/
theorem sinTheta_unbounded_gauge_of_spectrum_gap
    (N : RectangularSymmetricIdealFamily (𝕜 := ℂ))
    (D : UnboundedSinThetaData (𝕜 := ℂ) (E := E) (F := F) (G := G))
    (hA : D.A.IsSelfAdjoint) (hA₀ : D.A₀.IsSelfAdjoint)
    (hΛ₁ : D.Λ₁.IsSelfAdjoint)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hA₀low : SemiboundedBelow D.A₀ β) (hA₀high : SemiboundedAbove D.A₀ α)
    (hΛspec : ∀ lam ∈ Set.Ioo (β - δ) (α + δ),
      lam ∉ Spectra.Resolvent.spectrum D.Λ₁.toLinearPMap)
    (hC : N.Mem (D.residual.adjoint ∘L D.F₁)) :
    N.Mem (D.X.adjoint ∘L D.F₁) ∧
      δ * N.gauge (D.X.adjoint ∘L D.F₁) ≤
        N.gauge (D.residual.adjoint ∘L D.F₁) := by
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

end SinTheta


end SpectraBridge
end Experimental
end DavisKahan
end TauCeti
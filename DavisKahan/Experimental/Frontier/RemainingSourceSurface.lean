/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.Experimental.Frontier.Lemma63
import DavisKahan.DoubleAngle.UnboundedIdeal
import DavisKahan.TanTwoTheta.UnboundedIdeal
import DavisKahan.TanTheta.GenuineSpectrum
import DavisKahan.OperatorIdeal.UnitarilyInvariant.RectangularFamily

/-!
# Remaining source-level endpoint signatures

This module records the principal paper-facing statements that still lack an
exact source wrapper or a proof at the full Hilbert-space norm-ideal scope.
They are kept outside the supported source facade until their hypotheses and
conclusions are compiler-certified and audited against the paper.
-/

open scoped InnerProductSpace
open Set

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace Frontier
namespace RemainingSourceSurface

open ExactSinTheta
open SpectraBridge
open DavisKahanExt

universe u v

section BanachSylvester

variable {X : Type u} {Y : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-- A norm on cross-space bounded operators compatible with contractions on
both sides, as required in Davis--Kahan Theorem 5.1. -/
structure CompatibleCrossOperatorNorm where
  toFun : (X →L[ℂ] Y) → ℝ
  nonneg : ∀ T, 0 ≤ toFun T
  eq_zero : ∀ T, toFun T = 0 → T = 0
  smul : ∀ c : ℂ, ∀ T, toFun (c • T) = ‖c‖ * toFun T
  triangle : ∀ S T, toFun (S + T) ≤ toFun S + toFun T
  compatible : ∀ (L : Y →L[ℂ] Y) (T : X →L[ℂ] Y)
    (R : X →L[ℂ] X), ‖L‖ ≤ 1 → ‖R‖ ≤ 1 →
      toFun (L ∘L T ∘L R) ≤ toFun T

instance : CoeFun (CompatibleCrossOperatorNorm (X := X) (Y := Y))
    (fun _ => (X →L[ℂ] Y) → ℝ) :=
  ⟨CompatibleCrossOperatorNorm.toFun⟩

/-- Davis--Kahan 1970, Theorem 5.1, exact Banach-space compatible-norm
statement. -/
theorem theorem5_1_banach_sylvester
    (N : CompatibleCrossOperatorNorm (X := X) (Y := Y))
    (A : Y →L[ℂ] Y) (B : X →L[ℂ] X)
    (T C : X →L[ℂ] Y) {gamma delta : ℝ}
    (hgamma : 0 ≤ gamma) (hdelta : 0 < delta)
    (hB : ‖B‖ ≤ gamma)
    (hA : ∀ y : Y, (gamma + delta) * ‖y‖ ≤ ‖A y‖)
    (hEq : A ∘L T - T ∘L B = C) :
    delta * N T ≤ N C := by
  sorry

end BanachSylvester

section GeneralizedTangent

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Residual operator of a trial subspace for a bounded self-adjoint operator. -/
noncomputable def trialResidual
    (T : H →L[ℂ] H) (Z : Submodule ℂ H)
    [Z.HasOrthogonalProjection] : Z →L[ℂ] H := by
  sorry

/-- Davis--Kahan 1970, Theorem 6.3 at Hilbert-space rectangular-ideal scope.
The dimension hypothesis is expressed by an isometric embedding of the trial
space into the selected exact space, rather than finite rank. -/
theorem theorem6_3_generalizedTanTheta_ideal
    (N : RectangularSymmetricIdealFamily (𝕜 := ℂ))
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T)
    (Z V : Submodule ℂ H) [Z.HasOrthogonalProjection]
    [V.HasOrthogonalProjection]
    (hdim : Nonempty (Z →ₗᵢ[ℂ] V))
    (hVinv : ∀ x ∈ V, T x ∈ V)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hZspec : ∀ x ∈ spectrum ℝ (compressOperator Z T), x ≤ alpha)
    (hVspec : ∀ x ∈ spectrum ℝ (compressOperator Vᗮ T),
      alpha + delta ≤ x)
    (hRmem : N.Mem (trialResidual T Z)) :
    ∃ hacute : IsAcute Z V,
      N.Mem (tanAngleOperatorC Z V hacute) ∧
      delta * N.gauge (tanAngleOperatorC Z V hacute) ≤
        N.gauge (trialResidual T Z) := by
  sorry

end GeneralizedTangent

section DoubleAngleSourceWrappers

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Source-numbered residual and perturbation form of the sine-double-angle
theorem at arbitrary rectangular ideal-gauge scope. -/
theorem section7_sinTwoTheta_source_ideal
    (N : RectangularSymmetricIdealFamily (𝕜 := ℂ))
    (A : DKClosedOperator (H := H)) (hA : A.IsSelfAdjoint)
    (E : H →L[ℂ] H) (hE : IsSelfAdjointOperator E)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {beta alpha delta : ℝ} (hba : beta ≤ alpha) (hdelta : 0 < delta)
    (hBlow : SemiboundedBelow
      (selfAdjointSpectralRestriction A hA B hB) beta)
    (hBhigh : SemiboundedAbove
      (selfAdjointSpectralRestriction A hA B hB) alpha)
    (hBcomplSpec : ∀ lam ∈ Set.Ioo (beta - delta) (alpha + delta),
      lam ∉ Spectra.Resolvent.spectrum
        (selfAdjointSpectralRestriction A hA Bᶜ hB.compl).toLinearPMap)
    (hEmem : N.Mem E) :
    N.Mem (sinTwoThetaIdealBlock
      (selfAdjointSpectralSubspace A hA B hB)
      (selfAdjointSpectralSubspace (A.addBounded E)
        (addBounded_isSelfAdjoint A hA E hE) S hS)) ∧
    delta * N.gauge (sinTwoThetaIdealBlock
      (selfAdjointSpectralSubspace A hA B hB)
      (selfAdjointSpectralSubspace (A.addBounded E)
        (addBounded_isSelfAdjoint A hA E hE) S hS)) ≤
      2 * N.gauge E := by
  sorry

/-- Source-numbered tangent-double-angle theorem after Section 8 selects the
strict quarter-acute branch. -/
theorem section7_tanTwoTheta_source_ideal
    (N : RectangularSymmetricIdealFamily (𝕜 := ℂ))
    (A : DKClosedOperator (H := H)) (hA : A.IsSelfAdjoint)
    (E : H →L[ℂ] H) (hE : IsSelfAdjointOperator E)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {beta alpha delta : ℝ} (hba : beta ≤ alpha) (hdelta : 0 < delta)
    (hBlow : SemiboundedBelow
      (selfAdjointSpectralRestriction A hA B hB) beta)
    (hBhigh : SemiboundedAbove
      (selfAdjointSpectralRestriction A hA B hB) alpha)
    (hBcomplSpec : ∀ lam ∈ Set.Ioo (beta - delta) (alpha + delta),
      lam ∉ Spectra.Resolvent.spectrum
        (selfAdjointSpectralRestriction A hA Bᶜ hB.compl).toLinearPMap)
    (hEmem : N.Mem E)
    (hquarter : IsQuarterAcute
      (selfAdjointSpectralSubspace A hA B hB)
      (selfAdjointSpectralSubspace (A.addBounded E)
        (addBounded_isSelfAdjoint A hA E hE) S hS)) :
    N.Mem (tanTwoThetaIdealBlock
      (selfAdjointSpectralSubspace A hA B hB)
      (selfAdjointSpectralSubspace (A.addBounded E)
        (addBounded_isSelfAdjoint A hA E hE) S hS) hquarter) ∧
    delta * N.gauge (tanTwoThetaIdealBlock
      (selfAdjointSpectralSubspace A hA B hB)
      (selfAdjointSpectralSubspace (A.addBounded E)
        (addBounded_isSelfAdjoint A hA E hE) S hS) hquarter) ≤
      2 * N.gauge E := by
  sorry

end DoubleAngleSourceWrappers

end RemainingSourceSurface
end Frontier
end Experimental
end DavisKahan
end ForMathlib

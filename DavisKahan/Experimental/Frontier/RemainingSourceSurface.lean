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

/-- An explicit bounded left inverse of `A` with a reciprocal norm bound.  On a
general Banach space a lower bound on `A` does not furnish a bounded projection
onto the (possibly non-complemented) range, so the reusable datum is the left
inverse itself; on a Hilbert space the spectral-separation lower bound supplies
it through the closed-range orthogonal projection. -/
structure BoundedLeftInverseData (A : Y →L[ℂ] Y) (c : ℝ) where
  leftInverse : Y →L[ℂ] Y
  comp_eq_id : leftInverse ∘L A = ContinuousLinearMap.id ℂ Y
  norm_le : ‖leftInverse‖ ≤ c

namespace CompatibleCrossOperatorNorm

/-- The compatible norm vanishes at the zero operator. -/
theorem map_zero (N : CompatibleCrossOperatorNorm (X := X) (Y := Y)) :
    N (0 : X →L[ℂ] Y) = 0 := by
  have h := N.smul 0 (0 : X →L[ℂ] Y)
  simpa using h

/-- Full two-sided ideal estimate obtained by normalizing the multipliers. -/
theorem comp_le_mul (N : CompatibleCrossOperatorNorm (X := X) (Y := Y))
    (L : Y →L[ℂ] Y) (T : X →L[ℂ] Y) (R : X →L[ℂ] X) :
    N (L ∘L T ∘L R) ≤ ‖L‖ * N T * ‖R‖ := by
  by_cases hL : L = 0
  · subst L; simp [map_zero N]
  by_cases hR : R = 0
  · subst R; simp [map_zero N]
  let Ln : Y →L[ℂ] Y := (‖L‖ : ℂ)⁻¹ • L
  let Rn : X →L[ℂ] X := (‖R‖ : ℂ)⁻¹ • R
  have hLnorm : ‖L‖ ≠ 0 := norm_ne_zero_iff.mpr hL
  have hRnorm : ‖R‖ ≠ 0 := norm_ne_zero_iff.mpr hR
  have hLcomplex : (‖L‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hLnorm
  have hRcomplex : (‖R‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hRnorm
  have hLn : ‖Ln‖ ≤ 1 := by
    change ‖(‖L‖ : ℂ)⁻¹ • L‖ ≤ 1
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg L), inv_mul_cancel₀ hLnorm]
  have hRn : ‖Rn‖ ≤ 1 := by
    change ‖(‖R‖ : ℂ)⁻¹ • R‖ ≤ 1
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg R), inv_mul_cancel₀ hRnorm]
  have hcompat := N.compatible Ln T Rn hLn hRn
  have hfactor :
      L ∘L T ∘L R = ((‖L‖ * ‖R‖ : ℝ) : ℂ) • (Ln ∘L T ∘L Rn) := by
    ext x
    simp [Ln, Rn, hLcomplex, hRcomplex, smul_smul,
      mul_assoc, mul_left_comm, mul_comm]
  rw [hfactor, N.smul]
  calc
    ‖((‖L‖ * ‖R‖ : ℝ) : ℂ)‖ * N (Ln ∘L T ∘L Rn)
        ≤ (‖L‖ * ‖R‖) * N T := by
          simpa using mul_le_mul_of_nonneg_left hcompat
            (mul_nonneg (norm_nonneg L) (norm_nonneg R))
    _ = ‖L‖ * N T * ‖R‖ := by ring

/-- One-sided left estimate. -/
theorem comp_left_le_mul (N : CompatibleCrossOperatorNorm (X := X) (Y := Y))
    (L : Y →L[ℂ] Y) (T : X →L[ℂ] Y) :
    N (L ∘L T) ≤ ‖L‖ * N T := by
  have h := comp_le_mul N L T (ContinuousLinearMap.id ℂ X)
  rw [ContinuousLinearMap.comp_id] at h
  calc
    N (L ∘L T) ≤ ‖L‖ * N T * ‖ContinuousLinearMap.id ℂ X‖ := h
    _ ≤ ‖L‖ * N T * 1 :=
      mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le
        (mul_nonneg (norm_nonneg L) (N.nonneg T))
    _ = ‖L‖ * N T := by ring

end CompatibleCrossOperatorNorm

/-- Davis--Kahan 1970, Theorem 5.1 at Banach compatible-norm scope, under the
corrected operator hypothesis.

The printed separation hypothesis `(gamma + delta) * ‖y‖ ≤ ‖A y‖` (i.e. `A`
bounded below) is insufficient on a general Banach space: it gives injectivity
and closed range but no bounded projection onto that range, hence no bounded left
inverse, and the elementary quotient argument breaks.  The faithful reusable
hypothesis is therefore an explicit bounded left inverse of `A` with reciprocal
norm bound `(gamma + delta)⁻¹`.  On a Hilbert space the bounded-below separation
supplies exactly this datum via the closed-range orthogonal projection (through
`lowerFramePolarData`), so this statement specializes to the paper's Hilbert
Theorem 5.1 there. -/
theorem theorem5_1_banach_sylvester
    (N : CompatibleCrossOperatorNorm (X := X) (Y := Y))
    (A : Y →L[ℂ] Y) (B : X →L[ℂ] X)
    (T C : X →L[ℂ] Y) {gamma delta : ℝ}
    (hgamma : 0 ≤ gamma) (hdelta : 0 < delta)
    (hB : ‖B‖ ≤ gamma)
    (hleft : BoundedLeftInverseData A (gamma + delta)⁻¹)
    (hEq : A ∘L T - T ∘L B = C) :
    delta * N T ≤ N C := by
  let L := hleft.leftInverse
  have hgd : 0 < gamma + delta := add_pos_of_nonneg_of_pos hgamma hdelta
  have hLT : T = L ∘L C + L ∘L T ∘L B := by
    have hcancel : L ∘L A = ContinuousLinearMap.id ℂ Y := hleft.comp_eq_id
    apply ContinuousLinearMap.ext
    intro x
    have heqpoint := congrArg (fun S : X →L[ℂ] Y => S x) hEq
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply] at heqpoint
    change T x = L (C x) + L (T (B x))
    have hLA : L (A (T x)) = T x := by
      have hp := congrArg (fun S : Y →L[ℂ] Y => S (T x)) hcancel
      simpa using hp
    rw [← heqpoint, map_sub, hLA]
    abel
  have htri : N T ≤ N (L ∘L C) + N (L ∘L T ∘L B) := by
    calc
      N T = N (L ∘L C + L ∘L T ∘L B) := congrArg N.toFun hLT
      _ ≤ N (L ∘L C) + N (L ∘L T ∘L B) := N.triangle _ _
  have hLC : N (L ∘L C) ≤ (gamma + delta)⁻¹ * N C :=
    (CompatibleCrossOperatorNorm.comp_left_le_mul N L C).trans
      (mul_le_mul_of_nonneg_right hleft.norm_le (N.nonneg C))
  have hLTB : N (L ∘L T ∘L B) ≤ (gamma + delta)⁻¹ * N T * gamma :=
    (CompatibleCrossOperatorNorm.comp_le_mul N L T B).trans
      (mul_le_mul
        (mul_le_mul_of_nonneg_right hleft.norm_le (N.nonneg T))
        hB (norm_nonneg B)
        (mul_nonneg (inv_nonneg.mpr hgd.le) (N.nonneg T)))
  have hsum : N T ≤ (gamma + delta)⁻¹ * N C +
      (gamma + delta)⁻¹ * N T * gamma :=
    htri.trans (add_le_add hLC hLTB)
  have hscaled := mul_le_mul_of_nonneg_left hsum hgd.le
  have hnormalize :
      (gamma + delta) *
          ((gamma + delta)⁻¹ * N C + (gamma + delta)⁻¹ * N T * gamma) =
        N C + N T * gamma := by
    calc
      (gamma + delta) *
          ((gamma + delta)⁻¹ * N C + (gamma + delta)⁻¹ * N T * gamma) =
          ((gamma + delta) * (gamma + delta)⁻¹) * N C +
            ((gamma + delta) * (gamma + delta)⁻¹) * N T * gamma := by ring
      _ = N C + N T * gamma := by
        rw [mul_inv_cancel₀ hgd.ne']; ring
  rw [hnormalize] at hscaled
  nlinarith

end BanachSylvester

section GeneralizedTangent

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Residual operator of a trial subspace for a bounded self-adjoint operator. -/
noncomputable def trialResidual
    (T : H →L[ℂ] H) (Z : Submodule ℂ H)
    [Z.HasOrthogonalProjection] : Z →L[ℂ] H :=
  Zᗮ.starProjection ∘L T ∘L Z.subtypeL

/-- Davis--Kahan 1970, Theorem 6.3 at Hilbert-space rectangular-ideal scope.
The dimension hypothesis is expressed by an isometric embedding of the trial
space into the selected exact space, rather than finite rank. -/
theorem theorem6_3_generalizedTanTheta_ideal
    (N : RectangularSymmetricIdealFamily (𝕜 := ℂ))
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T)
    -- `compressOperator Z T` needs the trial subspace to be a Hilbert space in
    -- its own right; the source's trial space is closed, so this is a
    -- faithful hypothesis rather than a restriction
    (Z V : Submodule ℂ H) [Z.HasOrthogonalProjection] [CompleteSpace Z]
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
  exact sinTwoTheta_addBounded_gauge_of_spectrum_gap
    N A hA E hE B S hB hS hba hdelta hBlow hBhigh hBcomplSpec hEmem

/-- Source-numbered tangent-double-angle theorem after Section 8 selects the
strict quarter-acute branch.

The bound carries the positive double-cosine denominator
`1 - 2 * directedGap ^ 2` (positive under the quarter-acute hypothesis).  This
factor is intrinsic to `tanTwoThetaIdealBlock = sinTwoThetaIdealBlock ∘L cos⁻¹`;
a bare `2 * N.gauge E` on the right is strictly stronger than the tangent
construction supports, so the denominator is a required part of the statement,
not an artifact. -/
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
      (2 * N.gauge E) /
        (1 - 2 * directedGap
          (selfAdjointSpectralSubspace A hA B hB)
          (selfAdjointSpectralSubspace (A.addBounded E)
            (addBounded_isSelfAdjoint A hA E hE) S hS) ^ 2) := by
  exact tanTwoTheta_addBounded_gauge_of_spectrum_gap
    N A hA E hE B S hB hS hba hdelta hBlow hBhigh hBcomplSpec hEmem hquarter

end DoubleAngleSourceWrappers

end RemainingSourceSurface
end Frontier
end Experimental
end DavisKahan
end ForMathlib

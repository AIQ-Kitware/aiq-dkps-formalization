/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.Geometry.Polar.NuclearRootClassification
public import TauCeti.Analysis.OperatorIdeal.OperatorNorm

/-!
# The nuclear optimizer parametrization preserves ideal distances

Pairwise differences of reconstructed transporters have exactly the
same symmetric ideal gauge as their signed-root parameter differences.
In particular the full parametrization is isometric in operator norm,
when actual unitaries are viewed as bounded operators.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- The literal reconstructed transporter coefficient is R times the
adjoint of its explicit relative coefficient. -/
theorem nuclearSignedSineTransport_coefficient
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L)
    (A : E →L[𝕜] E) (hA : IsSelfAdjoint A) (hmod : A.modulus = K.sinAngleOperator L)
    (hcomm : Commute A ((nuclearTransportDual K L D : E →L[𝕜] E) *
      Proposition35.section3CosAngleOperator K L)) :
    (nuclearSignedSineTransport K L D A hA hmod hcomm : E →L[𝕜] E) =
      nonacuteDirectRotation K L D * star (Proposition35.section3CosAngleOperator K L +
        (nuclearTransportDual K L D : E →L[𝕜] E) * A) := by
  rw [← nuclearSignedSineRelative_def K L D A hA hmod hcomm, LinearIsometryEquiv.star_eq_symm]
  ext x
  rfl

/-- **Exact preservation of every symmetric ideal distance.** Infinite
gauge values are included. The result is generic over either field and
requires neither trace class nor reflection oddness of the roots. -/
theorem nuclearSignedSineTransport_gauge_sub
    (Φ : SymmetricOperatorIdealFamily 𝕜)
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L)
    (A B : E →L[𝕜] E)
    (hA : IsSelfAdjoint A) (hAmod : A.modulus = K.sinAngleOperator L)
    (hAcomm : Commute A ((nuclearTransportDual K L D : E →L[𝕜] E) *
      Proposition35.section3CosAngleOperator K L))
    (hB : IsSelfAdjoint B) (hBmod : B.modulus = K.sinAngleOperator L)
    (hBcomm : Commute B ((nuclearTransportDual K L D : E →L[𝕜] E) *
      Proposition35.section3CosAngleOperator K L)) :
    Φ.gauge ((nuclearSignedSineTransport K L D A hA hAmod hAcomm : E →L[𝕜] E) -
      (nuclearSignedSineTransport K L D B hB hBmod hBcomm : E →L[𝕜] E)) = Φ.gauge (A - B) := by
  let Ψ := Φ.toOperatorIdealFamily
  let C := Proposition35.section3CosAngleOperator K L
  let V := nuclearTransportDual K L D
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L D, nonacuteDirectRotation_mem_unitary K L D⟩ : unitary (E →L[𝕜] E))
  have hfactor : (nuclearSignedSineTransport K L D A hA hAmod hAcomm : E →L[𝕜] E) -
      (nuclearSignedSineTransport K L D B hB hBmod hBcomm : E →L[𝕜] E) =
        (R : E →L[𝕜] E) * star ((V : E →L[𝕜] E) * (A - B)) := by
    rw [nuclearSignedSineTransport_coefficient, nuclearSignedSineTransport_coefficient]
    change (R : E →L[𝕜] E) * star (C + (V : E →L[𝕜] E) * A) -
      (R : E →L[𝕜] E) * star (C + (V : E →L[𝕜] E) * B) = _
    rw [← mul_sub, ← star_sub]
    congr 2
    rw [mul_sub]
    abel
  rw [hfactor]
  calc
    _ = Ψ.gauge (star ((V : E →L[𝕜] E) * (A - B))) :=
      Ψ.gauge_comp_linearIsometryEquiv_left _ R
    _ = Ψ.gauge ((V : E →L[𝕜] E) * (A - B)) := Φ.gauge_adjoint _
    _ = Ψ.gauge (A - B) := Ψ.gauge_comp_linearIsometryEquiv_left _ V

/-- The constructed family preserves operator-norm differences exactly. -/
theorem nuclearSignedSineTransport_norm_sub
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L)
    (A B : E →L[𝕜] E)
    (hA : IsSelfAdjoint A) (hAmod : A.modulus = K.sinAngleOperator L)
    (hAcomm : Commute A ((nuclearTransportDual K L D : E →L[𝕜] E) *
      Proposition35.section3CosAngleOperator K L))
    (hB : IsSelfAdjoint B) (hBmod : B.modulus = K.sinAngleOperator L)
    (hBcomm : Commute B ((nuclearTransportDual K L D : E →L[𝕜] E) *
      Proposition35.section3CosAngleOperator K L)) :
    ‖(nuclearSignedSineTransport K L D A hA hAmod hAcomm : E →L[𝕜] E) -
      (nuclearSignedSineTransport K L D B hB hBmod hBcomm : E →L[𝕜] E)‖ = ‖A - B‖ := by
  have h := nuclearSignedSineTransport_gauge_sub (SymmetricOperatorIdealFamily.opNorm 𝕜)
    K L D A B hA hAmod hAcomm hB hBmod hBcomm
  change (SymmetricOperatorIdealFamily.opNorm 𝕜).toOperatorIdealFamily.gauge _ =
    (SymmetricOperatorIdealFamily.opNorm 𝕜).toOperatorIdealFamily.gauge _ at h
  rw [SymmetricOperatorIdealFamily.opNorm_toOperatorIdealFamily] at h
  simp only [OperatorIdealFamily.gauge_opNorm] at h
  have ht := congrArg ENNReal.toReal h
  simpa only [toReal_enorm] using ht

section Complex

open scoped ENNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The complete nuclear optimizer parametrization is isometric when
actual transporters are viewed as bounded operators with operator norm. -/
theorem nuclearSignedSineEquivOptimizers_isometry_complex
    (K L : Submodule ℂ F) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hΔ : (K.starProjection - L.starProjection).nuclearENorm ≠ ∞) :
    Isometry (fun A : nuclearSignedSineParameters K L D =>
      ((nuclearSignedSineEquivOptimizers_complex K L D hΔ A).val : F →L[ℂ] F)) := by
  apply Isometry.of_dist_eq
  intro A B
  have hpA := (mem_nuclearSignedSineParameters K L D A.val).mp A.property
  have hpB := (mem_nuclearSignedSineParameters K L D B.val).mp B.property
  change dist ((nuclearSignedSineEquivOptimizers_complex K L D hΔ A).val : F →L[ℂ] F)
    ((nuclearSignedSineEquivOptimizers_complex K L D hΔ B).val : F →L[ℂ] F) = dist A.val B.val
  rw [dist_eq_norm, dist_eq_norm]
  change ‖(nuclearSignedSineTransport K L D A.val hpA.1 hpA.2.1 hpA.2.2.1 : F →L[ℂ] F) -
    (nuclearSignedSineTransport K L D B.val hpB.1 hpB.2.1 hpB.2.2.1 : F →L[ℂ] F)‖ = ‖A.val - B.val‖
  exact nuclearSignedSineTransport_norm_sub K L D A.val B.val hpA.1 hpA.2.1 hpA.2.2.1
    hpB.1 hpB.2.1 hpB.2.2.1

end Complex

end TauCeti.DavisKahan

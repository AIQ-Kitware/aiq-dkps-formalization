/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.Geometry.Polar.NuclearSignedRoot

/-!
# Constructing unitary transport from signed sine roots

The independent parameter is a self-adjoint operator with prescribed
sine modulus, commuting with the dual times cosine. The common-sector
conditions follow from its modulus, and zero cosine is retained.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan

attribute [local instance] _root_.ContinuousLinearMap.realAlgebra
  _root_.ContinuousLinearMap.realIsScalarTower

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- A signed sine root annihilates the full common sector on both
sides, preserves the cosine, and squares to the sine square. -/
theorem signed_sine_root_kernel_and_cosine
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L)
    (A : E →L[𝕜] E) (hA : IsSelfAdjoint A) (hmod : A.modulus = K.sinAngleOperator L) :
    let B := nonacuteDirectRotation K L D - Proposition35.section3CosAngleOperator K L
    let Q := B.ker.starProjection
    A * Q = 0 ∧ Q * A = 0 ∧ Commute A (Proposition35.section3CosAngleOperator K L) ∧
      A * A = K.sinAngleOperator L * K.sinAngleOperator L := by
  let B := nonacuteDirectRotation K L D - Proposition35.section3CosAngleOperator K L
  let Q := B.ker.starProjection
  have hBmod : B.modulus = K.sinAngleOperator L :=
    (Proposition35.modulus_nonacuteDirectRotation_sub_cosine K L D).trans
      (by rw [Proposition35.section3SinAngleOperator, Submodule.sinAngleOperator_def])
  have hker : A.ker = B.ker := by rw [← A.ker_modulus, hmod, ← hBmod, B.ker_modulus]
  have hAQ : A * Q = 0 := by
    ext x
    have hx := B.ker.starProjection_apply_mem x
    change Q x ∈ B.ker at hx
    rw [← hker] at hx
    exact hx
  have hQA : Q * A = 0 := by
    have hQ : IsSelfAdjoint Q := isSelfAdjoint_starProjection B.ker
    have h := congrArg star hAQ
    simpa only [star_mul, hA.star_eq, hQ.star_eq, star_zero] using h
  have hAS : Commute A (K.sinAngleOperator L) := by
    rw [← hmod]
    apply ContinuousLinearMap.commute_modulus_of_commute
    change Commute A (star A * A)
    rw [hA.star_eq]
    exact (Commute.refl A).mul_right (Commute.refl A)
  have hsq := A.modulus_comp_modulus
  change A.modulus * A.modulus = star A * A at hsq
  rw [hmod, hA.star_eq] at hsq
  exact ⟨hAQ, hQA,
    Proposition35.commute_section3CosAngleOperator_of_commute_sinAngleOperator K L A hAS, hsq.symm⟩

/-- Every self-adjoint sine root with the indicated commutation gives
an actual relative unitary. No compactness, trace-class or acuteness
assumption is needed; source preservation is handled separately. -/
theorem signed_sine_relative_mem_unitary
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L)
    (A : E →L[𝕜] E) (hA : IsSelfAdjoint A) (hmod : A.modulus = K.sinAngleOperator L)
    (hcomm : Commute A ((nuclearTransportDual K L D : E →L[𝕜] E) *
      Proposition35.section3CosAngleOperator K L)) :
    Proposition35.section3CosAngleOperator K L + (nuclearTransportDual K L D : E →L[𝕜] E) * A ∈
      unitary (E →L[𝕜] E) := by
  let C := Proposition35.section3CosAngleOperator K L
  let S := K.sinAngleOperator L
  let V := nuclearTransportDual K L D
  let B := nonacuteDirectRotation K L D - C
  let Q := B.ker.starProjection
  let G := star (V : E →L[𝕜] E) * C
  obtain ⟨hAQ, hQA, hAC, hsq⟩ := signed_sine_root_kernel_and_cosine K L D A hA hmod
  change A * Q = 0 at hAQ
  change Q * A = 0 at hQA
  have hC : IsSelfAdjoint C := ((ContinuousLinearMap.nonneg_iff_isPositive).mp
    (Proposition35.section3CosAngleOperator_nonneg K L)).isSelfAdjoint
  have hQ : IsSelfAdjoint Q := isSelfAdjoint_starProjection B.ker
  have hVm : (V : E →L[𝕜] E) ∈ unitary (E →L[𝕜] E) := (Unitary.linearIsometryEquiv.symm V).property
  have hVC : Commute (V : E →L[𝕜] E) C := nuclearTransportDual_comm_cosine K L D
  have hVstarC : Commute (star (V : E →L[𝕜] E)) C := by
    change star (V : E →L[𝕜] E) * C = C * star (V : E →L[𝕜] E)
    have h := congrArg star hVC.eq
    rw [star_mul, star_mul, hC.star_eq] at h
    exact h.symm
  have hCQ : C * Q = Q := cosine_mul_skew_ker_projection K L D
  have hQC : Q * C = Q := by
    have h := congrArg star hCQ
    simpa only [star_mul, hC.star_eq, hQ.star_eq] using h
  have hVsum : (V : E →L[𝕜] E) + star (V : E →L[𝕜] E) = Q + Q := nuclearTransportDual_add_star K L D
  have hGexp : G = (Q + Q) - (V : E →L[𝕜] E) * C := by
    have h := congrArg (fun T : E →L[𝕜] E => T * C) hVsum
    rw [add_mul, add_mul, hQC] at h
    change (V : E →L[𝕜] E) * C + G = Q + Q at h
    rw [← h]
    abel
  have hAG : Commute A G := by
    have hAQcomm : Commute A Q := by change A * Q = Q * A; rw [hAQ, hQA]
    rw [hGexp]
    exact (hAQcomm.add_right hAQcomm).sub_right hcomm
  have hGsum : G + star G = Q + Q := by
    change star (V : E →L[𝕜] E) * C + star (star (V : E →L[𝕜] E) * C) = _
    rw [star_mul, star_star, hC.star_eq, ← hVC.eq, add_comm, ← add_mul, hVsum, add_mul, hQC]
  have hGs : star G = Q + Q - G := by rw [← hGsum]; abel
  have hGG : star G * G = C * C := by
    dsimp only [G]
    rw [star_mul, star_star, hC.star_eq]
    calc
      _ = C * (((V : E →L[𝕜] E) * star (V : E →L[𝕜] E)) * C) := by simp only [mul_assoc]
      _ = _ := by rw [Unitary.mul_star_self_of_mem hVm, one_mul]
  have hGG' : G * star G = C * C := by
    dsimp only [G]
    rw [star_mul, star_star, hC.star_eq, hVstarC.eq, ← hVC.eq]
    calc
      _ = C * ((star (V : E →L[𝕜] E) * (V : E →L[𝕜] E)) * C) := by simp only [mul_assoc]
      _ = _ := by rw [Unitary.star_mul_self_of_mem hVm, one_mul]
  have hcross : star G * A + A * G = 0 := by
    rw [hGs, sub_mul, add_mul, hQA, zero_add, zero_sub, hAG.eq]
    abel
  have hcross' : G * A + A * star G = 0 := by
    rw [hGs, mul_sub, mul_add, hAQ, zero_add, zero_sub, hAG.eq]
    abel
  have hCS : C * C + S * S = 1 := Proposition35.section3CosAngleOperator_sq_add_sinAngleOperator_sq K L
  have hU : G + A ∈ unitary (E →L[𝕜] E) := by
    apply Unitary.mem_iff.mpr
    constructor
    · rw [star_add, hA.star_eq, add_mul, mul_add, mul_add, hGG]
      calc
        _ = C * C + A * A + (star G * A + A * G) := by abel
        _ = 1 := by rw [hcross, add_zero, hsq]; exact hCS
    · rw [star_add, hA.star_eq, add_mul, mul_add, mul_add, hGG']
      calc
        _ = C * C + A * A + (G * A + A * star G) := by abel
        _ = 1 := by rw [hcross', add_zero, hsq]; exact hCS
  have hZ : C + (V : E →L[𝕜] E) * A = (V : E →L[𝕜] E) * (G + A) := by
    dsimp only [G]
    rw [mul_add, ← mul_assoc, Unitary.mul_star_self_of_mem hVm, one_mul]
  rw [hZ]
  exact (unitary (E →L[𝕜] E)).mul_mem hVm hU

/-- The actual relative unitary reconstructed from an independent
signed sine root. Source preservation follows from reflection oddness. -/
@[expose]
def nuclearSignedSineRelative
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L)
    (A : E →L[𝕜] E) (hA : IsSelfAdjoint A) (hmod : A.modulus = K.sinAngleOperator L)
    (hcomm : Commute A ((nuclearTransportDual K L D : E →L[𝕜] E) *
      Proposition35.section3CosAngleOperator K L)) : E ≃ₗᵢ[𝕜] E :=
  Unitary.linearIsometryEquiv
    (⟨Proposition35.section3CosAngleOperator K L + (nuclearTransportDual K L D : E →L[𝕜] E) * A,
      signed_sine_relative_mem_unitary K L D A hA hmod hcomm⟩ : unitary (E →L[𝕜] E))

/-- The reconstructed relative unitary has its stated literal coefficient. -/
theorem nuclearSignedSineRelative_def
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L)
    (A : E →L[𝕜] E) (hA : IsSelfAdjoint A) (hmod : A.modulus = K.sinAngleOperator L)
    (hcomm : Commute A ((nuclearTransportDual K L D : E →L[𝕜] E) *
      Proposition35.section3CosAngleOperator K L)) :
    (nuclearSignedSineRelative K L D A hA hmod hcomm : E →L[𝕜] E) =
      Proposition35.section3CosAngleOperator K L + (nuclearTransportDual K L D : E →L[𝕜] E) * A := rfl

/-- Every reconstructed relative unitary fixes the full common sector. -/
theorem nuclearSignedSineRelative_fixed_projection
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L)
    (A : E →L[𝕜] E) (hA : IsSelfAdjoint A) (hmod : A.modulus = K.sinAngleOperator L)
    (hcomm : Commute A ((nuclearTransportDual K L D : E →L[𝕜] E) *
      Proposition35.section3CosAngleOperator K L)) :
    let B := nonacuteDirectRotation K L D - Proposition35.section3CosAngleOperator K L
    (1 - (nuclearSignedSineRelative K L D A hA hmod hcomm : E →L[𝕜] E)) * B.ker.starProjection = 0 := by
  let B := nonacuteDirectRotation K L D - Proposition35.section3CosAngleOperator K L
  have hAQ := (signed_sine_root_kernel_and_cosine K L D A hA hmod).1
  have hCQ := cosine_mul_skew_ker_projection K L D
  change (1 - (nuclearSignedSineRelative K L D A hA hmod hcomm : E →L[𝕜] E)) * B.ker.starProjection = 0
  rw [nuclearSignedSineRelative_def, sub_mul, one_mul, add_mul, mul_assoc, hAQ, mul_zero, add_zero, hCQ, sub_self]

/-- Reflection-odd signed sine roots give source-preserving relative
unitaries, including the zero-cosine defect sector. -/
theorem nuclearSignedSineRelative_map
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L)
    (A : E →L[𝕜] E) (hA : IsSelfAdjoint A) (hmod : A.modulus = K.sinAngleOperator L)
    (hcomm : Commute A ((nuclearTransportDual K L D : E →L[𝕜] E) *
      Proposition35.section3CosAngleOperator K L))
    (hodd : K.reflection.conjStarAlgEquiv A = -A) :
    K.map (nuclearSignedSineRelative K L D A hA hmod hcomm).toLinearMap = K := by
  let C := Proposition35.section3CosAngleOperator K L
  let V := nuclearTransportDual K L D
  let Z := nuclearSignedSineRelative K L D A hA hmod hcomm
  let B := nonacuteDirectRotation K L D - C
  let Q := B.ker.starProjection
  have hQA := (signed_sine_root_kernel_and_cosine K L D A hA hmod).2.1
  change Q * A = 0 at hQA
  have hCeven : K.reflection.conjStarAlgEquiv C = C := by
    have hc := (K.commute_reflection_iff.mpr
      (Proposition35.section3CosAngleOperator_comm_projection K L).symm).eq
    ext x
    have h := congrArg (fun T : E →L[𝕜] E => T (K.reflection.symm x)) hc
    change K.reflection (C (K.reflection.symm x)) = C (K.reflection (K.reflection.symm x)) at h
    simpa only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
      K.reflection.apply_symm_apply] using h
  have hVeven : K.reflection.conjStarAlgEquiv (V : E →L[𝕜] E) = -(V : E →L[𝕜] E) + Q + Q :=
    reflection_conj_nuclearTransportDual K L D
  have hZeven : K.reflection.conjStarAlgEquiv (Z : E →L[𝕜] E) = (Z : E →L[𝕜] E) := by
    rw [show (Z : E →L[𝕜] E) = C + (V : E →L[𝕜] E) * A from nuclearSignedSineRelative_def K L D A hA hmod hcomm,
      map_add, map_mul, hCeven, hVeven, hodd]
    simp only [add_mul, mul_neg, neg_mul, neg_neg, hQA, add_zero]
  apply (K.map_eq_iff_intertwines_reflection K Z).mpr
  intro x
  have h := congrArg (fun T : E →L[𝕜] E => T (K.reflection x)) hZeven
  change K.reflection (Z (K.reflection.symm (K.reflection x))) = Z (K.reflection x) at h
  rw [K.reflection.symm_apply_apply] at h
  exact h.symm

/-- The actual unitary obtained by correcting completed direct rotation
with a signed sine root. The map theorem supplies its transport property. -/
@[expose]
def nuclearSignedSineTransport
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L)
    (A : E →L[𝕜] E) (hA : IsSelfAdjoint A) (hmod : A.modulus = K.sinAngleOperator L)
    (hcomm : Commute A ((nuclearTransportDual K L D : E →L[𝕜] E) *
      Proposition35.section3CosAngleOperator K L)) : E ≃ₗᵢ[𝕜] E :=
  (nuclearSignedSineRelative K L D A hA hmod hcomm).symm.trans
    (Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation K L D, nonacuteDirectRotation_mem_unitary K L D⟩ : unitary (E →L[𝕜] E)))

/-- Every reflection-odd signed sine root constructs an actual
transporter of the given subspaces. -/
theorem nuclearSignedSineTransport_map
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L)
    (A : E →L[𝕜] E) (hA : IsSelfAdjoint A) (hmod : A.modulus = K.sinAngleOperator L)
    (hcomm : Commute A ((nuclearTransportDual K L D : E →L[𝕜] E) *
      Proposition35.section3CosAngleOperator K L))
    (hodd : K.reflection.conjStarAlgEquiv A = -A) :
    K.map (nuclearSignedSineTransport K L D A hA hmod hcomm).toLinearMap = L := by
  let Z := nuclearSignedSineRelative K L D A hA hmod hcomm
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L D, nonacuteDirectRotation_mem_unitary K L D⟩ : unitary (E →L[𝕜] E))
  have hZmap : K.map Z.toLinearMap = K := nuclearSignedSineRelative_map K L D A hA hmod hcomm hodd
  have hRmap : K.map R.toLinearMap = L :=
    (K.map_eq_iff_intertwines_reflection L R).mpr (nonacuteDirectRotation_reflection_intertwines K L D)
  have h := K.map_correction_transport Z R
  rw [hZmap, hRmap] at h
  exact h

/-- The relative unitary of the reconstructed transporter is exactly
the prescribed signed-root unitary. -/
theorem nuclearSignedSineTransport_relative
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L)
    (A : E →L[𝕜] E) (hA : IsSelfAdjoint A) (hmod : A.modulus = K.sinAngleOperator L)
    (hcomm : Commute A ((nuclearTransportDual K L D : E →L[𝕜] E) *
      Proposition35.section3CosAngleOperator K L)) :
    ((nuclearSignedSineTransport K L D A hA hmod hcomm).symm : E →L[𝕜] E) *
      nonacuteDirectRotation K L D =
        (nuclearSignedSineRelative K L D A hA hmod hcomm : E →L[𝕜] E) := by
  let Z := nuclearSignedSineRelative K L D A hA hmod hcomm
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L D, nonacuteDirectRotation_mem_unitary K L D⟩ : unitary (E →L[𝕜] E))
  ext x
  change Z (R.symm (R x)) = Z x
  rw [R.symm_apply_apply]

/-- Extracting the signed sine after construction returns the exact
original parameter, not just an isomorphic or spectrally equal one. -/
theorem nuclearSignedSineTransport_extract_root
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L)
    (A : E →L[𝕜] E) (hA : IsSelfAdjoint A) (hmod : A.modulus = K.sinAngleOperator L)
    (hcomm : Commute A ((nuclearTransportDual K L D : E →L[𝕜] E) *
      Proposition35.section3CosAngleOperator K L)) :
    star (nuclearTransportDual K L D : E →L[𝕜] E) *
      (((nuclearSignedSineTransport K L D A hA hmod hcomm).symm : E →L[𝕜] E) *
        nonacuteDirectRotation K L D - Proposition35.section3CosAngleOperator K L) = A := by
  rw [nuclearSignedSineTransport_relative, nuclearSignedSineRelative_def, add_sub_cancel_left,
    ← mul_assoc]
  have hVm : (nuclearTransportDual K L D : E →L[𝕜] E) ∈ unitary (E →L[𝕜] E) :=
    (Unitary.linearIsometryEquiv.symm (nuclearTransportDual K L D)).property
  rw [Unitary.star_mul_self_of_mem hVm, one_mul]

/-- The reconstructed transporter's calibrated displacement is
exactly the sine minus the prescribed signed root. -/
theorem nuclearSignedSineTransport_dual_displacement
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L)
    (A : E →L[𝕜] E) (hA : IsSelfAdjoint A) (hmod : A.modulus = K.sinAngleOperator L)
    (hcomm : Commute A ((nuclearTransportDual K L D : E →L[𝕜] E) *
      Proposition35.section3CosAngleOperator K L)) :
    star (nuclearTransportDual K L D : E →L[𝕜] E) *
      (nonacuteDirectRotation K L D -
        ((nuclearSignedSineTransport K L D A hA hmod hcomm).symm : E →L[𝕜] E) *
          nonacuteDirectRotation K L D) = K.sinAngleOperator L - A := by
  rw [nuclearSignedSineTransport_relative, nuclearSignedSineRelative_def]
  let C := Proposition35.section3CosAngleOperator K L
  let V := nuclearTransportDual K L D
  have hVB : star (V : E →L[𝕜] E) * (nonacuteDirectRotation K L D - C) = K.sinAngleOperator L :=
    nuclearTransportDual_adjoint_mul_skew K L D
  have hVm : (V : E →L[𝕜] E) ∈ unitary (E →L[𝕜] E) := (Unitary.linearIsometryEquiv.symm V).property
  have hsub : nonacuteDirectRotation K L D - (C + (V : E →L[𝕜] E) * A) =
      (nonacuteDirectRotation K L D - C) - (V : E →L[𝕜] E) * A := by abel
  change star (V : E →L[𝕜] E) * _ = _
  rw [hsub, mul_sub, hVB, ← mul_assoc, Unitary.star_mul_self_of_mem hVm, one_mul]

section Complex

open scoped ENNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **Every admissible signed root constructs a global optimizer.**
The minimum is over all ambient complex unitary transporters, without
an invariant-plane restriction. Finite displacement follows automatically. -/
theorem nuclearSignedSineTransport_isMin_complex
    (K L : Submodule ℂ F) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hΔ : (K.starProjection - L.starProjection).nuclearENorm ≠ ∞)
    (A : F →L[ℂ] F) (hA : IsSelfAdjoint A) (hmod : A.modulus = K.sinAngleOperator L)
    (hcomm : Commute A ((nuclearTransportDual K L D : F →L[ℂ] F) *
      Proposition35.section3CosAngleOperator K L))
    (hodd : K.reflection.conjStarAlgEquiv A = -A)
    (W : F ≃ₗᵢ[ℂ] F) (hW : K.map W.toLinearMap = L) :
    (1 - (nuclearSignedSineTransport K L D A hA hmod hcomm : F →L[ℂ] F)).nuclearENorm ≤
      (1 - (W : F →L[ℂ] F)).nuclearENorm := by
  let T := nuclearSignedSineTransport K L D A hA hmod hcomm
  let Z := nuclearSignedSineRelative K L D A hA hmod hcomm
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L D, nonacuteDirectRotation_mem_unitary K L D⟩ : unitary (F →L[ℂ] F))
  let B := nonacuteDirectRotation K L D - Proposition35.section3CosAngleOperator K L
  let Q := B.ker.starProjection
  have hT : K.map T.toLinearMap = L := nuclearSignedSineTransport_map K L D A hA hmod hcomm hodd
  apply ((nuclear_isMin_iff_hermitian_certificate_complex K L D hΔ T hT).mpr ?_) W hW
  constructor
  · intro x hx
    have hxker : x ∈ B.ker := by
      rw [ker_nonacuteDirectRotation_sub_cosine_eq_projection_sub]
      change K.starProjection x - L.starProjection x = 0
      exact sub_eq_zero.mpr hx
    have hQx : Q x = x := B.ker.starProjection_eq_self_iff.mpr hxker
    have hfix := nuclearSignedSineRelative_fixed_projection K L D A hA hmod hcomm
    have hZx := congrArg (fun U : F →L[ℂ] F => U x) hfix
    change Q x - Z (Q x) = 0 at hZx
    rw [hQx] at hZx
    have hZsymm := congrArg Z.symm (sub_eq_zero.mp hZx)
    rw [Z.symm_apply_apply] at hZsymm
    change R (Z.symm x) = x
    rw [hZsymm]
    exact nonacuteDirectRotation_apply_eq_self_of_projections_eq K L D x hx
  · rw [nuclearSignedSineTransport_dual_displacement]
    exact (K.isPositive_sinAngleOperator L).isSelfAdjoint.sub hA

end Complex

end TauCeti.DavisKahan

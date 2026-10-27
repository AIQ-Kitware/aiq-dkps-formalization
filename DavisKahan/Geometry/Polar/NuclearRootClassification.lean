/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.Geometry.Polar.NuclearRootConstruction

/-!
# Complete signed-root parameters for nuclear optimizers

The parameters are independent bounded self-adjoint sine roots,
reflection odd and commuting with the dual times cosine. The forward
construction is inverted literally, including all exceptional sectors.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- The extracted signed sine commutes with the dual times cosine.
No inverse cosine is used, so this retains the unrestricted right-angle
kernel instead of imposing phase commutation there. -/
theorem nuclearTransportDual_signed_sine_comm_cosine_phase
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L)
    (Z : E ≃ₗᵢ[𝕜] E)
    (hfix : (1 - (Z : E →L[𝕜] E)) *
      (nonacuteDirectRotation K L D - Proposition35.section3CosAngleOperator K L).ker.starProjection = 0)
    (hself : IsSelfAdjoint (star (nuclearTransportDual K L D : E →L[𝕜] E) *
      (nonacuteDirectRotation K L D - (Z : E →L[𝕜] E)))) :
    Commute (star (nuclearTransportDual K L D : E →L[𝕜] E) *
      ((Z : E →L[𝕜] E) - Proposition35.section3CosAngleOperator K L))
        ((nuclearTransportDual K L D : E →L[𝕜] E) * Proposition35.section3CosAngleOperator K L) := by
  let C := Proposition35.section3CosAngleOperator K L
  let V := nuclearTransportDual K L D
  let W := (V.trans Z.symm).trans V.symm
  have hC : C.IsPositive := ContinuousLinearMap.nonneg_iff_isPositive.mp
    (Proposition35.section3CosAngleOperator_nonneg K L)
  have hVC : Commute (V : E →L[𝕜] E) C := nuclearTransportDual_comm_cosine K L D
  have hVm : (V : E →L[𝕜] E) ∈ unitary (E →L[𝕜] E) := (Unitary.linearIsometryEquiv.symm V).property
  have hW : (W : E →L[𝕜] E) =
      star (V : E →L[𝕜] E) * star (Z : E →L[𝕜] E) * (V : E →L[𝕜] E) := by
    rw [V.star_eq_symm, Z.star_eq_symm]
    ext x
    rfl
  have hWs : star (W : E →L[𝕜] E) =
      star (V : E →L[𝕜] E) * (Z : E →L[𝕜] E) * (V : E →L[𝕜] E) := by
    rw [W.star_eq_symm, V.star_eq_symm]
    ext x
    rfl
  have hsum : (Z : E →L[𝕜] E) + (W : E →L[𝕜] E) = C + C := by
    rw [hW]
    exact nuclearTransportDual_relative_positive_average K L D Z hfix hself
  have hstruct := TauCeti.ContinuousLinearMap.unitary_positive_average_structure
    C (Z : E →L[𝕜] E) (W : E →L[𝕜] E) hC
      (Unitary.linearIsometryEquiv.symm Z).property (Unitary.linearIsometryEquiv.symm W).property hsum
  have hz := hstruct.2.2
  rw [mul_sub, sub_eq_zero, hWs] at hz
  have hInter : (V : E →L[𝕜] E) * (C * (Z : E →L[𝕜] E)) = C * (Z : E →L[𝕜] E) * (V : E →L[𝕜] E) := by
    calc
      _ = (V : E →L[𝕜] E) * (C * (star (V : E →L[𝕜] E) * (Z : E →L[𝕜] E) * (V : E →L[𝕜] E))) :=
        congrArg (fun T : E →L[𝕜] E => (V : E →L[𝕜] E) * T) hz
      _ = ((V : E →L[𝕜] E) * C) * star (V : E →L[𝕜] E) * (Z : E →L[𝕜] E) * (V : E →L[𝕜] E) := by
        simp only [mul_assoc]
      _ = (C * (V : E →L[𝕜] E)) * star (V : E →L[𝕜] E) * (Z : E →L[𝕜] E) * (V : E →L[𝕜] E) := by rw [hVC.eq]
      _ = C * ((V : E →L[𝕜] E) * star (V : E →L[𝕜] E)) * (Z : E →L[𝕜] E) * (V : E →L[𝕜] E) := by
        simp only [mul_assoc]
      _ = _ := by rw [Unitary.mul_star_self_of_mem hVm, mul_one]
  have hZVC : Commute (Z : E →L[𝕜] E) ((V : E →L[𝕜] E) * C) := by
    change (Z : E →L[𝕜] E) * ((V : E →L[𝕜] E) * C) = ((V : E →L[𝕜] E) * C) * (Z : E →L[𝕜] E)
    calc
      _ = (Z : E →L[𝕜] E) * (C * (V : E →L[𝕜] E)) := by rw [hVC.eq]
      _ = (C * (Z : E →L[𝕜] E)) * (V : E →L[𝕜] E) := by rw [← mul_assoc, hstruct.1.eq]
      _ = (V : E →L[𝕜] E) * (C * (Z : E →L[𝕜] E)) := hInter.symm
      _ = _ := (mul_assoc _ _ _).symm
  have hVstarC : Commute (star (V : E →L[𝕜] E)) C := by
    change star (V : E →L[𝕜] E) * C = C * star (V : E →L[𝕜] E)
    have h := congrArg star hVC.eq
    rw [star_mul, star_mul, hC.isSelfAdjoint.star_eq] at h
    exact h.symm
  have hVstarVC : Commute (star (V : E →L[𝕜] E)) ((V : E →L[𝕜] E) * C) :=
    (commute_unitary_star_self hVm).mul_right hVstarC
  have hCVC : Commute C ((V : E →L[𝕜] E) * C) := hVC.symm.mul_right (Commute.refl C)
  exact hVstarVC.mul_left (hZVC.sub_left hCVC)

/-- Source-preserving relative unitaries have reflection-odd signed
sines. Common directions are retained, rather than assumed absent. -/
theorem nuclearTransportDual_signed_sine_reflection_odd
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L)
    (Z : E ≃ₗᵢ[𝕜] E) (hZ : ∀ x, Z (K.reflection x) = K.reflection (Z x))
    (hfix : (1 - (Z : E →L[𝕜] E)) *
      (nonacuteDirectRotation K L D - Proposition35.section3CosAngleOperator K L).ker.starProjection = 0) :
    K.reflection.conjStarAlgEquiv (star (nuclearTransportDual K L D : E →L[𝕜] E) *
      ((Z : E →L[𝕜] E) - Proposition35.section3CosAngleOperator K L)) =
        -(star (nuclearTransportDual K L D : E →L[𝕜] E) *
          ((Z : E →L[𝕜] E) - Proposition35.section3CosAngleOperator K L)) := by
  let C := Proposition35.section3CosAngleOperator K L
  let V := nuclearTransportDual K L D
  let B := nonacuteDirectRotation K L D - C
  let Q := B.ker.starProjection
  have hQ : IsSelfAdjoint Q := isSelfAdjoint_starProjection B.ker
  have hC : IsSelfAdjoint C := ((ContinuousLinearMap.nonneg_iff_isPositive).mp
    (Proposition35.section3CosAngleOperator_nonneg K L)).isSelfAdjoint
  have hZm : (Z : E →L[𝕜] E) ∈ unitary (E →L[𝕜] E) := (Unitary.linearIsometryEquiv.symm Z).property
  have hZQ : (Z : E →L[𝕜] E) * Q = Q := by
    change (1 - (Z : E →L[𝕜] E)) * Q = 0 at hfix
    rw [sub_mul, one_mul, sub_eq_zero] at hfix
    exact hfix.symm
  have hQZ : Q * (Z : E →L[𝕜] E) = Q := by
    have h := congrArg star hZQ
    rw [star_mul, hQ.star_eq] at h
    have h' := congrArg (fun T : E →L[𝕜] E => T * (Z : E →L[𝕜] E)) h
    rw [mul_assoc, Unitary.star_mul_self_of_mem hZm, mul_one] at h'
    exact h'.symm
  have hCQ : C * Q = Q := cosine_mul_skew_ker_projection K L D
  have hQC : Q * C = Q := by
    simpa only [star_mul, hC.star_eq, hQ.star_eq] using congrArg star hCQ
  have hQzero : Q * ((Z : E →L[𝕜] E) - C) = 0 := by rw [mul_sub, hQZ, hQC, sub_self]
  have hVeven : K.reflection.conjStarAlgEquiv (V : E →L[𝕜] E) = -(V : E →L[𝕜] E) + Q + Q :=
    reflection_conj_nuclearTransportDual K L D
  have hCeven : K.reflection.conjStarAlgEquiv C = C := by
    have hc := (K.commute_reflection_iff.mpr
      (Proposition35.section3CosAngleOperator_comm_projection K L).symm).eq
    ext x
    have h := congrArg (fun T : E →L[𝕜] E => T (K.reflection.symm x)) hc
    change K.reflection (C (K.reflection.symm x)) = C (K.reflection (K.reflection.symm x)) at h
    simpa only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
      K.reflection.apply_symm_apply] using h
  have hZeven : K.reflection.conjStarAlgEquiv (Z : E →L[𝕜] E) = (Z : E →L[𝕜] E) := by
    ext x
    rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
    change K.reflection (Z (K.reflection.symm x)) = Z x
    rw [← hZ, K.reflection.apply_symm_apply]
  change K.reflection.conjStarAlgEquiv (star (V : E →L[𝕜] E) * ((Z : E →L[𝕜] E) - C)) = _
  rw [map_mul, map_star, map_sub, hVeven, hZeven, hCeven, star_add, star_add, star_neg, hQ.star_eq,
    add_mul, add_mul, neg_mul, hQzero, add_zero, add_zero]

/-- The extracted root satisfies every independent parameter condition
and reconstructs the exact relative unitary. -/
theorem nuclearTransportDual_signed_sine_parameters
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L)
    (Z : E ≃ₗᵢ[𝕜] E) (hZ : ∀ x, Z (K.reflection x) = K.reflection (Z x))
    (hfix : (1 - (Z : E →L[𝕜] E)) *
      (nonacuteDirectRotation K L D - Proposition35.section3CosAngleOperator K L).ker.starProjection = 0)
    (hself : IsSelfAdjoint (star (nuclearTransportDual K L D : E →L[𝕜] E) *
      (nonacuteDirectRotation K L D - (Z : E →L[𝕜] E)))) :
    let C := Proposition35.section3CosAngleOperator K L
    let V := nuclearTransportDual K L D
    let A := star (V : E →L[𝕜] E) * ((Z : E →L[𝕜] E) - C)
    IsSelfAdjoint A ∧ A.modulus = K.sinAngleOperator L ∧
      Commute A ((V : E →L[𝕜] E) * C) ∧ K.reflection.conjStarAlgEquiv A = -A ∧
        (Z : E →L[𝕜] E) = C + (V : E →L[𝕜] E) * A := by
  obtain ⟨hA, hmod, _, _⟩ := nuclearTransportDual_signed_sine_structure K L D Z hfix hself
  refine ⟨hA, hmod, nuclearTransportDual_signed_sine_comm_cosine_phase K L D Z hfix hself,
    nuclearTransportDual_signed_sine_reflection_odd K L D Z hZ hfix, ?_⟩
  let V := nuclearTransportDual K L D
  have hVm : (V : E →L[𝕜] E) ∈ unitary (E →L[𝕜] E) := (Unitary.linearIsometryEquiv.symm V).property
  rw [← mul_assoc, Unitary.mul_star_self_of_mem hVm, one_mul]
  abel

/-- Reconstruction recovers any unitary having the specified relative
coefficient. No optimization or source-map assumption is needed. -/
theorem nuclearSignedSineTransport_eq_of_relative
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L)
    (A : E →L[𝕜] E) (hA : IsSelfAdjoint A) (hmod : A.modulus = K.sinAngleOperator L)
    (hcomm : Commute A ((nuclearTransportDual K L D : E →L[𝕜] E) *
      Proposition35.section3CosAngleOperator K L))
    (T : E ≃ₗᵢ[𝕜] E)
    (hrelative : (T.symm : E →L[𝕜] E) * nonacuteDirectRotation K L D =
      Proposition35.section3CosAngleOperator K L + (nuclearTransportDual K L D : E →L[𝕜] E) * A) :
    nuclearSignedSineTransport K L D A hA hmod hcomm = T := by
  let U := nuclearSignedSineTransport K L D A hA hmod hcomm
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L D, nonacuteDirectRotation_mem_unitary K L D⟩ : unitary (E →L[𝕜] E))
  have hrel : (U.symm : E →L[𝕜] E) * nonacuteDirectRotation K L D =
      (T.symm : E →L[𝕜] E) * nonacuteDirectRotation K L D :=
    ((nuclearSignedSineTransport_relative K L D A hA hmod hcomm).trans
      (nuclearSignedSineRelative_def K L D A hA hmod hcomm)).trans hrelative.symm
  ext x
  apply T.symm.injective
  rw [T.symm_apply_apply]
  have h := congrArg (fun B : E →L[𝕜] E => B (R.symm (U x))) hrel
  change U.symm (R (R.symm (U x))) = T.symm (R (R.symm (U x))) at h
  rw [R.apply_symm_apply, U.symm_apply_apply] at h
  exact h.symm

/-- The independent signed-root parameter set. All its conditions
are operator identities; transport and cost are consequences. -/
def nuclearSignedSineParameters
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L) : Set (E →L[𝕜] E) :=
  {A | IsSelfAdjoint A ∧ A.modulus = K.sinAngleOperator L ∧
    Commute A ((nuclearTransportDual K L D : E →L[𝕜] E) * Proposition35.section3CosAngleOperator K L) ∧
      K.reflection.conjStarAlgEquiv A = -A}

/-- Membership in the independent parameter set, with no optimization
predicate hidden among its hypotheses. -/
@[simp]
theorem mem_nuclearSignedSineParameters
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L) (A : E →L[𝕜] E) :
    A ∈ nuclearSignedSineParameters K L D ↔
      IsSelfAdjoint A ∧ A.modulus = K.sinAngleOperator L ∧
        Commute A ((nuclearTransportDual K L D : E →L[𝕜] E) * Proposition35.section3CosAngleOperator K L) ∧
          K.reflection.conjStarAlgEquiv A = -A := Iff.rfl

/-- The actual ambient nuclear minimizers, including the transport
constraint and comparison with every feasible ambient competitor. -/
def nuclearTransportOptimizers
    (K L : Submodule 𝕜 E) : Set (E ≃ₗᵢ[𝕜] E) :=
  {T | K.map T.toLinearMap = L ∧ ∀ W : E ≃ₗᵢ[𝕜] E, K.map W.toLinearMap = L →
    (1 - (T : E →L[𝕜] E)).nuclearENorm ≤ (1 - (W : E →L[𝕜] E)).nuclearENorm}

omit [CompleteSpace E] in
/-- Membership in the unrestricted ambient optimizer set. -/
@[simp]
theorem mem_nuclearTransportOptimizers
    (K L : Submodule 𝕜 E) (T : E ≃ₗᵢ[𝕜] E) :
    T ∈ nuclearTransportOptimizers K L ↔ K.map T.toLinearMap = L ∧
      ∀ W : E ≃ₗᵢ[𝕜] E, K.map W.toLinearMap = L →
        (1 - (T : E →L[𝕜] E)).nuclearENorm ≤ (1 - (W : E →L[𝕜] E)).nuclearENorm := Iff.rfl

section Complex

open scoped ENNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Every global complex optimizer gives an independent signed sine
parameter and the exact reconstruction identity, with all degeneracies
included. This is the necessity direction of the full parametrization. -/
theorem nuclear_minimizer_signed_sine_parameters_complex
    (K L : Submodule ℂ F) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hΔ : (K.starProjection - L.starProjection).nuclearENorm ≠ ∞)
    (T : F ≃ₗᵢ[ℂ] F) (hT : K.map T.toLinearMap = L)
    (hmin : ∀ W : F ≃ₗᵢ[ℂ] F, K.map W.toLinearMap = L →
      (1 - (T : F →L[ℂ] F)).nuclearENorm ≤ (1 - (W : F →L[ℂ] F)).nuclearENorm) :
    let C := Proposition35.section3CosAngleOperator K L
    let R := nonacuteDirectRotation K L D
    let V := nuclearTransportDual K L D
    let A := star (V : F →L[ℂ] F) * ((T.symm : F →L[ℂ] F) * R - C)
    A ∈ nuclearSignedSineParameters K L D ∧
      (T.symm : F →L[ℂ] F) * R = C + (V : F →L[ℂ] F) * A := by
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L D, nonacuteDirectRotation_mem_unitary K L D⟩ : unitary (F →L[ℂ] F))
  let Z := R.trans T.symm
  let C := Proposition35.section3CosAngleOperator K L
  let B := nonacuteDirectRotation K L D - C
  let Q := B.ker.starProjection
  have hcert := (nuclear_isMin_iff_hermitian_certificate_complex K L D hΔ T hT).mp hmin
  have hRref (x : F) : R (K.reflection x) = L.reflection (R x) :=
    nonacuteDirectRotation_reflection_intertwines K L D x
  have hTref := (K.map_eq_iff_intertwines_reflection L T).mp hT
  have hZ (x : F) : Z (K.reflection x) = K.reflection (Z x) := by
    apply T.injective
    change T (T.symm (R (K.reflection x))) = T (K.reflection (T.symm (R x)))
    rw [T.apply_symm_apply, hTref, T.apply_symm_apply, hRref]
  have hfix : (1 - (Z : F →L[ℂ] F)) * Q = 0 := by
    ext x
    have hx := B.ker.starProjection_apply_mem x
    change Q x ∈ B.ker at hx
    rw [ker_nonacuteDirectRotation_sub_cosine_eq_projection_sub] at hx
    change K.starProjection (Q x) - L.starProjection (Q x) = 0 at hx
    have hR : R (Q x) = Q x :=
      nonacuteDirectRotation_apply_eq_self_of_projections_eq K L D _ (sub_eq_zero.mp hx)
    have hTQ := hcert.1 (Q x) (sub_eq_zero.mp hx)
    have hZQ : Z (Q x) = Q x := by
      apply T.injective
      change T (T.symm (R (Q x))) = T (Q x)
      rw [T.apply_symm_apply, hR, hTQ]
    change Q x - Z (Q x) = 0
    rw [hZQ, sub_self]
  have hself : IsSelfAdjoint (star (nuclearTransportDual K L D : F →L[ℂ] F) *
      (nonacuteDirectRotation K L D - (Z : F →L[ℂ] F))) := hcert.2
  obtain ⟨hA, hmod, hcomm, hodd, hrelative⟩ :=
    nuclearTransportDual_signed_sine_parameters K L D Z hZ hfix hself
  exact ⟨(mem_nuclearSignedSineParameters K L D _).mpr ⟨hA, hmod, hcomm, hodd⟩, hrelative⟩

/-- **Complete signed-root parametrization of every complex nuclear
optimizer.** The maps are the explicit construction and exact root
extraction, inverse on the nose. Infinite rank, zero angles, repeated
angles, fixed ambient directions and right defects are all included. -/
@[expose]
def nuclearSignedSineEquivOptimizers_complex
    (K L : Submodule ℂ F) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hΔ : (K.starProjection - L.starProjection).nuclearENorm ≠ ∞) :
    nuclearSignedSineParameters K L D ≃ nuclearTransportOptimizers K L where
  toFun A :=
    let hp := (mem_nuclearSignedSineParameters K L D A.val).mp A.property
    ⟨nuclearSignedSineTransport K L D A.val hp.1 hp.2.1 hp.2.2.1,
      (mem_nuclearTransportOptimizers K L _).mpr
        ⟨nuclearSignedSineTransport_map K L D A.val hp.1 hp.2.1 hp.2.2.1 hp.2.2.2,
          nuclearSignedSineTransport_isMin K L D A.val hp.1 hp.2.1 hp.2.2.1 hp.2.2.2⟩⟩
  invFun T :=
    let hp := (mem_nuclearTransportOptimizers K L T.val).mp T.property
    ⟨star (nuclearTransportDual K L D : F →L[ℂ] F) *
      ((T.val.symm : F →L[ℂ] F) * nonacuteDirectRotation K L D - Proposition35.section3CosAngleOperator K L),
        (nuclear_minimizer_signed_sine_parameters_complex K L D hΔ T.val hp.1 hp.2).1⟩
  left_inv A := by
    apply Subtype.ext
    exact nuclearSignedSineTransport_extract_root K L D A.val _ _ _
  right_inv T := by
    apply Subtype.ext
    have hp := (mem_nuclearTransportOptimizers K L T.val).mp T.property
    exact nuclearSignedSineTransport_eq_of_relative K L D _ _ _ _ T.val
      (nuclear_minimizer_signed_sine_parameters_complex K L D hΔ T.val hp.1 hp.2).2

/-- The inverse of the full parametrization is the literal signed-root
extraction, independent of any choices of spectral coordinates. -/
@[simp]
theorem nuclearSignedSineEquivOptimizers_symm_apply_complex
    (K L : Submodule ℂ F) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hΔ : (K.starProjection - L.starProjection).nuclearENorm ≠ ∞)
    (T : nuclearTransportOptimizers K L) :
    ((nuclearSignedSineEquivOptimizers_complex K L D hΔ).symm T).val =
      star (nuclearTransportDual K L D : F →L[ℂ] F) *
        ((T.val.symm : F →L[ℂ] F) * nonacuteDirectRotation K L D -
          Proposition35.section3CosAngleOperator K L) := rfl

/-- The forward parametrization has the stated relative coefficient;
it does not choose a different representative of the optimizer family. -/
theorem nuclearSignedSineEquivOptimizers_relative_complex
    (K L : Submodule ℂ F) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hΔ : (K.starProjection - L.starProjection).nuclearENorm ≠ ∞)
    (A : nuclearSignedSineParameters K L D) :
    (((nuclearSignedSineEquivOptimizers_complex K L D hΔ A).val.symm : F →L[ℂ] F) *
      nonacuteDirectRotation K L D) = Proposition35.section3CosAngleOperator K L +
        (nuclearTransportDual K L D : F →L[ℂ] F) * A.val := by
  have hp := (mem_nuclearSignedSineParameters K L D A.val).mp A.property
  exact (nuclearSignedSineTransport_relative K L D A.val hp.1 hp.2.1 hp.2.2.1).trans
    (nuclearSignedSineRelative_def K L D A.val hp.1 hp.2.1 hp.2.2.1)

end Complex

end TauCeti.DavisKahan

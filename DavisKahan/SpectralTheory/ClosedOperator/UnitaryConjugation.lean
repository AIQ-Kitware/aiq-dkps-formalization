/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.SpectralTheory.ClosedOperator.MathlibBridge
import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Constructions
import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent

/-!
# Unitary conjugation for DK closed operators

This module exposes the vendored Spectra unitary-conjugation construction in
terms of the DK closed-operator wrapper.  The source and target Hilbert spaces
may differ, which is important when conjugating operators restricted to
spectral subspaces.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace SpectraBridge


universe u v

variable {H : Type u} {K : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Conjugate a self-adjoint DK closed operator by a linear isometry
 equivalence.  The resulting DK operator is obtained by forgetting the
 self-adjoint partial operator built from the conjugated partial operator. -/
noncomputable def unitaryConjugate
    (W : H ≃ₗᵢ[ℂ] K) (A : DKClosedOperator (H := H))
    (hA : A.IsSelfAdjoint) : DKClosedOperator (H := K) :=
  closedOperatorOfSelfAdjointPMap (TauCeti.LinearPMap.unitaryConj W A.toLinearPMap)
    (TauCeti.LinearPMap.isSelfAdjoint_unitaryConj hA)

/-- The domain of a unitary conjugate is the image of the original domain. -/
@[simp] theorem unitaryConjugate_domain
    (W : H ≃ₗᵢ[ℂ] K) (A : DKClosedOperator (H := H))
    (hA : A.IsSelfAdjoint) :
    (unitaryConjugate W A hA).domain =
      A.domain.comap (W.symm.toLinearEquiv : K →ₗ[ℂ] H) := rfl

/-- Membership in the transported domain is the expected inverse-image
condition. -/
theorem mem_unitaryConjugate_domain_iff
    (W : H ≃ₗᵢ[ℂ] K) (A : DKClosedOperator (H := H))
    (hA : A.IsSelfAdjoint) {x : K} :
    x ∈ (unitaryConjugate W A hA).domain ↔ W.symm x ∈ A.domain := Iff.rfl

/-- The transported domain is also the direct image of the original domain. -/
theorem unitaryConjugate_domain_eq_map
    (W : H ≃ₗᵢ[ℂ] K) (A : DKClosedOperator (H := H))
    (hA : A.IsSelfAdjoint) :
    (unitaryConjugate W A hA).domain =
      A.domain.map (W.toLinearEquiv : H →ₗ[ℂ] K) := by
  ext x
  constructor
  · intro hx
    refine ⟨W.symm x, hx, ?_⟩
    exact W.apply_symm_apply x
  · rintro ⟨z, hz, rfl⟩
    change W.symm (W z) ∈ A.domain
    simpa using hz

/-- The unitary conjugate acts by transporting, applying, and transporting back. -/
@[simp] theorem unitaryConjugate_apply
    (W : H ≃ₗᵢ[ℂ] K) (A : DKClosedOperator (H := H))
    (hA : A.IsSelfAdjoint) (x : (unitaryConjugate W A hA).domain) :
    (unitaryConjugate W A hA).toLinearMap x =
      W (A.toLinearMap ⟨W.symm (x : K), x.property⟩) := rfl

/-- The unitary sends every original-domain vector into the transported
 domain. -/
theorem unitaryConjugate_map_mem_domain
    (W : H ≃ₗᵢ[ℂ] K) (A : DKClosedOperator (H := H))
    (hA : A.IsSelfAdjoint) (x : A.domain) :
    W (x : H) ∈ (unitaryConjugate W A hA).domain := by
  rw [mem_unitaryConjugate_domain_iff, W.symm_apply_apply]
  exact x.property

/-- Conjugation acts by the expected formula on transported domain vectors. -/
theorem unitaryConjugate_apply_map
    (W : H ≃ₗᵢ[ℂ] K) (A : DKClosedOperator (H := H))
    (hA : A.IsSelfAdjoint) (x : A.domain) :
    (unitaryConjugate W A hA).toLinearMap
        ⟨W (x : H), unitaryConjugate_map_mem_domain W A hA x⟩ =
      W (A.toLinearMap x) := by
  rw [unitaryConjugate_apply]
  congr 1
  exact congrArg A.toLinearMap
    (Subtype.ext (W.symm_apply_apply (x : H)))

/-- Transport a bounded operator through a unitary equivalence. -/
noncomputable def unitaryConjugateBounded
    (W : H ≃ₗᵢ[ℂ] K) (R : H →L[ℂ] H) : K →L[ℂ] K :=
  W.toLinearIsometry.toContinuousLinearMap ∘L R ∘L
    W.symm.toLinearIsometry.toContinuousLinearMap

omit [CompleteSpace H] [CompleteSpace K] in
/-- The bounded unitary conjugate, unfolded. -/
@[simp] theorem unitaryConjugateBounded_apply
    (W : H ≃ₗᵢ[ℂ] K) (R : H →L[ℂ] H) (x : K) :
    unitaryConjugateBounded W R x = W (R (W.symm x)) := rfl

omit [CompleteSpace H] [CompleteSpace K] in
/-- A resolvent of a partial operator transports to its unitary conjugate. -/
theorem mem_resolventSet_unitaryConj_of_mem
    (W : H ≃ₗᵢ[ℂ] K) (A : H →ₗ.[ℂ] H) {z : ℂ}
    (hz : z ∈ TauCeti.LinearPMap.resolventSet A) :
    z ∈ TauCeti.LinearPMap.resolventSet
      (TauCeti.LinearPMap.unitaryConj W A) := by
  obtain ⟨R, hleft, hright⟩ := hz
  refine ⟨unitaryConjugateBounded W R, ?_, ?_⟩
  · intro ψ
    let x : A.domain := ⟨W.symm (ψ : K), ψ.property⟩
    have hx := congrArg W (hleft x)
    simpa only [x, unitaryConjugateBounded_apply,
      TauCeti.LinearPMap.unitaryConj_apply, map_sub, map_smul,
      W.symm_apply_apply, W.apply_symm_apply] using hx
  · intro φ
    obtain ⟨hmem, hrightφ⟩ := hright (W.symm φ)
    have htransport : W (R (W.symm φ)) ∈
        (TauCeti.LinearPMap.unitaryConj W A).domain := by
      rw [TauCeti.LinearPMap.mem_unitaryConj_domain_iff,
        W.symm_apply_apply]
      exact hmem
    refine ⟨htransport, ?_⟩
    have hφ := congrArg W hrightφ
    simpa only [TauCeti.LinearPMap.unitaryConj_apply,
      unitaryConjugateBounded_apply, map_sub, map_smul,
      W.symm_apply_apply, W.apply_symm_apply] using hφ

omit [CompleteSpace H] [CompleteSpace K] in
/-- Conjugation first by `W` and then by `W⁻¹` returns the original partial
operator. -/
theorem unitaryConj_symm_unitaryConj
    (W : H ≃ₗᵢ[ℂ] K) (A : H →ₗ.[ℂ] H) :
    TauCeti.LinearPMap.unitaryConj W.symm
        (TauCeti.LinearPMap.unitaryConj W A) = A := by
  refine LinearPMap.ext_iff.mpr ⟨?_, ?_⟩
  · ext x
    simp only [TauCeti.LinearPMap.mem_unitaryConj_domain_iff,
      LinearIsometryEquiv.symm_symm, W.symm_apply_apply]
  · intro x hx hy
    rw [TauCeti.LinearPMap.unitaryConj_apply,
      TauCeti.LinearPMap.unitaryConj_apply]
    simp only [LinearIsometryEquiv.symm_symm, W.symm_apply_apply]

omit [CompleteSpace H] [CompleteSpace K] in
/-- Resolvent membership is invariant under unitary conjugation. -/
theorem mem_resolventSet_unitaryConj_iff
    (W : H ≃ₗᵢ[ℂ] K) (A : H →ₗ.[ℂ] H) {z : ℂ} :
    z ∈ TauCeti.LinearPMap.resolventSet
        (TauCeti.LinearPMap.unitaryConj W A) ↔
      z ∈ TauCeti.LinearPMap.resolventSet A := by
  constructor
  · intro hz
    have hz' := mem_resolventSet_unitaryConj_of_mem
      W.symm (TauCeti.LinearPMap.unitaryConj W A) hz
    rwa [unitaryConj_symm_unitaryConj W A] at hz'
  · exact mem_resolventSet_unitaryConj_of_mem W A

/-- A resolvent of the original DK operator transports to a resolvent of the
unitarily conjugated DK operator. -/
theorem mem_resolventSet_unitaryConjugate_iff
    (W : H ≃ₗᵢ[ℂ] K) (A : DKClosedOperator (H := H))
    (hA : A.IsSelfAdjoint) {z : ℂ} :
    z ∈ TauCeti.LinearPMap.resolventSet
        (unitaryConjugate W A hA).toLinearPMap ↔
      z ∈ TauCeti.LinearPMap.resolventSet A.toLinearPMap := by
  change z ∈ TauCeti.LinearPMap.resolventSet
      (TauCeti.LinearPMap.unitaryConj W A.toLinearPMap) ↔
    z ∈ TauCeti.LinearPMap.resolventSet A.toLinearPMap
  exact mem_resolventSet_unitaryConj_iff W A.toLinearPMap

/-- The conjugated DK operator is self-adjoint. -/
theorem unitaryConjugate_isSelfAdjoint
    (W : H ≃ₗᵢ[ℂ] K) (A : DKClosedOperator (H := H))
    (hA : A.IsSelfAdjoint) : (unitaryConjugate W A hA).IsSelfAdjoint := by
  change IsSelfAdjoint (TauCeti.LinearPMap.unitaryConj W A.toLinearPMap)
  exact TauCeti.LinearPMap.isSelfAdjoint_unitaryConj hA

/-- The real spectrum is invariant under unitary conjugation. -/
theorem unitaryConjugate_spectrum_eq
    (W : H ≃ₗᵢ[ℂ] K) (A : DKClosedOperator (H := H))
    (hA : A.IsSelfAdjoint) :
    TauCeti.LinearPMap.spectrum (unitaryConjugate W A hA).toLinearPMap =
      TauCeti.LinearPMap.spectrum A.toLinearPMap := by
  ext lam
  change ((lam : ℂ) ∉ TauCeti.LinearPMap.resolventSet
      (unitaryConjugate W A hA).toLinearPMap) ↔
    ((lam : ℂ) ∉ TauCeti.LinearPMap.resolventSet A.toLinearPMap)
  exact not_congr (mem_resolventSet_unitaryConjugate_iff W A hA)

/-- Restriction of an ambient unitary to a submodule and its transported
image.  This same-ambient-space form is exactly what reflection transport
needs; it does not impose completeness on an arbitrary submodule. -/
noncomputable def submoduleMapIsometry
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (W : E ≃ₗᵢ[ℂ] E) (U : Submodule ℂ E) :
    U ≃ₗᵢ[ℂ] U.map (W.toLinearEquiv : E →ₗ[ℂ] E) where
  toLinearEquiv := W.toLinearEquiv.submoduleMap U
  norm_map' x := by
    have hcoe :
        (((W.toLinearEquiv.submoduleMap U x :
          U.map (W.toLinearEquiv : E →ₗ[ℂ] E)) : E)) = W (x : E) := rfl
    rw [show ‖W.toLinearEquiv.submoduleMap U x‖ =
        ‖((W.toLinearEquiv.submoduleMap U x :
          U.map (W.toLinearEquiv : E →ₗ[ℂ] E)) : E)‖ from rfl,
      hcoe, W.norm_map]
    rfl

/-- The induced submodule isometry acts as the underlying map. -/
@[simp] theorem submoduleMapIsometry_coe_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (W : E ≃ₗᵢ[ℂ] E) (U : Submodule ℂ E) (x : U) :
    ((submoduleMapIsometry W U x :
      U.map (W.toLinearEquiv : E →ₗ[ℂ] E)) : E) = W (x : E) := rfl

/-- Its inverse acts as the inverse map. -/
@[simp] theorem submoduleMapIsometry_symm_coe_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (W : E ≃ₗᵢ[ℂ] E) (U : Submodule ℂ E)
    (x : U.map (W.toLinearEquiv : E →ₗ[ℂ] E)) :
    (((submoduleMapIsometry W U).symm x : U) : E) = W.symm (x : E) := rfl


end SpectraBridge
end Experimental
end DavisKahan
end TauCeti
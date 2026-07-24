/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Interop.Spectra.ReflectionRestriction

/-!
# Unbounded sine two theta

The main theorem reflects the exact operator through a genuine spectral
subspace of its bounded perturbation.  The reflected complementary spectral
restriction is a unitary conjugate of the original complementary restriction,
so the accepted unbounded sine-theta theorem applies without introducing a
second functional calculus.  Reflection geometry then identifies the overlap
block with the complex sine-two-angle operator.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace SpectraBridge

open TauCeti.DavisKahanExt
open TauCeti.DavisKahan.Experimental.ExactSinTheta

universe v

variable {H : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The ambient projection product for the reflected complementary subspace
has the norm of the complex sine-two-angle operator. -/
theorem norm_starProjection_reflectedComplementary_eq_sinTwoAngle
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖U.starProjection ∘L
        (Uᗮ.map (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)).starProjection‖ =
      ‖sinTwoAngleOperatorC U V‖ := by
  let W := U.map (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)
  have hperpProjection :
      Wᗮ.starProjection =
        boundedUnitaryConjugate V.reflection Uᗮ.starProjection := by
    ext x
    rw [Submodule.starProjection_orthogonal_apply,
      boundedUnitaryConjugate_apply,
      Submodule.starProjection_orthogonal_apply, map_sub,
      V.reflection.apply_symm_apply, Submodule.starProjection_map_apply]
  have hmapProjection :
      (Uᗮ.map (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)).starProjection =
        Wᗮ.starProjection := by
    calc
      (Uᗮ.map
          (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)).starProjection =
          boundedUnitaryConjugate V.reflection Uᗮ.starProjection :=
        starProjection_map_unitary Uᗮ V.reflection
      _ = Wᗮ.starProjection := hperpProjection.symm
  rw [hmapProjection]
  calc
    ‖U.starProjection ∘L Wᗮ.starProjection‖ =
        ‖(U.starProjection ∘L Wᗮ.starProjection).adjoint‖ := by
      symm
      exact ContinuousLinearMap.adjoint.norm_map _
    _ = ‖Wᗮ.starProjection ∘L U.starProjection‖ := by
      rw [ContinuousLinearMap.adjoint_comp,
        ← ContinuousLinearMap.star_eq_adjoint,
        ← ContinuousLinearMap.star_eq_adjoint,
        (isSelfAdjoint_starProjection Wᗮ).star_eq,
        (isSelfAdjoint_starProjection U).star_eq]
    _ = directedGap U W := rfl
    _ = subspaceGap U W :=
      (subspaceGap_eq_directedGap_reflection U V).symm
    _ = ‖sinTwoAngleOperatorC U V‖ :=
      subspaceGap_map_reflection_eq_norm_sinTwoAngle U V

/-- The complementary overlap with the reflected complementary subspace is
exactly the norm of the sine-two-angle operator. -/
theorem norm_reflectedComplementaryOverlap_eq_sinTwoAngle
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    [CompleteSpace U] :
    ‖U.subtypeL.adjoint ∘L
        (Uᗮ.map (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)).subtypeL‖ =
      ‖sinTwoAngleOperatorC U V‖ := by
  rw [norm_adjoint_subtypeL_comp_subtypeL_eq U
    (Uᗮ.map (V.reflection.toLinearEquiv : H →ₗ[ℂ] H))]
  exact norm_starProjection_reflectedComplementary_eq_sinTwoAngle U V

/-- Residual reflection form of the unbounded sine-two-theta theorem.  The
bounded operator `R` is required to implement reflection of `A` on its full
domain. -/
theorem sinTwoTheta_reflectionResidual_of_spectrum_gap
    (A : DKClosedOperator (H := H)) (hA : A.IsSelfAdjoint)
    (R : H →L[ℂ] H) (hR : IsSelfAdjointOperator R)
    (B : Set ℝ) (hB : MeasurableSet B)
    (V : Submodule ℂ H) [V.HasOrthogonalProjection]
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hBlow : SemiboundedBelow
      (selfAdjointSpectralRestriction A hA B hB) β)
    (hBhigh : SemiboundedAbove
      (selfAdjointSpectralRestriction A hA B hB) α)
    (hBcomplSpec : ∀ lam ∈ Set.Ioo (β - δ) (α + δ),
      lam ∉ Spectra.Resolvent.spectrum
        (selfAdjointSpectralRestriction A hA Bᶜ hB.compl).toLinearPMap)
    (hJdom : ∀ x : A.domain, V.reflectionOperator (x : H) ∈ A.domain)
    (hJintertwines : ∀ x : A.domain,
      (A.addBounded R).toLinearMap
          ⟨V.reflectionOperator (x : H), hJdom x⟩ =
        V.reflectionOperator (A.toLinearMap x)) :
    δ * ‖sinTwoAngleOperatorC
        (selfAdjointSpectralSubspace A hA B hB) V‖ ≤ ‖R‖ := by
  let U := selfAdjointSpectralSubspace A hA B hB
  let Uc := selfAdjointSpectralSubspace A hA Bᶜ hB.compl
  let Wc := Uc.map (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)
  let A₀ := selfAdjointSpectralRestriction A hA B hB
  let Λ := selfAdjointSpectralRestriction A hA Bᶜ hB.compl
  let hA₀ : A₀.IsSelfAdjoint :=
    selfAdjointSpectralRestriction_isSelfAdjoint A hA B hB
  let hΛ : Λ.IsSelfAdjoint :=
    selfAdjointSpectralRestriction_isSelfAdjoint A hA Bᶜ hB.compl
  letI : Wc.HasOrthogonalProjection := by
    dsimp [Wc]
    infer_instance
  letI : CompleteSpace Wc :=
    (Wc.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  let e : Uc ≃ₗᵢ[ℂ] Wc := submoduleMapIsometry V.reflection Uc
  let ΛJ := unitaryConjugate e Λ hΛ
  let hΛJ : ΛJ.IsSelfAdjoint := unitaryConjugate_isSelfAdjoint e Λ hΛ
  let X : U →L[ℂ] H := U.subtypeL
  let F₁ : Wc →L[ℂ] H := Wc.subtypeL
  have hXdom : ∀ x : A₀.domain, X (x : U) ∈ A.domain :=
    selfAdjointSpectralRestriction_inclusion_mem_domain A hA B hB
  have hXint : ∀ x : A₀.domain,
      A.toLinearMap ⟨X (x : U), hXdom x⟩ = X (A₀.toLinearMap x) :=
    selfAdjointSpectralRestriction_inclusion_intertwines A hA B hB
  have hFdom : ∀ y : ΛJ.domain, F₁ (y : Wc) ∈ A.domain := by
    intro y
    have hyConj : (y : Wc) ∈ (unitaryConjugate e Λ hΛ).domain := by
      simpa only [ΛJ] using y.property
    have hyΛ : e.symm (y : Wc) ∈ Λ.domain :=
      (mem_unitaryConjugate_domain_iff e Λ hΛ).mp hyConj
    let z : Λ.domain := ⟨e.symm (y : Wc), hyΛ⟩
    have hzdom : (((z : Uc) : H)) ∈ A.domain :=
      selfAdjointSpectralRestriction_inclusion_mem_domain
        A hA Bᶜ hB.compl z
    let za : A.domain := ⟨((z : Uc) : H), hzdom⟩
    have hy : (y : H) = V.reflectionOperator (za : H) := by
      symm
      calc
        V.reflectionOperator (za : H) =
            ((e (e.symm (y : Wc)) : Wc) : H) := rfl
        _ = (y : H) := congrArg Subtype.val (e.apply_symm_apply (y : Wc))
    change (y : H) ∈ A.domain
    rw [hy]
    exact hJdom za
  have hFint : ∀ y : ΛJ.domain,
      (A.addBounded R).toLinearMap ⟨F₁ (y : Wc), hFdom y⟩ =
        F₁ (ΛJ.toLinearMap y) := by
    intro y
    have hyConj : (y : Wc) ∈ (unitaryConjugate e Λ hΛ).domain := by
      simpa only [ΛJ] using y.property
    have hyΛ : e.symm (y : Wc) ∈ Λ.domain :=
      (mem_unitaryConjugate_domain_iff e Λ hΛ).mp hyConj
    let z : Λ.domain := ⟨e.symm (y : Wc), hyΛ⟩
    have hzdom : (((z : Uc) : H)) ∈ A.domain :=
      selfAdjointSpectralRestriction_inclusion_mem_domain
        A hA Bᶜ hB.compl z
    let za : A.domain := ⟨((z : Uc) : H), hzdom⟩
    have hy : (y : H) = V.reflectionOperator (za : H) := by
      symm
      calc
        V.reflectionOperator (za : H) =
            ((e (e.symm (y : Wc)) : Wc) : H) := rfl
        _ = (y : H) := congrArg Subtype.val (e.apply_symm_apply (y : Wc))
    have hsub :
        (⟨F₁ (y : Wc), hFdom y⟩ : (A.addBounded R).domain) =
          ⟨V.reflectionOperator (za : H), hJdom za⟩ :=
      Subtype.ext hy
    have hAint := selfAdjointSpectralRestriction_inclusion_intertwines
      A hA Bᶜ hB.compl z
    have hright :
        V.reflectionOperator (A.toLinearMap za) =
          F₁ (ΛJ.toLinearMap y) := by
      change V.reflectionOperator (A.toLinearMap za) =
        ((ΛJ.toLinearMap y : Wc) : H)
      calc
        V.reflectionOperator (A.toLinearMap za) =
            V.reflectionOperator (((Λ.toLinearMap z : Uc) : H)) :=
          congrArg V.reflectionOperator hAint
        _ = ((e (Λ.toLinearMap z) : Wc) : H) := by
          rfl
        _ = ((ΛJ.toLinearMap y : Wc) : H) := by
          exact congrArg Subtype.val
            (unitaryConjugate_apply e Λ hΛ y).symm
    calc
      (A.addBounded R).toLinearMap ⟨F₁ (y : Wc), hFdom y⟩ =
          (A.addBounded R).toLinearMap
            ⟨V.reflectionOperator (za : H), hJdom za⟩ := by
        exact congrArg (fun q : (A.addBounded R).domain =>
          (A.addBounded R).toLinearMap q) hsub
      _ = V.reflectionOperator (A.toLinearMap za) := hJintertwines za
      _ = F₁ (ΛJ.toLinearMap y) := hright
  have hXiso : IsometricEmbedding X := by
    intro x
    rfl
  have hFiso : IsometricEmbedding F₁ := by
    intro y
    rfl
  have hΛJspec : ∀ lam ∈ Set.Ioo (β - δ) (α + δ),
      lam ∉ Spectra.Resolvent.spectrum ΛJ.toLinearPMap := by
    intro lam hlam
    rw [unitaryConjugate_spectrum_eq e Λ hΛ]
    exact hBcomplSpec lam hlam
  have hraw := sinTheta_addBounded_opNorm_of_spectrum_gap_isometric
    A hA R hR A₀ hA₀ ΛJ hΛJ X F₁ hXdom hXint hFdom hFint
    hXiso hFiso hβα hδ hBlow hBhigh hΛJspec
  change δ * ‖U.subtypeL.adjoint ∘L Wc.subtypeL‖ ≤ ‖R‖ at hraw
  have hrawProjection :
      δ * ‖U.starProjection ∘L Wc.starProjection‖ ≤ ‖R‖ := by
    rw [← norm_adjoint_subtypeL_comp_subtypeL_eq U Wc]
    exact hraw
  have hUcProjection : Uc.starProjection = Uᗮ.starProjection := by
    rw [← selfAdjointSpectralProjection_eq_starProjection
      A hA Bᶜ hB.compl]
    change Spectra.QuantumMechanics.SpectralTheory.spectralProjection
        (Spectra.YosidaHille.genToGroup hA) Bᶜ hB.compl =
      Uᗮ.starProjection
    rw [Spectra.QuantumMechanics.SpectralTheory.spectralProjection_compl
      (Spectra.YosidaHille.genToGroup hA) B hB]
    change ContinuousLinearMap.id ℂ H -
        selfAdjointSpectralProjection A hA B hB = Uᗮ.starProjection
    rw [selfAdjointSpectralProjection_eq_starProjection A hA B hB]
    exact (Submodule.starProjection_orthogonal' U).symm
  have hWcProjection : Wc.starProjection =
      (Uᗮ.map (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)).starProjection := by
    calc
      Wc.starProjection =
          boundedUnitaryConjugate V.reflection Uc.starProjection :=
        starProjection_map_unitary Uc V.reflection
      _ = boundedUnitaryConjugate V.reflection Uᗮ.starProjection := by
        rw [hUcProjection]
      _ = (Uᗮ.map
          (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)).starProjection :=
        (starProjection_map_unitary Uᗮ V.reflection).symm
  have hgeometry :=
    norm_starProjection_reflectedComplementary_eq_sinTwoAngle U V
  calc
    δ * ‖sinTwoAngleOperatorC U V‖ =
        δ * ‖U.starProjection ∘L
          (Uᗮ.map
            (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)).starProjection‖ := by
      rw [hgeometry]
    _ = δ * ‖U.starProjection ∘L Wc.starProjection‖ := by
      rw [hWcProjection]
    _ ≤ ‖R‖ := hrawProjection

/-- Canonical complex operator-norm unbounded sine-two-theta theorem for a
bounded self-adjoint perturbation. -/
theorem sinTwoTheta_addBounded_of_spectrum_gap
    (A : DKClosedOperator (H := H)) (hA : A.IsSelfAdjoint)
    (E : H →L[ℂ] H) (hE : IsSelfAdjointOperator E)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hBlow : SemiboundedBelow
      (selfAdjointSpectralRestriction A hA B hB) β)
    (hBhigh : SemiboundedAbove
      (selfAdjointSpectralRestriction A hA B hB) α)
    (hBcomplSpec : ∀ lam ∈ Set.Ioo (β - δ) (α + δ),
      lam ∉ Spectra.Resolvent.spectrum
        (selfAdjointSpectralRestriction A hA Bᶜ hB.compl).toLinearPMap) :
    δ * ‖sinTwoAngleOperatorC
        (selfAdjointSpectralSubspace A hA B hB)
        (selfAdjointSpectralSubspace (A.addBounded E)
          (addBounded_isSelfAdjoint A hA E hE) S hS)‖ ≤
      2 * ‖E‖ := by
  let C := A.addBounded E
  let hC : C.IsSelfAdjoint := addBounded_isSelfAdjoint A hA E hE
  let V := selfAdjointSpectralSubspace C hC S hS
  let D := reflectionPerturbation V E
  have hD : IsSelfAdjointOperator D :=
    reflectionPerturbation_isSelfAdjoint V E hE
  have hmain :
      δ * ‖sinTwoAngleOperatorC
        (selfAdjointSpectralSubspace A hA B hB) V‖ ≤ ‖D‖ :=
    sinTwoTheta_reflectionResidual_of_spectrum_gap
      A hA D hD B hB V hβα hδ hBlow hBhigh hBcomplSpec
      (perturbedSpectralReflection_mem_domain A hA E hE S hS)
      (add_reflectionPerturbation_intertwines A hA E hE S hS)
  exact hmain.trans (norm_reflectionPerturbation_le V E)

/-- Set-localized form of the canonical complex unbounded sine-two-theta
theorem. -/
theorem sinTwoTheta_addBounded_of_intervalExterior
    (A : DKClosedOperator (H := H)) (hA : A.IsSelfAdjoint)
    (E : H →L[ℂ] H) (hE : IsSelfAdjointOperator E)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hBsub : B ⊆ Set.Icc β α)
    (hBcomplDisj : Bᶜ ∩ Set.Ioo (β - δ) (α + δ) = ∅) :
    δ * ‖sinTwoAngleOperatorC
        (selfAdjointSpectralSubspace A hA B hB)
        (selfAdjointSpectralSubspace (A.addBounded E)
          (addBounded_isSelfAdjoint A hA E hE) S hS)‖ ≤
      2 * ‖E‖ := by
  obtain ⟨hBlow, hBhigh⟩ :=
    selfAdjointSpectralRestriction_semibounded_of_subset_Icc
      A hA B hB hBsub
  have hBcomplSpec :=
    selfAdjointSpectralRestriction_spectrum_avoids_open_of_inter_eq_empty
      A hA Bᶜ hB.compl hBcomplDisj
  exact sinTwoTheta_addBounded_of_spectrum_gap
    A hA E hE B S hB hS hβα hδ hBlow hBhigh hBcomplSpec

end SpectraBridge
end Experimental
end DavisKahan
end TauCeti
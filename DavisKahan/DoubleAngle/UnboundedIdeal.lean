/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.OperatorIdeal.ApproximationNumbers.ScalarGeneric
import DavisKahan.OperatorIdeal.CanonicalRealView
import DavisKahan.DoubleAngle.Unbounded
import DavisKahan.SinTheta.BoundedPerturbationIdeal
import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent

/-!
# Ideal-gauge unbounded sine two theta

The rectangular ideal interface naturally controls the reflected
complementary overlap block.  Its operator norm is exactly the norm of the
complex sine-two-angle operator, while its ideal gauge remains meaningful for
families whose rectangular source and target spaces differ.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace Experimental

open TauCeti.DavisKahanExt
open TauCeti.DavisKahan.Experimental.ExactSinTheta

universe v

variable {H : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The ambient sine-two-theta ideal block obtained by overlapping the exact
spectral subspace with the reflected exact complementary subspace. -/
noncomputable def sinTwoThetaIdealBlock
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : H →L[ℂ] H :=
  U.starProjection ∘L
    (Uᗮ.map (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)).starProjection

/-- The operator norm of the ambient ideal block is exactly the norm of sine
of twice the complex operator angle. -/
theorem norm_sinTwoThetaIdealBlock
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖sinTwoThetaIdealBlock U V‖ = ‖sinTwoAngleOperatorC U V‖ := by
  exact norm_starProjection_reflectedComplementary_eq_sinTwoAngle U V

/-- A rectangular overlap block controls the corresponding ambient projection
product in every rectangular symmetric ideal family. -/
theorem projectionProduct_mem_and_gauge_le_overlap
    (N : TauCeti.SymmetricOperatorIdealFamily.{0, v} ℂ)
    [N.toOperatorIdealFamily.IsComplete]
    (U W : Submodule ℂ H)
    [U.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    [CompleteSpace U] [CompleteSpace W]
    (hT : N.Mem (U.subtypeL.adjoint ∘L W.subtypeL)) :
    N.Mem (U.starProjection ∘L W.starProjection) ∧
      N.gaugeReal (U.starProjection ∘L W.starProjection) ≤
        N.gaugeReal (U.subtypeL.adjoint ∘L W.subtypeL) := by
  let T : W →L[ℂ] U := U.subtypeL.adjoint ∘L W.subtypeL
  have hfactor :
      U.starProjection ∘L W.starProjection =
        U.subtypeL ∘L T ∘L W.subtypeL.adjoint := by
    ext x
    dsimp [T]
    rw [Submodule.adjoint_subtypeL, Submodule.adjoint_subtypeL]
    change U.starProjection (W.starProjection x) =
      U.starProjection (W.starProjection x)
    rfl
  have hmemFactor : N.Mem (U.subtypeL ∘L T ∘L W.subtypeL.adjoint) :=
    N.comp_mem U.subtypeL W.subtypeL.adjoint hT
  have hUiso : IsometricEmbedding U.subtypeL := by
    intro x
    rfl
  have hWiso : IsometricEmbedding W.subtypeL := by
    intro x
    rfl
  have hUnorm : ‖U.subtypeL‖ ≤ 1 := opNorm_le_one_of_isometry hUiso
  have hWadjNorm : ‖W.subtypeL.adjoint‖ ≤ 1 := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact opNorm_le_one_of_isometry hWiso
  refine ⟨?_, ?_⟩
  · rw [hfactor]
    exact hmemFactor
  · rw [hfactor]
    have hgauge := N.gaugeReal_comp_le U.subtypeL W.subtypeL.adjoint hT
    have hnonneg := N.gaugeReal_nonneg hT
    calc
      N.gaugeReal (U.subtypeL ∘L T ∘L W.subtypeL.adjoint) ≤
          ‖U.subtypeL‖ * N.gaugeReal T * ‖W.subtypeL.adjoint‖ := hgauge
      _ ≤ 1 * N.gaugeReal T * ‖W.subtypeL.adjoint‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hUnorm hnonneg)
          (norm_nonneg W.subtypeL.adjoint)
      _ ≤ 1 * N.gaugeReal T * 1 := by
        exact mul_le_mul_of_nonneg_left hWadjNorm
          (mul_nonneg zero_le_one hnonneg)
      _ = N.gaugeReal (U.subtypeL.adjoint ∘L W.subtypeL) := by
        dsimp [T]
        ring

/-- The bounded reflection residual remains in every rectangular symmetric
ideal containing the perturbation, with gauge cost at most two. -/
theorem reflectionPerturbation_mem_and_gauge_le
    (N : TauCeti.SymmetricOperatorIdealFamily.{0, v} ℂ)
    [N.toOperatorIdealFamily.IsComplete]
    (V : Submodule ℂ H) [V.HasOrthogonalProjection]
    (E : H →L[ℂ] H) (hEmem : N.Mem E) :
    N.Mem (reflectionPerturbation V E) ∧
      N.gaugeReal (reflectionPerturbation V E) ≤ 2 * N.gaugeReal E := by
  let W : H →L[ℂ] H :=
    V.reflection.toLinearIsometry.toContinuousLinearMap
  let W' : H →L[ℂ] H :=
    V.reflection.symm.toLinearIsometry.toContinuousLinearMap
  have hWiso : IsometricEmbedding W := by
    intro x
    exact V.reflection.norm_map x
  have hW'iso : IsometricEmbedding W' := by
    intro x
    exact V.reflection.symm.norm_map x
  have hconjMem : N.Mem (boundedUnitaryConjugate V.reflection E) := by
    change N.Mem (W ∘L E ∘L W')
    exact N.comp_mem W W' hEmem
  have hconjGauge :
      N.gaugeReal (boundedUnitaryConjugate V.reflection E) ≤ N.gaugeReal E := by
    change N.gaugeReal (W ∘L E ∘L W') ≤ N.gaugeReal E
    exact N.gaugeReal_comp_le_of_contractions W W' hEmem
      (opNorm_le_one_of_isometry hWiso)
      (opNorm_le_one_of_isometry hW'iso)
  refine ⟨?_, ?_⟩
  · unfold reflectionPerturbation
    exact N.sub_mem hEmem hconjMem
  · unfold reflectionPerturbation
    have hsub := N.gaugeReal_sub_le hEmem hconjMem
    calc
      N.gaugeReal (E - boundedUnitaryConjugate V.reflection E) ≤
          N.gaugeReal E + N.gaugeReal (boundedUnitaryConjugate V.reflection E) := hsub
      _ ≤ N.gaugeReal E + N.gaugeReal E :=
        add_le_add le_rfl hconjGauge
      _ = 2 * N.gaugeReal E := by ring

/-- Residual reflection form of unbounded sine two theta at rectangular
ideal-gauge scope. -/
theorem sinTwoTheta_reflectionResidual_gauge_of_spectrum_gap
    (N : TauCeti.SymmetricOperatorIdealFamily.{0, v} ℂ)
    [N.toOperatorIdealFamily.IsComplete]
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
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum
        (selfAdjointSpectralRestriction A hA Bᶜ hB.compl).toLinearPMap)
    (hJdom : ∀ x : A.domain, V.reflectionOperator (x : H) ∈ A.domain)
    (hJintertwines : ∀ x : A.domain,
      (A.addBounded R).toLinearMap
          ⟨V.reflectionOperator (x : H), hJdom x⟩ =
        V.reflectionOperator (A.toLinearMap x))
    (hRmem : N.Mem R) :
    N.Mem (sinTwoThetaIdealBlock
        (selfAdjointSpectralSubspace A hA B hB) V) ∧
      δ * N.gaugeReal (sinTwoThetaIdealBlock
        (selfAdjointSpectralSubspace A hA B hB) V) ≤ N.gaugeReal R := by
  let U := selfAdjointSpectralSubspace A hA B hB
  let Uc := selfAdjointSpectralSubspace A hA Bᶜ hB.compl
  let Wc := Uc.map (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)
  let A₀ := selfAdjointSpectralRestriction A hA B hB
  let Λ := selfAdjointSpectralRestriction A hA Bᶜ hB.compl
  let hA₀ : A₀.IsSelfAdjoint :=
    selfAdjointSpectralRestriction_isSelfAdjoint A hA B hB
  let hΛ : Λ.IsSelfAdjoint :=
    selfAdjointSpectralRestriction_isSelfAdjoint A hA Bᶜ hB.compl
  letI : U.HasOrthogonalProjection :=
    selfAdjointSpectralSubspace_hasOrthogonalProjection A hA B hB
  letI : CompleteSpace U :=
    (U.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
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
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum ΛJ.toLinearPMap := by
    intro lam hlam
    rw [unitaryConjugate_spectrum_eq e Λ hΛ]
    exact hBcomplSpec lam hlam
  have hraw := sinTheta_addBounded_gauge_of_spectrum_gap_isometric
    N A hA R hR A₀ hA₀ ΛJ hΛJ X F₁ hXdom hXint hFdom hFint
      hXiso hFiso hβα hδ hBlow hBhigh hΛJspec hRmem
  change
    N.Mem (U.subtypeL.adjoint ∘L Wc.subtypeL) ∧
      δ * N.gaugeReal (U.subtypeL.adjoint ∘L Wc.subtypeL) ≤ N.gaugeReal R at hraw
  have hambient := projectionProduct_mem_and_gauge_le_overlap
    N U Wc hraw.1
  have hUcProjection : Uc.starProjection = Uᗮ.starProjection := by
    rw [← selfAdjointSpectralProjection_eq_starProjection
      A hA Bᶜ hB.compl]
    rw [show selfAdjointSpectralProjection A hA Bᶜ hB.compl
          = ContinuousLinearMap.id ℂ H - selfAdjointSpectralProjection A hA B hB from
        (TauCeti.LinearPMap.spectralPVM hA).proj_compl B hB]
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
  have hblock :
      sinTwoThetaIdealBlock U V =
        U.starProjection ∘L Wc.starProjection := by
    unfold sinTwoThetaIdealBlock
    rw [hWcProjection]
  rw [hblock]
  refine ⟨hambient.1, ?_⟩
  calc
    δ * N.gaugeReal (U.starProjection ∘L Wc.starProjection) ≤
        δ * N.gaugeReal (U.subtypeL.adjoint ∘L Wc.subtypeL) :=
      mul_le_mul_of_nonneg_left hambient.2 hδ.le
    _ ≤ N.gaugeReal R := hraw.2

/-- Canonical bounded-perturbation unbounded sine-two-theta theorem at
rectangular ideal-gauge scope. -/
theorem sinTwoTheta_addBounded_gauge_of_spectrum_gap
    (N : TauCeti.SymmetricOperatorIdealFamily.{0, v} ℂ)
    [N.toOperatorIdealFamily.IsComplete]
    (A : DKClosedOperator (H := H)) (hA : A.IsSelfAdjoint)
    (E : H →L[ℂ] H) (hE : IsSelfAdjointOperator E)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hBlow : SemiboundedBelow
      (selfAdjointSpectralRestriction A hA B hB) β)
    (hBhigh : SemiboundedAbove
      (selfAdjointSpectralRestriction A hA B hB) α)
    (hBcomplSpec : ∀ lam ∈ Set.Ioo (β - δ) (α + δ),
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum
        (selfAdjointSpectralRestriction A hA Bᶜ hB.compl).toLinearPMap)
    (hEmem : N.Mem E) :
    N.Mem (sinTwoThetaIdealBlock
        (selfAdjointSpectralSubspace A hA B hB)
        (selfAdjointSpectralSubspace (A.addBounded E)
          (addBounded_isSelfAdjoint A hA E hE) S hS)) ∧
      δ * N.gaugeReal (sinTwoThetaIdealBlock
        (selfAdjointSpectralSubspace A hA B hB)
        (selfAdjointSpectralSubspace (A.addBounded E)
          (addBounded_isSelfAdjoint A hA E hE) S hS)) ≤
        2 * N.gaugeReal E := by
  let C := A.addBounded E
  let hC : C.IsSelfAdjoint := addBounded_isSelfAdjoint A hA E hE
  let V := selfAdjointSpectralSubspace C hC S hS
  let D := reflectionPerturbation V E
  have hD : IsSelfAdjointOperator D :=
    reflectionPerturbation_isSelfAdjoint V E hE
  have hDideal := reflectionPerturbation_mem_and_gauge_le N V E hEmem
  have hmain := sinTwoTheta_reflectionResidual_gauge_of_spectrum_gap
    N A hA D hD B hB V hβα hδ hBlow hBhigh hBcomplSpec
      (perturbedSpectralReflection_mem_domain A hA E hE S hS)
      (add_reflectionPerturbation_intertwines A hA E hE S hS)
      hDideal.1
  refine ⟨hmain.1, hmain.2.trans ?_⟩
  exact hDideal.2

/-- Set-localized canonical ideal-gauge form of unbounded sine two theta. -/
theorem sinTwoTheta_addBounded_gauge_of_intervalExterior
    (N : TauCeti.SymmetricOperatorIdealFamily.{0, v} ℂ)
    [N.toOperatorIdealFamily.IsComplete]
    (A : DKClosedOperator (H := H)) (hA : A.IsSelfAdjoint)
    (E : H →L[ℂ] H) (hE : IsSelfAdjointOperator E)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hBsub : B ⊆ Set.Icc β α)
    (hBcomplDisj : Bᶜ ∩ Set.Ioo (β - δ) (α + δ) = ∅)
    (hEmem : N.Mem E) :
    N.Mem (sinTwoThetaIdealBlock
        (selfAdjointSpectralSubspace A hA B hB)
        (selfAdjointSpectralSubspace (A.addBounded E)
          (addBounded_isSelfAdjoint A hA E hE) S hS)) ∧
      δ * N.gaugeReal (sinTwoThetaIdealBlock
        (selfAdjointSpectralSubspace A hA B hB)
        (selfAdjointSpectralSubspace (A.addBounded E)
          (addBounded_isSelfAdjoint A hA E hE) S hS)) ≤
        2 * N.gaugeReal E := by
  obtain ⟨hBlow, hBhigh⟩ :=
    selfAdjointSpectralRestriction_semibounded_of_subset_Icc
      A hA B hB hBsub
  have hBcomplSpec :=
    selfAdjointSpectralRestriction_spectrum_avoids_open_of_inter_eq_empty
      A hA Bᶜ hB.compl hBcomplDisj
  exact sinTwoTheta_addBounded_gauge_of_spectrum_gap
    N A hA E hE B S hB hS hβα hδ hBlow hBhigh hBcomplSpec hEmem


/-- Source-facing unitary-invariant-family wrapper for the spectrum-gap ideal
form. -/
theorem sinTwoTheta_addBounded_unitaryInvariant_of_spectrum_gap
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (A : DKClosedOperator (H := H)) (hA : A.IsSelfAdjoint)
    (E : H →L[ℂ] H) (hE : IsSelfAdjointOperator E)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hBlow : SemiboundedBelow
      (selfAdjointSpectralRestriction A hA B hB) β)
    (hBhigh : SemiboundedAbove
      (selfAdjointSpectralRestriction A hA B hB) α)
    (hBcomplSpec : ∀ lam ∈ Set.Ioo (β - δ) (α + δ),
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum
        (selfAdjointSpectralRestriction A hA Bᶜ hB.compl).toLinearPMap)
    (hEmem : N.Mem E) :
    N.Mem (sinTwoThetaIdealBlock
        (selfAdjointSpectralSubspace A hA B hB)
        (selfAdjointSpectralSubspace (A.addBounded E)
          (addBounded_isSelfAdjoint A hA E hE) S hS)) ∧
      δ * N.gauge (sinTwoThetaIdealBlock
        (selfAdjointSpectralSubspace A hA B hB)
        (selfAdjointSpectralSubspace (A.addBounded E)
          (addBounded_isSelfAdjoint A hA E hE) S hS)) ≤
        2 * N.gauge E := by
  exact sinTwoTheta_addBounded_gauge_of_spectrum_gap
    N.toSymmetricOperatorIdealFamily A hA E hE B S hB hS
      hβα hδ hBlow hBhigh hBcomplSpec hEmem

/-- Source-facing unitary-invariant-family wrapper for the set-localized ideal
form. -/
theorem sinTwoTheta_addBounded_unitaryInvariant_of_intervalExterior
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (A : DKClosedOperator (H := H)) (hA : A.IsSelfAdjoint)
    (E : H →L[ℂ] H) (hE : IsSelfAdjointOperator E)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hBsub : B ⊆ Set.Icc β α)
    (hBcomplDisj : Bᶜ ∩ Set.Ioo (β - δ) (α + δ) = ∅)
    (hEmem : N.Mem E) :
    N.Mem (sinTwoThetaIdealBlock
        (selfAdjointSpectralSubspace A hA B hB)
        (selfAdjointSpectralSubspace (A.addBounded E)
          (addBounded_isSelfAdjoint A hA E hE) S hS)) ∧
      δ * N.gauge (sinTwoThetaIdealBlock
        (selfAdjointSpectralSubspace A hA B hB)
        (selfAdjointSpectralSubspace (A.addBounded E)
          (addBounded_isSelfAdjoint A hA E hE) S hS)) ≤
        2 * N.gauge E := by
  exact sinTwoTheta_addBounded_gauge_of_intervalExterior
    N.toSymmetricOperatorIdealFamily A hA E hE B S hB hS
      hβα hδ hBsub hBcomplDisj hEmem

/-- Residual reflection form of the unbounded sine-two-theta theorem, operator norm.  The
bounded operator `R` is required to implement reflection of `A` on its full domain.

This is `sinTwoTheta_reflectionResidual_gauge_of_spectrum_gap` read at the operator-norm
family, where membership is vacuous and the gauge is the norm; the geometric spine is proved
once, above. -/
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
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum
        (selfAdjointSpectralRestriction A hA Bᶜ hB.compl).toLinearPMap)
    (hJdom : ∀ x : A.domain, V.reflectionOperator (x : H) ∈ A.domain)
    (hJintertwines : ∀ x : A.domain,
      (A.addBounded R).toLinearMap
          ⟨V.reflectionOperator (x : H), hJdom x⟩ =
        V.reflectionOperator (A.toLinearMap x)) :
    δ * ‖sinTwoAngleOperatorC
        (selfAdjointSpectralSubspace A hA B hB) V‖ ≤ ‖R‖ := by
  have h := (sinTwoTheta_reflectionResidual_gauge_of_spectrum_gap
    (TauCeti.operatorNormFamily ℂ) A hA R hR B hB V hβα hδ
    hBlow hBhigh hBcomplSpec hJdom hJintertwines
    (TauCeti.SymmetricOperatorIdealFamily.mem_operatorNormFamily R)).2
  rwa [TauCeti.SymmetricOperatorIdealFamily.gaugeReal_operatorNormFamily,
    TauCeti.SymmetricOperatorIdealFamily.gaugeReal_operatorNormFamily,
    norm_sinTwoThetaIdealBlock] at h

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
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum
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

end Experimental
end DavisKahan
end TauCeti
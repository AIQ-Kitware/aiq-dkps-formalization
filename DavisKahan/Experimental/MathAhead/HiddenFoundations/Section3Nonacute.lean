/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.Experimental.MathAhead.Section3Elementary
import DavisKahan.Experimental.Frontier.Section3
import DavisKahan.Experimental.MathAhead.HiddenFoundations.PolarIsometryFinal
import DavisKahan.Experimental.MathAhead.HiddenFoundations.PolarIntertwining
import Spectra.QuantumMechanics.Channels.TraceClass.PartialIsometry

/-!
# Nonacute direct rotations from crossed-defect data

For two projections, the canonical polar factor is the direct rotation on the
orthogonal complement of the two crossed defect spaces and vanishes on those
defects.  A unitary identification of the crossed defects supplies the missing
quarter-turn.  Adding the two orthogonal blocks gives the nonacute direct
rotation of Davis--Kahan Proposition 3.2.

This file keeps the construction operator-valued.  Equality of Hilbert
cardinals enters only through the existence of the linear isometric equivalence
between the crossed defects.
-/

open scoped InnerProductSpace

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace MathAhead
namespace HiddenFoundations

open SpectraBridge
open Frontier

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
  [V.HasOrthogonalProjection]

private theorem projection_mul_projection_eq_zero_of_le_orthogonal
    (K L : Submodule ℂ H) [K.HasOrthogonalProjection]
    [L.HasOrthogonalProjection] (hKL : K ≤ Lᗮ) :
    projection L * projection K = 0 := by
  ext x
  have hxK : projection K x ∈ K := K.starProjection_apply_mem x
  have hxOrth : projection K x ∈ Lᗮ := hKL hxK
  rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.zero_apply,
    Submodule.starProjection_apply_eq_zero_iff]
  exact hxOrth

private theorem projection_mul_projection_eq_zero_of_ge_orthogonal
    (K L : Submodule ℂ H) [K.HasOrthogonalProjection]
    [L.HasOrthogonalProjection] (hKL : K ≤ Lᗮ) :
    projection K * projection L = 0 := by
  have hLK : L ≤ Kᗮ := by
    intro x hx y hy
    exact inner_eq_zero_symm.mp (hKL hy x hx)
  exact projection_mul_projection_eq_zero_of_le_orthogonal L K hLK

/-- Orthogonal sum of the two crossed defect spaces. -/
noncomputable def crossedDefectSum : Submodule ℂ H :=
  halmosSourceDefect U V ⊔ halmosTargetDefect U V

noncomputable instance crossedDefectSum_hasOrthogonalProjection :
    (crossedDefectSum U V).HasOrthogonalProjection :=
  hasOrthogonalProjection_sup_of_le_orthogonal
    (halmosSourceDefect U V) (halmosTargetDefect U V)
    (halmosSourceDefect_le_targetDefect_orthogonal U V)

/-- Projection onto the crossed-defect block. -/
noncomputable def crossedDefectProjection : H →L[ℂ] H :=
  projection (crossedDefectSum U V)

/-- Projection onto the regular block complementary to the crossed defects. -/
noncomputable def regularProjection : H →L[ℂ] H :=
  complementaryProjection (crossedDefectSum U V)

/-- Inclusion--transport--projection operator from the source defect to the
target defect. -/
noncomputable def sourceToTargetDefect
    (J : halmosSourceDefect U V ≃ₗᵢ[ℂ] halmosTargetDefect U V) :
    H →L[ℂ] H :=
  (halmosTargetDefect U V).subtypeL ∘L
    J.toContinuousLinearEquiv.toContinuousLinearMap ∘L
      (halmosSourceDefect U V).orthogonalProjectionOnto

/-- Reverse inclusion--transport--projection operator. -/
noncomputable def targetToSourceDefect
    (J : halmosSourceDefect U V ≃ₗᵢ[ℂ] halmosTargetDefect U V) :
    H →L[ℂ] H :=
  (halmosSourceDefect U V).subtypeL ∘L
    J.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
      (halmosTargetDefect U V).orthogonalProjectionOnto

/-- Quarter-turn on the crossed defect block, zero on its orthogonal
complement.  It maps source defect to target defect and target defect to the
negative source defect. -/
noncomputable def crossedDefectQuarterTurn
    (J : halmosSourceDefect U V ≃ₗᵢ[ℂ] halmosTargetDefect U V) :
    H →L[ℂ] H :=
  sourceToTargetDefect U V J - targetToSourceDefect U V J

@[simp]
theorem sourceToTargetDefect_apply_source
    (J : halmosSourceDefect U V ≃ₗᵢ[ℂ] halmosTargetDefect U V)
    (x : halmosSourceDefect U V) :
    sourceToTargetDefect U V J (x : H) = (J x : H) := by
  simp [sourceToTargetDefect,
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]

@[simp]
theorem targetToSourceDefect_apply_target
    (J : halmosSourceDefect U V ≃ₗᵢ[ℂ] halmosTargetDefect U V)
    (y : halmosTargetDefect U V) :
    targetToSourceDefect U V J (y : H) = (J.symm y : H) := by
  simp [targetToSourceDefect,
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]

@[simp]
theorem sourceToTargetDefect_apply_target
    (J : halmosSourceDefect U V ≃ₗᵢ[ℂ] halmosTargetDefect U V)
    (y : halmosTargetDefect U V) :
    sourceToTargetDefect U V J (y : H) = 0 := by
  have hy : (y : H) ∈ (halmosSourceDefect U V)ᗮ :=
    Submodule.orthogonal_le (halmosSourceDefect_le_targetDefect_orthogonal U V)
      (Submodule.le_orthogonal_orthogonal _ y.property)
  simp [sourceToTargetDefect,
    Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr hy]

@[simp]
theorem targetToSourceDefect_apply_source
    (J : halmosSourceDefect U V ≃ₗᵢ[ℂ] halmosTargetDefect U V)
    (x : halmosSourceDefect U V) :
    targetToSourceDefect U V J (x : H) = 0 := by
  have hx : (x : H) ∈ (halmosTargetDefect U V)ᗮ :=
    halmosSourceDefect_le_targetDefect_orthogonal U V x.property
  simp [targetToSourceDefect,
    Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr hx]

@[simp]
theorem crossedDefectQuarterTurn_apply_source
    (J : halmosSourceDefect U V ≃ₗᵢ[ℂ] halmosTargetDefect U V)
    (x : halmosSourceDefect U V) :
    crossedDefectQuarterTurn U V J (x : H) = (J x : H) := by
  simp [crossedDefectQuarterTurn]

@[simp]
theorem crossedDefectQuarterTurn_apply_target
    (J : halmosSourceDefect U V ≃ₗᵢ[ℂ] halmosTargetDefect U V)
    (y : halmosTargetDefect U V) :
    crossedDefectQuarterTurn U V J (y : H) = -(J.symm y : H) := by
  simp [crossedDefectQuarterTurn]

/-- The quarter-turn vanishes on the regular block. -/
theorem crossedDefectQuarterTurn_apply_regular
    (J : halmosSourceDefect U V ≃ₗᵢ[ℂ] halmosTargetDefect U V)
    {x : H} (hx : x ∈ (crossedDefectSum U V)ᗮ) :
    crossedDefectQuarterTurn U V J x = 0 := by
  have hxS : x ∈ (halmosSourceDefect U V)ᗮ :=
    Submodule.orthogonal_le le_sup_left hx
  have hxT : x ∈ (halmosTargetDefect U V)ᗮ :=
    Submodule.orthogonal_le le_sup_right hx
  simp [crossedDefectQuarterTurn, sourceToTargetDefect,
    targetToSourceDefect,
    Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr hxS,
    Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr hxT]

/-- The two directional defect transports are adjoints. -/
theorem star_sourceToTargetDefect
    (J : halmosSourceDefect U V ≃ₗᵢ[ℂ] halmosTargetDefect U V) :
    star (sourceToTargetDefect U V J) = targetToSourceDefect U V J := by
  refine ContinuousLinearMap.ext fun x => ?_
  refine ext_inner_left ℂ fun y => ?_
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  simp only [sourceToTargetDefect, targetToSourceDefect,
    ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rw [← Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left,
    ← Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right,
    LinearIsometryEquiv.inner_map_eq_flip]

/-- The crossed-defect quarter-turn is skew-adjoint. -/
theorem star_crossedDefectQuarterTurn
    (J : halmosSourceDefect U V ≃ₗᵢ[ℂ] halmosTargetDefect U V) :
    star (crossedDefectQuarterTurn U V J) =
      -crossedDefectQuarterTurn U V J := by
  rw [crossedDefectQuarterTurn, star_sub, star_sourceToTargetDefect U V J]
  have h2 : star (targetToSourceDefect U V J) = sourceToTargetDefect U V J := by
    rw [← star_sourceToTargetDefect U V J, star_star]
  rw [h2]
  abel

/-- Initial and final projection of the defect quarter-turn. -/
theorem star_crossedDefectQuarterTurn_mul_self
    (J : halmosSourceDefect U V ≃ₗᵢ[ℂ] halmosTargetDefect U V) :
    star (crossedDefectQuarterTurn U V J) *
        crossedDefectQuarterTurn U V J =
      crossedDefectProjection U V := by
  apply ContinuousLinearMap.ext
  intro x
  obtain ⟨d, hd, hdperp⟩ :=
    Submodule.HasOrthogonalProjection.exists_orthogonal
      (K := crossedDefectSum U V) x
  obtain ⟨r, hr, hxr⟩ : ∃ r ∈ (crossedDefectSum U V)ᗮ, x = d + r :=
    ⟨x - d, hdperp, by abel⟩
  obtain ⟨s, hs, t, ht, rfl⟩ :
      ∃ s ∈ halmosSourceDefect U V, ∃ t ∈ halmosTargetDefect U V, s + t = d :=
    Submodule.mem_sup.mp hd
  have hQr : crossedDefectQuarterTurn U V J r = 0 :=
    crossedDefectQuarterTurn_apply_regular U V J hr
  have hQx : crossedDefectQuarterTurn U V J x =
      (J ⟨s, hs⟩ : H) - (J.symm ⟨t, ht⟩ : H) := by
    rw [hxr, map_add, map_add, hQr, add_zero,
      show crossedDefectQuarterTurn U V J s = (J ⟨s, hs⟩ : H) from
        crossedDefectQuarterTurn_apply_source U V J ⟨s, hs⟩,
      show crossedDefectQuarterTurn U V J t = -(J.symm ⟨t, ht⟩ : H) from
        crossedDefectQuarterTurn_apply_target U V J ⟨t, ht⟩,
      ← sub_eq_add_neg]
  have hQQx : crossedDefectQuarterTurn U V J
      (crossedDefectQuarterTurn U V J x) = -(s + t) := by
    rw [hQx, map_sub,
      crossedDefectQuarterTurn_apply_target U V J (J ⟨s, hs⟩),
      crossedDefectQuarterTurn_apply_source U V J (J.symm ⟨t, ht⟩),
      LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.apply_symm_apply]
    show -(s : H) - (t : H) = -(s + t)
    abel
  have hproj : crossedDefectProjection U V x = s + t := by
    rw [crossedDefectProjection, hxr, map_add,
      (Submodule.starProjection_apply_eq_zero_iff _).mpr hr, add_zero]
    exact Submodule.starProjection_eq_self_iff.mpr
      (Submodule.mem_sup.mpr ⟨s, hs, t, ht, rfl⟩)
  rw [ContinuousLinearMap.mul_apply, star_crossedDefectQuarterTurn,
    ContinuousLinearMap.neg_apply, hQQx, neg_neg, hproj]

/-- The canonical intertwiner vanishes on the source defect. -/
theorem canonicalIntertwiner_apply_sourceDefect_eq_zero
    (x : halmosSourceDefect U V) :
    spectraCanonicalIntertwiner U V (x : H) = 0 := by
  obtain ⟨hPx, hQperpx⟩ := mem_halmosSourceDefect.mp x.property
  have hP : projection U (x : H) = x :=
    Submodule.starProjection_eq_self_iff.mpr hPx
  have hQ : projection V (x : H) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff _).mpr hQperpx
  have hPc : complementaryProjection U (x : H) = 0 := by
    simp [complementaryProjection, hP]
  simp [spectraCanonicalIntertwiner, hP, hQ, hPc]

/-- The canonical intertwiner vanishes on the target defect. -/
theorem canonicalIntertwiner_apply_targetDefect_eq_zero
    (x : halmosTargetDefect U V) :
    spectraCanonicalIntertwiner U V (x : H) = 0 := by
  obtain ⟨hPperpx, hQx⟩ := mem_halmosTargetDefect.mp x.property
  have hP : projection U (x : H) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff _).mpr hPperpx
  have hPc : complementaryProjection U (x : H) = x := by
    simp [complementaryProjection, hP]
  have hQc : complementaryProjection V (x : H) = 0 := by
    have hQ : projection V (x : H) = x :=
      Submodule.starProjection_eq_self_iff.mpr hQx
    simp [complementaryProjection, hQ]
  simp [spectraCanonicalIntertwiner, hP, hPc, hQc]

/-- The kernel of the canonical intertwiner is exactly the crossed-defect sum. -/
theorem ker_canonicalIntertwiner_eq_crossedDefectSum :
    LinearMap.ker (spectraCanonicalIntertwiner U V).toLinearMap =
      crossedDefectSum U V := by
  ext x
  constructor
  · intro hx
    have hzero := congrArg (fun y => ‖y‖ * ‖y‖) hx
    have horth :
        ⟪projection V (projection U x),
          complementaryProjection V (complementaryProjection U x)⟫_ℂ = 0 := by
      exact Submodule.inner_right_of_mem_orthogonal
        (V.starProjection_apply_mem _) (Vᗮ.starProjection_apply_mem _)
    have hsumzero :
        projection V (projection U x) = 0 ∧
        complementaryProjection V (complementaryProjection U x) = 0 := by
      have hsquares :=
        norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
      rw [spectraCanonicalIntertwiner, ContinuousLinearMap.coe_coe,
        ContinuousLinearMap.add_apply,
        ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply] at hzero
      rw [hsquares] at hzero
      exact (add_eq_zero_iff_of_nonneg (mul_self_nonneg _) (mul_self_nonneg _)).mp
          (by simpa using hzero)
        |>.imp (fun h => by simpa [mul_self_eq_zero] using h)
               (fun h => by simpa [mul_self_eq_zero] using h)
    let s : H := projection U x
    let t : H := complementaryProjection U x
    have hsU : s ∈ U := U.starProjection_apply_mem x
    have hsVperp : s ∈ Vᗮ :=
      (Submodule.starProjection_apply_eq_zero_iff _).mp hsumzero.1
    have htUperp : t ∈ Uᗮ := Uᗮ.starProjection_apply_mem x
    have htV : t ∈ V := by
      have hmem : t ∈ (Vᗮ)ᗮ :=
        (Submodule.starProjection_apply_eq_zero_iff _).mp hsumzero.2
      rwa [V.orthogonal_orthogonal] at hmem
    have hs : s ∈ halmosSourceDefect U V :=
      mem_halmosSourceDefect.mpr ⟨hsU, hsVperp⟩
    have ht : t ∈ halmosTargetDefect U V :=
      mem_halmosTargetDefect.mpr ⟨htUperp, htV⟩
    have hsplit : x = s + t := by
      exact (U.starProjection_add_starProjection_orthogonal x).symm
    rw [hsplit]
    exact Submodule.mem_sup.mpr ⟨s, hs, t, ht, rfl⟩
  · intro hx
    rcases Submodule.mem_sup.mp hx with ⟨s, hs, t, ht, rfl⟩
    refine LinearMap.mem_ker.mpr ?_
    simp only [ContinuousLinearMap.coe_coe, map_add,
      canonicalIntertwiner_apply_sourceDefect_eq_zero U V ⟨s, hs⟩,
      canonicalIntertwiner_apply_targetDefect_eq_zero U V ⟨t, ht⟩, add_zero]

/-- The polar initial space is the regular block. -/
theorem polarRange_canonicalIntertwiner_eq_regular :
    Spectra.QuantumMechanics.Channels.polarRange
        (spectraCanonicalIntertwiner U V) =
      (crossedDefectSum U V)ᗮ := by
  have hker : LinearMap.ker (Spectra.QuantumMechanics.Channels.absOp
      (spectraCanonicalIntertwiner U V)).toLinearMap = crossedDefectSum U V := by
    rw [← ker_canonicalIntertwiner_eq_crossedDefectSum U V]
    ext y
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    constructor
    · intro hy
      have hn := Spectra.QuantumMechanics.Channels.norm_absOp_apply
        (spectraCanonicalIntertwiner U V) y
      rw [hy, norm_zero, eq_comm, norm_eq_zero] at hn
      exact hn
    · intro hy
      have hn := Spectra.QuantumMechanics.Channels.norm_absOp_apply
        (spectraCanonicalIntertwiner U V) y
      rw [hy, norm_zero, norm_eq_zero] at hn
      exact hn
  rw [Spectra.QuantumMechanics.Channels.polarRange,
    ← Submodule.orthogonal_orthogonal_eq_closure,
    ContinuousLinearMap.orthogonal_range,
    ← ContinuousLinearMap.star_eq_adjoint,
    (Spectra.QuantumMechanics.Channels.absOp_isSelfAdjoint
      (spectraCanonicalIntertwiner U V)).star_eq,
    hker]

/-- The canonical polar factor vanishes on the crossed defect block. -/
theorem canonicalPolarFactor_apply_crossedDefect_eq_zero
    {x : H} (hx : x ∈ crossedDefectSum U V) :
    spectraCanonicalPolarFactor U V x = 0 := by
  rw [spectraCanonicalPolarFactor, spectraPolarIsometry,
    Spectra.QuantumMechanics.Channels.polarIsometry_apply_eq]
  have hxperp : x ∈ (Spectra.QuantumMechanics.Channels.polarRange
      (spectraCanonicalIntertwiner U V))ᗮ := by
    rw [polarRange_canonicalIntertwiner_eq_regular U V]
    exact Submodule.le_orthogonal_orthogonal (crossedDefectSum U V) hx
  rw [show (Spectra.QuantumMechanics.Channels.polarRange
      (spectraCanonicalIntertwiner U V)).orthogonalProjection x = 0 from
    Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr hxperp, map_zero]

/-- The final range of the canonical intertwiner is the regular block. -/
theorem polarFinalRange_canonicalIntertwiner_eq_regular :
    Spectra.QuantumMechanics.Channels.polarFinalRange
        (spectraCanonicalIntertwiner U V) =
      (crossedDefectSum U V)ᗮ := by
  rw [Spectra.QuantumMechanics.Channels.polarFinalRange,
    ← Submodule.orthogonal_orthogonal_eq_closure,
    ContinuousLinearMap.orthogonal_range,
    ← ContinuousLinearMap.star_eq_adjoint,
    star_spectraCanonicalIntertwiner,
    ker_canonicalIntertwiner_eq_crossedDefectSum V U]
  congr 1
  simp only [crossedDefectSum, halmosSourceDefect, halmosTargetDefect,
    inf_comm, sup_comm]

/-- The polar factor has both initial and final projection equal to the regular
projection. -/
theorem canonicalPolarFactor_initial_final_projection :
    star (spectraCanonicalPolarFactor U V) *
        spectraCanonicalPolarFactor U V = regularProjection U V ∧
    spectraCanonicalPolarFactor U V *
        star (spectraCanonicalPolarFactor U V) = regularProjection U V := by
  constructor
  · have h := Spectra.QuantumMechanics.Channels.polarIsometry_adjoint_comp_self
      (spectraCanonicalIntertwiner U V)
    simp only [polarRange_canonicalIntertwiner_eq_regular U V] at h
    rw [ContinuousLinearMap.star_eq_adjoint]
    exact h
  · have h := Spectra.QuantumMechanics.Channels.polarIsometry_comp_adjoint_self
      (spectraCanonicalIntertwiner U V)
    simp only [polarFinalRange_canonicalIntertwiner_eq_regular U V] at h
    rw [ContinuousLinearMap.star_eq_adjoint]
    exact h

/-- The polar factor maps the regular block into itself. -/
theorem canonicalPolarFactor_mem_regular (x : H) :
    spectraCanonicalPolarFactor U V x ∈ (crossedDefectSum U V)ᗮ := by
  rw [← polarFinalRange_canonicalIntertwiner_eq_regular U V]
  exact Spectra.QuantumMechanics.Channels.polarPartial_mem_finalRange
    (spectraCanonicalIntertwiner U V)
    ((Spectra.QuantumMechanics.Channels.polarRange
      (spectraCanonicalIntertwiner U V)).orthogonalProjection x)

/-- The canonical polar factor and defect quarter-turn have orthogonal initial
and final blocks. -/
theorem canonicalPolarFactor_orthogonal_defectQuarterTurn
    (J : halmosSourceDefect U V ≃ₗᵢ[ℂ] halmosTargetDefect U V) :
    star (spectraCanonicalPolarFactor U V) * crossedDefectQuarterTurn U V J = 0 ∧
    star (crossedDefectQuarterTurn U V J) * spectraCanonicalPolarFactor U V = 0 ∧
    spectraCanonicalPolarFactor U V * star (crossedDefectQuarterTurn U V J) = 0 ∧
    crossedDefectQuarterTurn U V J * star (spectraCanonicalPolarFactor U V) = 0 := by
  have hfirst : star (spectraCanonicalPolarFactor U V) *
      crossedDefectQuarterTurn U V J = 0 := by
    ext x
    rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.zero_apply,
      ContinuousLinearMap.star_eq_adjoint]
    refine ext_inner_right ℂ fun y => ?_
    rw [ContinuousLinearMap.adjoint_inner_left, inner_zero_left]
    have hrange : crossedDefectQuarterTurn U V J x ∈ crossedDefectSum U V := by
      let s := (halmosSourceDefect U V).orthogonalProjectionOnto x
      let t := (halmosTargetDefect U V).orthogonalProjectionOnto x
      refine Submodule.mem_sup.mpr
        ⟨-(J.symm t : H), Submodule.neg_mem _ (J.symm t).property,
          (J s : H), (J s).property, ?_⟩
      simp [crossedDefectQuarterTurn, sourceToTargetDefect,
        targetToSourceDefect, s, t]
      abel
    have hyreg := canonicalPolarFactor_mem_regular U V y
    exact Submodule.inner_right_of_mem_orthogonal hrange hyreg
  have hsecond : star (crossedDefectQuarterTurn U V J) *
      spectraCanonicalPolarFactor U V = 0 := by
    have h := congrArg star hfirst
    simpa [star_mul] using h
  have hthird : spectraCanonicalPolarFactor U V *
      star (crossedDefectQuarterTurn U V J) = 0 := by
    rw [star_crossedDefectQuarterTurn]
    ext x
    have hrange : crossedDefectQuarterTurn U V J x ∈ crossedDefectSum U V := by
      let s := (halmosSourceDefect U V).orthogonalProjectionOnto x
      let t := (halmosTargetDefect U V).orthogonalProjectionOnto x
      refine Submodule.mem_sup.mpr
        ⟨-(J.symm t : H), Submodule.neg_mem _ (J.symm t).property,
          (J s : H), (J s).property, ?_⟩
      simp [crossedDefectQuarterTurn, sourceToTargetDefect,
        targetToSourceDefect, s, t]
      abel
    simp [ContinuousLinearMap.mul_apply,
      canonicalPolarFactor_apply_crossedDefect_eq_zero U V hrange]
  have hfourth : crossedDefectQuarterTurn U V J *
      star (spectraCanonicalPolarFactor U V) = 0 := by
    have h := congrArg star hthird
    simpa [star_mul] using h
  exact ⟨hfirst, hsecond, hthird, hfourth⟩

/-- The quarter-turn has the same initial and final defect projection. -/
theorem crossedDefectQuarterTurn_mul_star_self
    (J : halmosSourceDefect U V ≃ₗᵢ[ℂ] halmosTargetDefect U V) :
    crossedDefectQuarterTurn U V J *
        star (crossedDefectQuarterTurn U V J) = crossedDefectProjection U V := by
  have hinit := star_crossedDefectQuarterTurn_mul_self U V J
  rw [star_crossedDefectQuarterTurn] at hinit ⊢
  rw [mul_neg, ← neg_mul]
  exact hinit

/-- The canonical polar factor intertwines the two projections without an
acuteness assumption. -/
theorem canonicalPolarFactor_intertwines_general :
    spectraCanonicalPolarFactor U V * projection U =
      projection V * spectraCanonicalPolarFactor U V := by
  simpa [ContinuousLinearMap.mul_def] using
    canonicalPolarFactor_intertwines_from_polar U V

/-- Positivity of the source diagonal compression of the canonical partial
polar factor.

Leaf obligation handed to the mathematics agent: this needs the source-block
compression formula `P U * polarFactor * P U = positiveSupportInverse |C| ∘L
(P U * C* * P V * P U)` together with the positive-support inverse of the
canonical absolute value and its quadratic-form nonnegativity
(`positiveSupportInverse`, `source_compression_polar_formula`,
`positiveSupportInverse_quadratic_nonnegative`), none of which exist yet in
Mathlib, Spectra, or this repo. -/
theorem canonicalPolarFactor_sourceCompression_nonnegative (x : H) :
    0 ≤ RCLike.re
      ⟪x, (projection U * spectraCanonicalPolarFactor U V * projection U) x⟫_ℂ :=
  sorry

/-- Positivity of the complementary diagonal compression. -/
theorem canonicalPolarFactor_complementCompression_nonnegative (x : H) :
    0 ≤ RCLike.re
      ⟪x, (complementaryProjection U * spectraCanonicalPolarFactor U V *
        complementaryProjection U) x⟫_ℂ := by
  have hswap : spectraCanonicalPolarFactor Uᗮ Vᗮ = spectraCanonicalPolarFactor U V := by
    have hI : spectraCanonicalIntertwiner Uᗮ Vᗮ = spectraCanonicalIntertwiner U V := by
      simp only [spectraCanonicalIntertwiner, complementaryProjection,
        Submodule.orthogonal_orthogonal]
      abel
    unfold spectraCanonicalPolarFactor
    rw [hI]
  have h := canonicalPolarFactor_sourceCompression_nonnegative Uᗮ Vᗮ x
  rwa [hswap] at h

/-- The crossed blocks of the canonical partial polar factor are
skew-adjoint.

Leaf obligation handed to the mathematics agent: the proof needs the reflection
relation `canonicalPolarFactor_reflection_relation` for the canonical polar
factor (relating `Pᗮ U * polarFactor * P U` to the adjoint of
`P U * polarFactor * Pᗮ U`), which does not exist yet in Mathlib, Spectra, or
this repo. -/
theorem canonicalPolarFactor_crossed_blocks_general :
    complementaryProjection U * spectraCanonicalPolarFactor U V * projection U =
      -star (projection U * spectraCanonicalPolarFactor U V *
        complementaryProjection U) :=
  sorry

/-- The defect quarter-turn has the paper crossed-block relation. -/
theorem crossedDefectQuarterTurn_crossed_blocks
    (J : halmosSourceDefect U V ≃ₗᵢ[ℂ] halmosTargetDefect U V) :
    complementaryProjection U * crossedDefectQuarterTurn U V J * projection U =
      -star (projection U * crossedDefectQuarterTurn U V J *
        complementaryProjection U) := by
  rw [star_mul, star_mul,
    (isSelfAdjoint_starProjection U).star_eq,
    (isSelfAdjoint_starProjection Uᗮ).star_eq,
    star_crossedDefectQuarterTurn]
  noncomm_ring

/-- The nonacute direct-rotation candidate obtained by filling the two defect
spaces with the chosen quarter-turn. -/
noncomputable def nonacuteDirectRotation
    (J : halmosSourceDefect U V ≃ₗᵢ[ℂ] halmosTargetDefect U V) :
    H →L[ℂ] H :=
  spectraCanonicalPolarFactor U V + crossedDefectQuarterTurn U V J

/-- Initial projection identity for the nonacute rotation. -/
theorem star_nonacuteDirectRotation_mul_self
    (J : halmosSourceDefect U V ≃ₗᵢ[ℂ] halmosTargetDefect U V) :
    star (nonacuteDirectRotation U V J) * nonacuteDirectRotation U V J = 1 := by
  have hcross := canonicalPolarFactor_orthogonal_defectQuarterTurn U V J
  rw [nonacuteDirectRotation, star_add]
  rw [add_mul, mul_add, mul_add]
  rw [hcross.1, hcross.2.1,
    star_crossedDefectQuarterTurn_mul_self U V J,
    (canonicalPolarFactor_initial_final_projection U V).1]
  simp [regularProjection, crossedDefectProjection,
    Submodule.starProjection_orthogonal']

/-- Final projection identity for the nonacute rotation. -/
theorem nonacuteDirectRotation_mul_star_self
    (J : halmosSourceDefect U V ≃ₗᵢ[ℂ] halmosTargetDefect U V) :
    nonacuteDirectRotation U V J * star (nonacuteDirectRotation U V J) = 1 := by
  have hcross := canonicalPolarFactor_orthogonal_defectQuarterTurn U V J
  have hpolar := (canonicalPolarFactor_initial_final_projection U V).2
  rw [nonacuteDirectRotation, star_add]
  rw [add_mul, mul_add, mul_add]
  rw [hcross.2.2.1, hcross.2.2.2,
    crossedDefectQuarterTurn_mul_star_self U V J, hpolar]
  simp [regularProjection, crossedDefectProjection,
    Submodule.starProjection_orthogonal']

/-- The completed nonacute rotation is unitary. -/
theorem nonacuteDirectRotation_mem_unitary
    (J : halmosSourceDefect U V ≃ₗᵢ[ℂ] halmosTargetDefect U V) :
    nonacuteDirectRotation U V J ∈ unitary (H →L[ℂ] H) := by
  exact ⟨star_nonacuteDirectRotation_mul_self U V J,
    nonacuteDirectRotation_mul_star_self U V J⟩

/-- The defect quarter-turn intertwines the source and target projections. -/
theorem crossedDefectQuarterTurn_intertwines
    (J : halmosSourceDefect U V ≃ₗᵢ[ℂ] halmosTargetDefect U V) :
    crossedDefectQuarterTurn U V J * projection U =
      projection V * crossedDefectQuarterTurn U V J := by
  ext x
  let s := (halmosSourceDefect U V).orthogonalProjectionOnto x
  let t := (halmosTargetDefect U V).orthogonalProjectionOnto x
  have hVJs : projection V (J s : H) = J s :=
    Submodule.starProjection_eq_self_iff.mpr (J s).property.2
  have hVJt : projection V (J.symm t : H) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff _).mpr (J.symm t).property.2
  have hpS : (halmosSourceDefect U V).orthogonalProjectionOnto (projection U x) = s :=
    Submodule.orthogonalProjectionOnto_starProjection_of_le inf_le_left x
  have hpT : (halmosTargetDefect U V).orthogonalProjectionOnto (projection U x) = 0 := by
    rw [Submodule.orthogonalProjectionOnto_eq_zero_iff]
    exact Submodule.orthogonal_le inf_le_left
      (Submodule.le_orthogonal_orthogonal U (U.starProjection_apply_mem x))
  simp [crossedDefectQuarterTurn, sourceToTargetDefect,
    targetToSourceDefect, s, t, hVJs, hVJt, hpS, hpT]

/-- The completed nonacute rotation intertwines the two projections. -/
theorem nonacuteDirectRotation_intertwines
    (J : halmosSourceDefect U V ≃ₗᵢ[ℂ] halmosTargetDefect U V) :
    nonacuteDirectRotation U V J * projection U =
      projection V * nonacuteDirectRotation U V J := by
  rw [nonacuteDirectRotation, add_mul, mul_add,
    canonicalPolarFactor_intertwines_general,
    crossedDefectQuarterTurn_intertwines]

/-- Positivity of both diagonal compressions of the nonacute construction. -/
theorem nonacuteDirectRotation_compressions_nonnegative
    (J : halmosSourceDefect U V ≃ₗᵢ[ℂ] halmosTargetDefect U V) :
    (∀ x : H, 0 ≤ RCLike.re
      ⟪x, (projection U * nonacuteDirectRotation U V J * projection U) x⟫_ℂ) ∧
    (∀ x : H, 0 ≤ RCLike.re
      ⟪x, (complementaryProjection U * nonacuteDirectRotation U V J *
        complementaryProjection U) x⟫_ℂ) := by
  constructor
  · intro x
    rw [nonacuteDirectRotation, mul_add, add_mul]
    have hdefectZero :
        projection U * crossedDefectQuarterTurn U V J * projection U = 0 := by
      ext y
      simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.zero_apply]
      have hpT : (halmosTargetDefect U V).orthogonalProjectionOnto
          (projection U y) = 0 := by
        rw [Submodule.orthogonalProjectionOnto_eq_zero_iff]
        exact Submodule.orthogonal_le inf_le_left
          (Submodule.le_orthogonal_orthogonal U (U.starProjection_apply_mem y))
      have hval : crossedDefectQuarterTurn U V J (projection U y) =
          (J ((halmosSourceDefect U V).orthogonalProjectionOnto
            (projection U y)) : H) -
          (J.symm ((halmosTargetDefect U V).orthogonalProjectionOnto
            (projection U y)) : H) := by
        simp only [crossedDefectQuarterTurn, sourceToTargetDefect,
          targetToSourceDefect, ContinuousLinearMap.sub_apply,
          ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
          ContinuousLinearEquiv.coe_coe,
          LinearIsometryEquiv.coe_toContinuousLinearEquiv]
      rw [hval, hpT, map_zero, Submodule.coe_zero, sub_zero]
      exact (Submodule.starProjection_apply_eq_zero_iff _).mpr
        (mem_halmosTargetDefect.mp (J _).property).1
    rw [hdefectZero, add_zero]
    exact canonicalPolarFactor_sourceCompression_nonnegative U V x
  · intro x
    rw [nonacuteDirectRotation, mul_add, add_mul]
    have hdefectZero :
        complementaryProjection U * crossedDefectQuarterTurn U V J *
          complementaryProjection U = 0 := by
      ext y
      simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.zero_apply]
      have hpS : (halmosSourceDefect U V).orthogonalProjectionOnto
          (complementaryProjection U y) = 0 := by
        rw [Submodule.orthogonalProjectionOnto_eq_zero_iff]
        exact Submodule.orthogonal_le inf_le_left (Uᗮ.starProjection_apply_mem y)
      have hval : crossedDefectQuarterTurn U V J (complementaryProjection U y) =
          (J ((halmosSourceDefect U V).orthogonalProjectionOnto
            (complementaryProjection U y)) : H) -
          (J.symm ((halmosTargetDefect U V).orthogonalProjectionOnto
            (complementaryProjection U y)) : H) := by
        simp only [crossedDefectQuarterTurn, sourceToTargetDefect,
          targetToSourceDefect, ContinuousLinearMap.sub_apply,
          ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
          ContinuousLinearEquiv.coe_coe,
          LinearIsometryEquiv.coe_toContinuousLinearEquiv]
      rw [hval, hpS, map_zero, Submodule.coe_zero, zero_sub, map_neg, neg_eq_zero]
      exact (Submodule.starProjection_apply_eq_zero_iff _).mpr
        (Submodule.le_orthogonal_orthogonal U
          (mem_halmosSourceDefect.mp (J.symm _).property).1)
    rw [hdefectZero, add_zero]
    exact canonicalPolarFactor_complementCompression_nonnegative U V x

/-- The crossed blocks of the nonacute construction are skew-adjoint. -/
theorem nonacuteDirectRotation_crossed_blocks
    (J : halmosSourceDefect U V ≃ₗᵢ[ℂ] halmosTargetDefect U V) :
    complementaryProjection U * nonacuteDirectRotation U V J * projection U =
      -star (projection U * nonacuteDirectRotation U V J *
        complementaryProjection U) := by
  rw [nonacuteDirectRotation, mul_add, add_mul, mul_add, add_mul,
    star_add, neg_add]
  congr 1
  · exact canonicalPolarFactor_crossed_blocks_general U V
  · exact crossedDefectQuarterTurn_crossed_blocks U V J

/-- The explicit nonacute construction satisfies the paper's direct-rotation
predicate. -/
theorem nonacuteDirectRotation_isPaperDirectRotation
    (J : halmosSourceDefect U V ≃ₗᵢ[ℂ] halmosTargetDefect U V) :
    IsPaperDirectRotation U V (nonacuteDirectRotation U V J) := by
  refine
    { unitary_mem := nonacuteDirectRotation_mem_unitary U V J
      intertwines := nonacuteDirectRotation_intertwines U V J
      source_compression_nonnegative :=
        (nonacuteDirectRotation_compressions_nonnegative U V J).1
      complement_compression_nonnegative :=
        (nonacuteDirectRotation_compressions_nonnegative U V J).2
      crossed_blocks := nonacuteDirectRotation_crossed_blocks U V J }

/-- The chosen defect identification can be recovered from the completed
rotation, so the parameterization is injective. -/
theorem nonacuteDirectRotation_injective :
    Function.Injective
      (nonacuteDirectRotation U V :
        (halmosSourceDefect U V ≃ₗᵢ[ℂ] halmosTargetDefect U V) →
          H →L[ℂ] H) := by
  intro J K hJK
  apply LinearIsometryEquiv.ext
  intro x
  have hx := DFunLike.congr_fun hJK (x : H)
  have hpolar : spectraCanonicalPolarFactor U V (x : H) = 0 :=
    canonicalPolarFactor_apply_crossedDefect_eq_zero U V
      (Submodule.mem_sup.mpr ⟨x, x.property, 0, Submodule.zero_mem _, by simp⟩)
  simpa [nonacuteDirectRotation, hpolar] using hx

/-- Constructive half of Davis--Kahan Proposition 3.2. -/
theorem exists_paperDirectRotation_of_crossedDefectsEquivalent
    (hdefect : CrossedDefectsEquivalent U V) :
    ∃ T : H →L[ℂ] H, IsPaperDirectRotation U V T := by
  rcases hdefect with ⟨J⟩
  exact ⟨nonacuteDirectRotation U V J,
    nonacuteDirectRotation_isPaperDirectRotation U V J⟩

/-- A paper direct rotation restricts to a linear isometric equivalence between
the two crossed defects.

Two of the four membership obligations below are handed to the mathematics
agent: that a paper direct rotation maps the source defect `U ⊓ Vᗮ` into `Uᗮ`
(and dually its adjoint maps the target defect into `Vᗮ`).  These require the
crossed-block/compression structure of `IsPaperDirectRotation`, not merely the
intertwining relation `T * P U = P V * T`, and are not derivable from the API
mechanically available here. -/
noncomputable def crossedDefectEquivOfPaperDirectRotation
    (T : H →L[ℂ] H) (hT : IsPaperDirectRotation U V T) :
    halmosSourceDefect U V ≃ₗᵢ[ℂ] halmosTargetDefect U V where
  toFun x := ⟨T x, by
    rw [mem_halmosTargetDefect]
    constructor
    · sorry
    · have hPx : projection U (x : H) = x :=
        Submodule.starProjection_eq_self_iff.mpr x.property.1
      have h := DFunLike.congr_fun hT.intertwines (x : H)
      rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, hPx] at h
      exact Submodule.starProjection_eq_self_iff.mp h.symm⟩
  invFun y := ⟨star T y, by
    rw [mem_halmosSourceDefect]
    constructor
    · have hstar := congrArg star hT.intertwines
      have hrel : projection U * star T = star T * projection V := by
        simpa [star_mul,
          (isSelfAdjoint_starProjection U).star_eq,
          (isSelfAdjoint_starProjection V).star_eq] using hstar
      have hQy : projection V (y : H) = y :=
        Submodule.starProjection_eq_self_iff.mpr y.property.2
      have h := DFunLike.congr_fun hrel (y : H)
      rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, hQy] at h
      exact Submodule.starProjection_eq_self_iff.mp h
    · sorry⟩
  left_inv x := by
    apply Subtype.ext
    have hunit := hT.unitary_mem
    have hleft : star T * T = 1 := hunit.1
    have h := DFunLike.congr_fun hleft (x : H)
    simpa [ContinuousLinearMap.mul_apply] using h
  right_inv y := by
    apply Subtype.ext
    have hunit := hT.unitary_mem
    have hright : T * star T = 1 := hunit.2
    have h := DFunLike.congr_fun hright (y : H)
    simpa [ContinuousLinearMap.mul_apply] using h
  map_add' x y := by
    apply Subtype.ext
    exact map_add T (x : H) (y : H)
  map_smul' c x := by
    apply Subtype.ext
    exact map_smul T c (x : H)
  norm_map' x := by
    have hunit := hT.unitary_mem
    exact Unitary.norm_map ⟨T, hunit⟩ x

/-- Necessity half of Davis--Kahan Proposition 3.2. -/
theorem crossedDefectsEquivalent_of_exists_paperDirectRotation
    (h : ∃ T : H →L[ℂ] H, IsPaperDirectRotation U V T) :
    CrossedDefectsEquivalent U V := by
  rcases h with ⟨T, hT⟩
  exact ⟨crossedDefectEquivOfPaperDirectRotation U V T hT⟩

/-- Davis--Kahan Proposition 3.2 in constructive Hilbert-dimension form. -/
theorem proposition3_2_completed :
    (∃ T : H →L[ℂ] H, IsPaperDirectRotation U V T) ↔
      CrossedDefectsEquivalent U V := by
  constructor
  · exact crossedDefectsEquivalent_of_exists_paperDirectRotation U V
  · exact exists_paperDirectRotation_of_crossedDefectsEquivalent U V

/-- Explicit injective parameterization of all constructed extensions. -/
theorem proposition3_2_parameterization_completed
    (hdefect : CrossedDefectsEquivalent U V) :
    ∃ build :
        (halmosSourceDefect U V ≃ₗᵢ[ℂ] halmosTargetDefect U V) →
          H →L[ℂ] H,
      (∀ J, IsPaperDirectRotation U V (build J)) ∧
      Function.Injective build := by
  refine ⟨nonacuteDirectRotation U V, ?_,
    nonacuteDirectRotation_injective U V⟩
  intro J
  exact nonacuteDirectRotation_isPaperDirectRotation U V J

end

end HiddenFoundations
end MathAhead
end Experimental
end DavisKahan
end ForMathlib

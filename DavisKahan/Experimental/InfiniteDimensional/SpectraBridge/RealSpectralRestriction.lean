/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.Core.ClosedOperatorComplexification
import DavisKahan.Experimental.InfiniteDimensional.Core.ComplexificationFunctionalCalculus
import DavisKahan.Experimental.InfiniteDimensional.Core.ComplexificationSubspace
import DavisKahan.Experimental.InfiniteDimensional.Core.ReducingRestriction
import DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.SpectralRestrictionOperator
import Spectra.Resolvent.Identities
import Spectra.SpectralTheory.ResolventForm
import Spectra.SpectralTheory.Essential.Weyl

/-!
# Real spectral projections and restrictions by complexification

For a self-adjoint closed operator on a real Hilbert space, this module obtains
its measurable spectral projections from the canonical spectral measure of the
complexified operator.  The key point is that the complexified operator is
real with respect to the canonical conjugation.  Resolvent uniqueness implies
that its spectral measure is fixed by conjugation, so every spectral projection
descends to a bounded real orthogonal projection.

The closed operator on a selected real spectral range is then constructed by
the scalar-generic reducing-restriction API.  Thus the spectral bridge owns
only the genuinely spectral descent; domain density, graph closedness,
self-adjointness, and inclusion intertwining are supplied by the generic core.
-/

open scoped InnerProductSpace ComplexConjugate

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace SpectraBridge
namespace RealSpectralRestriction

open Spectra
open Spectra.Resolvent
open Spectra.YosidaHille
open Spectra.Essential
open Spectra.QuantumMechanics.SpectralTheory
open ExactSinTheta
open ExactSinTheta.ClosedOperatorComplexification
open ExactSinTheta.RealComplexificationFunctionalCalculus
open Foundation
open Foundation.RealComplexification

noncomputable section

universe v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Local notation keeps the ambient real space syntactically visible at every
use site; an abbreviation here would turn `E` into an uninferable implicit
argument in several PVM declarations. -/
local notation "Eℂ" => RealComplexification E
local notation "RealClosedOperator" =>
  ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := ℝ) (E := E)

/-- Conjugate a projection-valued measure by the canonical real-structure
conjugation. -/
noncomputable def conjugatePVM (P : Spectra.ProjValMeasure Eℂ) :
    Spectra.ProjValMeasure Eℂ where
  proj B hB := conjugateOperator (P.proj B hB)
  diag z := P.diag (conjugation z)
  diag_finite z := P.diag_finite (conjugation z)
  inner_proj B hB z := by
    rw [conjugateOperator_apply, inner_conjugation_right]
    calc
      ⟪P.proj B hB (conjugation z), conjugation z⟫_ℂ =
          starRingEnd ℂ
            ⟪conjugation z, P.proj B hB (conjugation z)⟫_ℂ := by
        rw [inner_conj_symm]
      _ = (((P.diag (conjugation z)) B).toReal : ℂ) := by
        rw [P.inner_proj, Complex.conj_ofReal]
  proj_univ := by
    rw [P.proj_univ]
    exact conjugateOperator_one
  proj_inter B₁ B₂ hB₁ hB₂ := by
    rw [← conjugateOperator_mul, P.proj_inter]

@[simp]
theorem conjugatePVM_proj (P : Spectra.ProjValMeasure Eℂ)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (conjugatePVM P).proj B hB = conjugateOperator (P.proj B hB) :=
  rfl

@[simp]
theorem conjugatePVM_diag (P : Spectra.ProjValMeasure Eℂ) (z : Eℂ) :
    (conjugatePVM P).diag z = P.diag (conjugation z) :=
  rfl

/-- Conjugation preserves the coordinatewise complexified operator domain. -/
def conjugationDomain (A : RealClosedOperator)
    (z : (ClosedOperatorComplexification.complexify A).domain) :
    (ClosedOperatorComplexification.complexify A).domain :=
  ⟨conjugation (z : Eℂ), by
    rw [ClosedOperatorComplexification.mem_complexify_domain_iff]
    simpa using
      (ClosedOperatorComplexification.mem_complexify_domain_iff A z).mp z.property⟩

@[simp]
theorem conjugationDomain_coe (A : RealClosedOperator)
    (z : (ClosedOperatorComplexification.complexify A).domain) :
    ((conjugationDomain A z :
      (ClosedOperatorComplexification.complexify A).domain) : Eℂ) =
      conjugation (z : Eℂ) :=
  rfl

/-- The complexified closed operator commutes with canonical conjugation on its
operator domain. -/
theorem complexify_apply_conjugationDomain (A : RealClosedOperator)
    (z : (ClosedOperatorComplexification.complexify A).domain) :
    (ClosedOperatorComplexification.complexify A).toLinearMap
        (conjugationDomain A z) =
      conjugation
        ((ClosedOperatorComplexification.complexify A).toLinearMap z) := by
  refine RealComplexification.ext ?_ ?_
  · rw [ClosedOperatorComplexification.complexify_apply_re,
      RealComplexification.re_conj,
      ClosedOperatorComplexification.complexify_apply_re]
    exact ClosedOperatorComplexification.toLinearMap_congr rfl
  · rw [ClosedOperatorComplexification.complexify_apply_im,
      RealComplexification.im_conj,
      ClosedOperatorComplexification.complexify_apply_im]
    refine (ClosedOperatorComplexification.toLinearMap_congr ?_).trans (map_neg _ _)
    simp [conjugationDomain]

private theorem selfAdjointResolvent_adjoint
    {A : Eℂ →ₗ.[ℂ] Eℂ} (hA : IsSelfAdjoint A)
    (z : ℂ) (hz : z.im ≠ 0) :
    (selfAdjointResolvent hA z hz).adjoint =
      selfAdjointResolvent hA (starRingEnd ℂ z)
        (by simpa only [Complex.conj_im, neg_ne_zero] using hz) := by
  unfold selfAdjointResolvent
  exact resolvent_adjoint
    (isFormalAdjoint_of_isSelfAdjoint hA)
    (isSelfAdjoint_to_surjective hA).1
    (isSelfAdjoint_to_surjective hA).2 z hz

/-- Resolvents of a complexified real self-adjoint operator are exchanged by
canonical conjugation and conjugation of the spectral parameter. -/
theorem conjugateOperator_selfAdjointResolvent
    (A : RealClosedOperator) (hA : A.IsSelfAdjoint)
    (z : ℂ) (hz : z.im ≠ 0) :
    conjugateOperator
        (selfAdjointResolvent
          (ClosedOperatorComplexification.isSelfAdjoint_complexify hA) z hz) =
      selfAdjointResolvent
        (ClosedOperatorComplexification.isSelfAdjoint_complexify hA)
        (starRingEnd ℂ z)
        (by simpa only [Complex.conj_im, neg_ne_zero] using hz) := by
  let Aℂ := ClosedOperatorComplexification.complexify A
  let hAℂ := ClosedOperatorComplexification.isSelfAdjoint_complexify hA
  let zbar := starRingEnd ℂ z
  have hzbar : zbar.im ≠ 0 := by
    simpa [zbar] using hz
  apply ContinuousLinearMap.ext
  intro ξ
  let r : Eℂ := selfAdjointResolvent hAℂ z hz (conjugation ξ)
  have hrdom : r ∈ Aℂ.domain :=
    selfAdjointResolvent_mem_domain hAℂ z hz (conjugation ξ)
  let rDom : Aℂ.domain := ⟨r, hrdom⟩
  let jrDom : Aℂ.domain := conjugationDomain A rDom
  have hsolve :
      (ClosedOperatorComplexification.complexify A).toLinearPMap rDom
          - z • (rDom : Eℂ) = conjugation ξ :=
    selfAdjointResolvent_solves hAℂ z hz (conjugation ξ)
  have happ :
      (ClosedOperatorComplexification.complexify A).toLinearPMap jrDom =
        conjugation
          ((ClosedOperatorComplexification.complexify A).toLinearPMap rDom) :=
    complexify_apply_conjugationDomain A rDom
  have hjsolve :
      (ClosedOperatorComplexification.complexify A).toLinearPMap jrDom
          - zbar • (jrDom : Eℂ) = ξ := by
    have h1 :
        (ClosedOperatorComplexification.complexify A).toLinearPMap jrDom
            - zbar • (jrDom : Eℂ) =
          conjugation
            ((ClosedOperatorComplexification.complexify A).toLinearPMap rDom
              - z • (rDom : Eℂ)) := by
      rw [map_sub, conjugation_complex_smul, ← happ]
      rfl
    rw [h1, hsolve, conjugation_involutive]
  have hleft := selfAdjointResolvent_left_inverse hAℂ zbar hzbar jrDom
  change conjugation
      (selfAdjointResolvent hAℂ z hz (conjugation ξ)) =
    selfAdjointResolvent hAℂ zbar hzbar ξ
  rw [hjsolve] at hleft
  exact hleft.symm

/-- The spectral PVM of a complexified real self-adjoint operator is fixed by
canonical conjugation. -/
theorem conjugatePVM_spectralPVM
    (A : RealClosedOperator) (hA : A.IsSelfAdjoint) :
    conjugatePVM
        (Spectra.QuantumMechanics.SpectralTheory.spectralPVM
          (ClosedOperatorComplexification.isSelfAdjoint_complexify hA)) =
      Spectra.QuantumMechanics.SpectralTheory.spectralPVM
        (ClosedOperatorComplexification.isSelfAdjoint_complexify hA) := by
  let Aℂ := ClosedOperatorComplexification.complexify A
  let hAℂ := ClosedOperatorComplexification.isSelfAdjoint_complexify hA
  let P := Spectra.QuantumMechanics.SpectralTheory.spectralPVM hAℂ
  apply spectralPVM_unique hAℂ (conjugatePVM P)
  intro z hz ξ
  have hzbar : (starRingEnd ℂ z).im ≠ 0 := by
    simpa only [Complex.conj_im, neg_ne_zero] using hz
  have hres := congrArg
    (fun T : Eℂ →L[ℂ] Eℂ => T (conjugation ξ))
    (conjugateOperator_selfAdjointResolvent A hA
      (starRingEnd ℂ z) hzbar)
  have hresPoint :
      selfAdjointResolvent hAℂ z hz (conjugation ξ) =
        conjugation
          (selfAdjointResolvent hAℂ (starRingEnd ℂ z) hzbar ξ) := by
    simpa [Aℂ, hAℂ, conjugateOperator_apply] using hres.symm
  calc
    ⟪ξ, selfAdjointResolvent hAℂ z hz ξ⟫_ℂ =
        ⟪(selfAdjointResolvent hAℂ z hz).adjoint ξ, ξ⟫_ℂ := by
      rw [ContinuousLinearMap.adjoint_inner_left]
    _ = ⟪selfAdjointResolvent hAℂ (starRingEnd ℂ z) hzbar ξ, ξ⟫_ℂ := by
      rw [selfAdjointResolvent_adjoint]
    _ = ⟪conjugation ξ,
          conjugation
            (selfAdjointResolvent hAℂ (starRingEnd ℂ z) hzbar ξ)⟫_ℂ := by
      rw [inner_conjugation]
    _ = ⟪conjugation ξ,
          selfAdjointResolvent hAℂ z hz (conjugation ξ)⟫_ℂ := by
      rw [hresPoint]
    _ = ∫ s, ((s : ℂ) - z)⁻¹ ∂((conjugatePVM P).diag ξ) := by
      change ⟪conjugation ξ,
          selfAdjointResolvent hAℂ z hz (conjugation ξ)⟫_ℂ =
        ∫ s, ((s : ℂ) - z)⁻¹ ∂(P.diag (conjugation ξ))
      exact spectralPVM_resolvent_formula hAℂ z hz (conjugation ξ)

/-- Every measurable spectral projection of a complexified real self-adjoint
operator is fixed by canonical conjugation. -/
theorem conjugateOperator_selfAdjointSpectralProjection
    (A : RealClosedOperator) (hA : A.IsSelfAdjoint)
    (S : Set ℝ) (hS : MeasurableSet S) :
    conjugateOperator
        (selfAdjointSpectralProjection
          (ClosedOperatorComplexification.complexify A)
          (ClosedOperatorComplexification.isSelfAdjoint_complexify hA) S hS) =
      selfAdjointSpectralProjection
        (ClosedOperatorComplexification.complexify A)
        (ClosedOperatorComplexification.isSelfAdjoint_complexify hA) S hS := by
  let hP := conjugatePVM_spectralPVM A hA
  have hproj := congrArg
    (fun P : Spectra.ProjValMeasure Eℂ => P.proj S hS) hP
  exact hproj

/-- The canonical real spectral projection, obtained by descending the complex
spectral projection of the complexified operator. -/
noncomputable def realSelfAdjointSpectralProjection
    (A : RealClosedOperator) (hA : A.IsSelfAdjoint)
    (S : Set ℝ) (hS : MeasurableSet S) : E →L[ℝ] E :=
  realPartOperator
    (selfAdjointSpectralProjection
      (ClosedOperatorComplexification.complexify A)
      (ClosedOperatorComplexification.isSelfAdjoint_complexify hA) S hS)

/-- Complexification of the descended real projection recovers the canonical
complex spectral projection. -/
theorem complexify_realSelfAdjointSpectralProjection
    (A : RealClosedOperator) (hA : A.IsSelfAdjoint)
    (S : Set ℝ) (hS : MeasurableSet S) :
    RealComplexification.complexify
        (realSelfAdjointSpectralProjection A hA S hS) =
      selfAdjointSpectralProjection
        (ClosedOperatorComplexification.complexify A)
        (ClosedOperatorComplexification.isSelfAdjoint_complexify hA) S hS := by
  exact complexify_realPartOperator
    (conjugateOperator_selfAdjointSpectralProjection A hA S hS)

/-- The real spectral projection acts on the real copy exactly as the complex
spectral projection. -/
theorem selfAdjointSpectralProjection_ofReal
    (A : RealClosedOperator) (hA : A.IsSelfAdjoint)
    (S : Set ℝ) (hS : MeasurableSet S) (x : E) :
    selfAdjointSpectralProjection
        (ClosedOperatorComplexification.complexify A)
        (ClosedOperatorComplexification.isSelfAdjoint_complexify hA) S hS
        (ofReal x) =
      ofReal (realSelfAdjointSpectralProjection A hA S hS x) := by
  rw [← complexify_realSelfAdjointSpectralProjection A hA S hS]
  simp

/-- The descended real spectral projection is idempotent. -/
theorem realSelfAdjointSpectralProjection_idem
    (A : RealClosedOperator) (hA : A.IsSelfAdjoint)
    (S : Set ℝ) (hS : MeasurableSet S) :
    realSelfAdjointSpectralProjection A hA S hS *
        realSelfAdjointSpectralProjection A hA S hS =
      realSelfAdjointSpectralProjection A hA S hS := by
  change realSelfAdjointSpectralProjection A hA S hS ∘L
      realSelfAdjointSpectralProjection A hA S hS =
    realSelfAdjointSpectralProjection A hA S hS
  apply RealComplexification.complexify_injective
  rw [RealComplexification.complexify_comp,
    complexify_realSelfAdjointSpectralProjection]
  change selfAdjointSpectralProjection
      (ClosedOperatorComplexification.complexify A)
      (ClosedOperatorComplexification.isSelfAdjoint_complexify hA) S hS *
    selfAdjointSpectralProjection
      (ClosedOperatorComplexification.complexify A)
      (ClosedOperatorComplexification.isSelfAdjoint_complexify hA) S hS = _
  exact (Spectra.QuantumMechanics.SpectralTheory.PVM.spectralPVM
    (ClosedOperatorComplexification.isSelfAdjoint_complexify hA)).proj_idem S hS

/-- The descended real spectral projection is self-adjoint. -/
theorem realSelfAdjointSpectralProjection_isSelfAdjoint
    (A : RealClosedOperator) (hA : A.IsSelfAdjoint)
    (S : Set ℝ) (hS : MeasurableSet S) :
    IsSelfAdjoint (realSelfAdjointSpectralProjection A hA S hS) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  apply RealComplexification.complexify_injective
  rw [RealComplexificationFunctionalCalculus.complexify_adjoint,
    complexify_realSelfAdjointSpectralProjection]
  exact (Spectra.QuantumMechanics.SpectralTheory.PVM.spectralPVM
    (ClosedOperatorComplexification.isSelfAdjoint_complexify hA)).isSelfAdjoint_proj S hS
    |>.adjoint_eq

/-- The real spectral range. -/
noncomputable def realSelfAdjointSpectralSubspace
    (A : RealClosedOperator) (hA : A.IsSelfAdjoint)
    (S : Set ℝ) (hS : MeasurableSet S) : Submodule ℝ E :=
  (realSelfAdjointSpectralProjection A hA S hS).range

@[simp]
theorem realSelfAdjointSpectralSubspace_eq_range
    (A : RealClosedOperator) (hA : A.IsSelfAdjoint)
    (S : Set ℝ) (hS : MeasurableSet S) :
    realSelfAdjointSpectralSubspace A hA S hS =
      (realSelfAdjointSpectralProjection A hA S hS).range :=
  rfl

noncomputable instance realSelfAdjointSpectralSubspace_completeSpace
    (A : RealClosedOperator) (hA : A.IsSelfAdjoint)
    (S : Set ℝ) (hS : MeasurableSet S) :
    CompleteSpace (realSelfAdjointSpectralSubspace A hA S hS) := by
  change CompleteSpace (realSelfAdjointSpectralProjection A hA S hS).range
  exact (ContinuousLinearMap.IsIdempotentElem.isClosed_range
    (realSelfAdjointSpectralProjection_idem A hA S hS)).completeSpace_coe

noncomputable instance realSelfAdjointSpectralSubspace_hasOrthogonalProjection
    (A : RealClosedOperator) (hA : A.IsSelfAdjoint)
    (S : Set ℝ) (hS : MeasurableSet S) :
    (realSelfAdjointSpectralSubspace A hA S hS).HasOrthogonalProjection := by
  change (realSelfAdjointSpectralProjection A hA S hS).range.HasOrthogonalProjection
  exact ContinuousLinearMap.IsIdempotentElem.hasOrthogonalProjection_range
    (show IsIdempotentElem (realSelfAdjointSpectralProjection A hA S hS) from
      realSelfAdjointSpectralProjection_idem A hA S hS)

/-- Every projected vector belongs to the descended real spectral range. -/
theorem realSelfAdjointSpectralProjection_mem_subspace
    (A : RealClosedOperator) (hA : A.IsSelfAdjoint)
    (S : Set ℝ) (hS : MeasurableSet S) (x : E) :
    realSelfAdjointSpectralProjection A hA S hS x ∈
      realSelfAdjointSpectralSubspace A hA S hS :=
  ⟨x, rfl⟩

/-- A vector in the descended real spectral range is fixed by the projection. -/
theorem realSelfAdjointSpectralProjection_eq_self_of_mem
    (A : RealClosedOperator) (hA : A.IsSelfAdjoint)
    (S : Set ℝ) (hS : MeasurableSet S) {x : E}
    (hx : x ∈ realSelfAdjointSpectralSubspace A hA S hS) :
    realSelfAdjointSpectralProjection A hA S hS x = x := by
  rcases hx with ⟨y, rfl⟩
  change realSelfAdjointSpectralProjection A hA S hS
      (realSelfAdjointSpectralProjection A hA S hS y) =
    realSelfAdjointSpectralProjection A hA S hS y
  simpa only [mul_apply_eq_comp] using congrArg
    (fun T : E →L[ℝ] E => T y)
    (realSelfAdjointSpectralProjection_idem A hA S hS)

/-- The descended spectral projection is the orthogonal projection onto its
real range. -/
theorem realSelfAdjointSpectralProjection_eq_starProjection
    (A : RealClosedOperator) (hA : A.IsSelfAdjoint)
    (S : Set ℝ) (hS : MeasurableSet S) :
    realSelfAdjointSpectralProjection A hA S hS =
      (realSelfAdjointSpectralSubspace A hA S hS).starProjection := by
  apply ContinuousLinearMap.ext
  intro x
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact realSelfAdjointSpectralProjection_mem_subspace A hA S hS x
  · intro y hy
    have hyfix := realSelfAdjointSpectralProjection_eq_self_of_mem
      A hA S hS hy
    rw [← hyfix]
    have hadj := ContinuousLinearMap.adjoint_inner_right
      (realSelfAdjointSpectralProjection A hA S hS)
      (x - realSelfAdjointSpectralProjection A hA S hS x) y
    rw [(realSelfAdjointSpectralProjection_isSelfAdjoint A hA S hS).adjoint_eq] at hadj
    rw [hadj, map_sub,
      realSelfAdjointSpectralProjection_eq_self_of_mem A hA S hS
        (realSelfAdjointSpectralProjection_mem_subspace A hA S hS x),
      sub_self, inner_zero_left]

/-- The complexification of the descended real spectral range is exactly the
canonical complex spectral range of the complexified operator.  This is the
consistency theorem that rules out an arbitrary or underspecified real descent. -/
theorem complexifySubmodule_realSelfAdjointSpectralSubspace
    (A : RealClosedOperator) (hA : A.IsSelfAdjoint)
    (S : Set ℝ) (hS : MeasurableSet S) :
    complexifySubmodule (realSelfAdjointSpectralSubspace A hA S hS) =
      selfAdjointSpectralSubspace
        (ClosedOperatorComplexification.complexify A)
        (ClosedOperatorComplexification.isSelfAdjoint_complexify hA) S hS := by
  ext z
  rw [← Submodule.starProjection_eq_self_iff,
    ← Submodule.starProjection_eq_self_iff]
  rw [starProjection_complexifySubmodule,
    ← realSelfAdjointSpectralProjection_eq_starProjection,
    complexify_realSelfAdjointSpectralProjection,
    ← selfAdjointSpectralProjection_eq_starProjection]

/-- Complementation of measurable sets becomes orthogonal complementation of
real spectral ranges. -/
theorem realSelfAdjointSpectralProjection_compl
    (A : RealClosedOperator) (hA : A.IsSelfAdjoint)
    (S : Set ℝ) (hS : MeasurableSet S) :
    realSelfAdjointSpectralProjection A hA Sᶜ hS.compl =
      ContinuousLinearMap.id ℝ E -
        realSelfAdjointSpectralProjection A hA S hS := by
  apply RealComplexification.complexify_injective
  rw [complexify_realSelfAdjointSpectralProjection,
    RealComplexification.complexify_sub,
    RealComplexification.complexify_id,
    complexify_realSelfAdjointSpectralProjection]
  exact spectralProjection_compl
    (genToGroup (ClosedOperatorComplexification.isSelfAdjoint_complexify hA)) S hS

/-- The range selected by the complement set is the orthogonal complement of
the selected real spectral range. -/
theorem realSelfAdjointSpectralSubspace_compl
    (A : RealClosedOperator) (hA : A.IsSelfAdjoint)
    (S : Set ℝ) (hS : MeasurableSet S) :
    realSelfAdjointSpectralSubspace A hA Sᶜ hS.compl =
      (realSelfAdjointSpectralSubspace A hA S hS)ᗮ := by
  apply Submodule.ext
  intro x
  rw [← Submodule.starProjection_eq_self_iff,
    ← Submodule.starProjection_eq_self_iff]
  rw [← realSelfAdjointSpectralProjection_eq_starProjection,
    realSelfAdjointSpectralProjection_compl,
    Submodule.starProjection_orthogonal,
    ← realSelfAdjointSpectralProjection_eq_starProjection]

/-- The real copy of a domain vector has the expected underlying vector. -/
private theorem coe_ofRealDomain (A : RealClosedOperator) (x : A.domain) :
    ((ClosedOperatorComplexification.ofRealDomain A x :
      (ClosedOperatorComplexification.complexify A).domain) : Eℂ) =
      ofReal (x : E) :=
  rfl

omit [CompleteSpace E] in
/-- Orthogonal projections onto equal subspaces agree.  Stated pointwise so it
can be used as a rewrite where a direct `rw` on the subspace would produce an
ill-typed motive (the orthogonal-projection instance depends on it). -/
private theorem starProjection_congr {U V : Submodule ℝ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (h : U = V) (y : E) :
    U.starProjection y = V.starProjection y := by
  subst h
  rfl

/-- The real spectral projection preserves the original real operator domain. -/
theorem realSelfAdjointSpectralProjection_mem_domain
    (A : RealClosedOperator) (hA : A.IsSelfAdjoint)
    {S : Set ℝ} (hS : MeasurableSet S) (x : A.domain) :
    realSelfAdjointSpectralProjection A hA S hS (x : E) ∈ A.domain := by
  have hproj := selfAdjointSpectralProjection_mem_domain
    (ClosedOperatorComplexification.complexify A)
    (ClosedOperatorComplexification.isSelfAdjoint_complexify hA) hS
    (ClosedOperatorComplexification.ofRealDomain A x)
  rw [ClosedOperatorComplexification.mem_complexify_domain_iff] at hproj
  have hre := hproj.1
  rw [coe_ofRealDomain A x, selfAdjointSpectralProjection_ofReal,
    re_ofReal] at hre
  exact hre

/-- The real operator commutes with its descended spectral projections on the
full operator domain. -/
theorem realSelfAdjoint_apply_spectralProjection
    (A : RealClosedOperator) (hA : A.IsSelfAdjoint)
    {S : Set ℝ} (hS : MeasurableSet S) (x : A.domain) :
    A.toLinearMap
        ⟨realSelfAdjointSpectralProjection A hA S hS (x : E),
          realSelfAdjointSpectralProjection_mem_domain A hA hS x⟩ =
      realSelfAdjointSpectralProjection A hA S hS (A.toLinearMap x) := by
  have hcomm := selfAdjoint_apply_spectralProjection
    (ClosedOperatorComplexification.complexify A)
    (ClosedOperatorComplexification.isSelfAdjoint_complexify hA) hS
    (ClosedOperatorComplexification.ofRealDomain A x)
  have hre := congrArg re hcomm
  rw [ClosedOperatorComplexification.complexify_apply_re,
    ClosedOperatorComplexification.complexify_apply_ofReal,
    selfAdjointSpectralProjection_ofReal A hA S hS, re_ofReal] at hre
  refine Eq.trans ?_ hre
  refine ClosedOperatorComplexification.toLinearMap_congr ?_
  show realSelfAdjointSpectralProjection A hA S hS (x : E) =
    re (selfAdjointSpectralProjection
      (ClosedOperatorComplexification.complexify A)
      (ClosedOperatorComplexification.isSelfAdjoint_complexify hA) S hS
      (ofReal (x : E)))
  rw [selfAdjointSpectralProjection_ofReal A hA S hS, re_ofReal]

/-- The real spectral range reduces the original real self-adjoint operator. -/
theorem realSelfAdjointSpectralSubspace_reducing
    (A : RealClosedOperator) (hA : A.IsSelfAdjoint)
    (S : Set ℝ) (hS : MeasurableSet S) :
    A.ReducesSubspace (realSelfAdjointSpectralSubspace A hA S hS) := by
  let U := realSelfAdjointSpectralSubspace A hA S hS
  let Uc := realSelfAdjointSpectralSubspace A hA Sᶜ hS.compl
  have hUc : Uc = Uᗮ := realSelfAdjointSpectralSubspace_compl A hA S hS
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    rw [← realSelfAdjointSpectralProjection_eq_starProjection]
    exact realSelfAdjointSpectralProjection_mem_domain A hA hS x
  · intro x
    have hx := realSelfAdjointSpectralProjection_mem_domain A hA hS.compl x
    rw [realSelfAdjointSpectralProjection_eq_starProjection,
      starProjection_congr hUc] at hx
    exact hx
  · intro x hx
    rw [← Submodule.starProjection_eq_self_iff] at hx ⊢
    rw [← realSelfAdjointSpectralProjection_eq_starProjection] at hx ⊢
    have hcomm := realSelfAdjoint_apply_spectralProjection A hA hS x
    have hsub :
        (⟨realSelfAdjointSpectralProjection A hA S hS (x : E),
          realSelfAdjointSpectralProjection_mem_domain A hA hS x⟩ : A.domain) = x :=
      Subtype.ext hx
    simpa [hsub] using hcomm.symm
  · intro x hx
    rw [← hUc] at hx ⊢
    rw [← Submodule.starProjection_eq_self_iff] at hx ⊢
    rw [← realSelfAdjointSpectralProjection_eq_starProjection] at hx ⊢
    have hcomm := realSelfAdjoint_apply_spectralProjection A hA hS.compl x
    have hsub :
        (⟨realSelfAdjointSpectralProjection A hA Sᶜ hS.compl (x : E),
          realSelfAdjointSpectralProjection_mem_domain A hA hS.compl x⟩ : A.domain) = x :=
      Subtype.ext hx
    simpa [hsub] using hcomm.symm

/-- Canonical inclusion of a real spectral range. -/
noncomputable def realSelfAdjointSpectralSubspaceInclusion
    (A : RealClosedOperator) (hA : A.IsSelfAdjoint)
    (S : Set ℝ) (hS : MeasurableSet S) :
    realSelfAdjointSpectralSubspace A hA S hS →L[ℝ] E :=
  ForMathlib.DavisKahanExt.ClosedOperator.reducingSubspaceInclusion
    (realSelfAdjointSpectralSubspace A hA S hS)

/-- The real spectral-range inclusion is isometric. -/
theorem realSelfAdjointSpectralSubspaceInclusion_isometric
    (A : RealClosedOperator) (hA : A.IsSelfAdjoint)
    (S : Set ℝ) (hS : MeasurableSet S) :
    IsometricEmbedding
      (realSelfAdjointSpectralSubspaceInclusion A hA S hS) :=
  ForMathlib.DavisKahanExt.ClosedOperator.reducingSubspaceInclusion_isometric _

/-- Canonical real closed restriction to a measurable spectral range. -/
noncomputable def realSelfAdjointSpectralRestriction
    (A : RealClosedOperator) (hA : A.IsSelfAdjoint)
    (S : Set ℝ) (hS : MeasurableSet S) :
    ForMathlib.DavisKahanExt.ClosedOperator
      (𝕜 := ℝ) (E := realSelfAdjointSpectralSubspace A hA S hS) :=
  ForMathlib.DavisKahanExt.ClosedOperator.reducingRestriction A
    (realSelfAdjointSpectralSubspace A hA S hS)
    (realSelfAdjointSpectralSubspace_reducing A hA S hS)

/-- The canonical real spectral restriction is self-adjoint. -/
theorem realSelfAdjointSpectralRestriction_isSelfAdjoint
    (A : RealClosedOperator) (hA : A.IsSelfAdjoint)
    (S : Set ℝ) (hS : MeasurableSet S) :
    (realSelfAdjointSpectralRestriction A hA S hS).IsSelfAdjoint := by
  exact ForMathlib.DavisKahanExt.ClosedOperator.reducingRestriction_isSelfAdjoint
    A (realSelfAdjointSpectralSubspace A hA S hS)
    (realSelfAdjointSpectralSubspace_reducing A hA S hS) hA

/-- The real spectral inclusion maps the restricted domain into the ambient
operator domain. -/
theorem realSelfAdjointSpectralRestriction_inclusion_mem_domain
    (A : RealClosedOperator) (hA : A.IsSelfAdjoint)
    (S : Set ℝ) (hS : MeasurableSet S)
    (x : (realSelfAdjointSpectralRestriction A hA S hS).domain) :
    realSelfAdjointSpectralSubspaceInclusion A hA S hS
        (x : realSelfAdjointSpectralSubspace A hA S hS) ∈ A.domain := by
  exact ForMathlib.DavisKahanExt.ClosedOperator.reducingRestriction_inclusion_mem_domain
    A (realSelfAdjointSpectralSubspace A hA S hS)
    (realSelfAdjointSpectralSubspace_reducing A hA S hS) x

/-- The real spectral inclusion intertwines the restricted and ambient closed
operators. -/
theorem realSelfAdjointSpectralRestriction_inclusion_intertwines
    (A : RealClosedOperator) (hA : A.IsSelfAdjoint)
    (S : Set ℝ) (hS : MeasurableSet S)
    (x : (realSelfAdjointSpectralRestriction A hA S hS).domain) :
    A.toLinearMap
        ⟨realSelfAdjointSpectralSubspaceInclusion A hA S hS
            (x : realSelfAdjointSpectralSubspace A hA S hS),
          realSelfAdjointSpectralRestriction_inclusion_mem_domain
            A hA S hS x⟩ =
      realSelfAdjointSpectralSubspaceInclusion A hA S hS
        ((realSelfAdjointSpectralRestriction A hA S hS).toLinearMap x) := by
  exact ForMathlib.DavisKahanExt.ClosedOperator.reducingRestriction_inclusion_intertwines
    A (realSelfAdjointSpectralSubspace A hA S hS)
    (realSelfAdjointSpectralSubspace_reducing A hA S hS) x

end
end RealSpectralRestriction
end SpectraBridge
end Experimental
end DavisKahan
end ForMathlib

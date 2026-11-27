/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.BorelCalculus.PVM
public import DavisKahan.SpectralTheory.Real.SpectralRestriction
public import DavisKahan.SpectralTheory.AbstractSpectrum

/-!
# Canonical spectral projections

This module is the low-level spectral-projection surface used by the concrete
continuation development. The complex projection comes from TauCeti's
spectral measure of the everywhere-defined partial map. The real projection
comes from the complexification-and-descent API in
`DavisKahan.SpectralTheory.Real.SpectralRestriction`.

The former scalar-generic `spectralResolution` namespace and the nonexistent
`Spectra.SpectralTheory.SpectralTheorem` import are not reconstructed.  A
uniform `RCLike` PVM would require mathematical structure not present in the
pinned dependencies.  Downstream contour theory should identify its Riesz
operator with `boundedSelfAdjointSpectralProjection` instead.
-/

public section

namespace TauCeti
namespace DavisKahanExt

open DavisKahan

open Set
open scoped InnerProductSpace
open DavisKahan
open DavisKahan.Foundation

universe v

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A spectral point of a self-adjoint operator is its own real part. -/
theorem coe_reCoord (A : H →L[ℂ] H) (hA : A.IsSymmetric)
    (w : spectrum ℂ A) :
    ((TauCeti.BorelCalculus.reCoord w : ℝ) : ℂ) = (w : ℂ) := by
  have hAsa : IsSelfAdjoint A := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA
  rw [TauCeti.BorelCalculus.reCoord_apply]
  exact (hAsa.mem_spectrum_eq_re w.property).symm

/-- The genuine measurable spectral projection of a bounded self-adjoint
operator. -/
@[expose]
noncomputable def boundedSelfAdjointSpectralProjection
    (A : H →L[ℂ] H) (hA : A.IsSymmetric)
    (s : Set ℝ) (hs : MeasurableSet s) : H →L[ℂ] H :=
  ((A.toLinearMap.toPMap ⊤).spectralPVM
      (LinearPMap.isSelfAdjoint_toPMap_top
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA))).proj s hs

/-- The selected spectral range of a bounded self-adjoint operator. -/
@[expose]
noncomputable def boundedSelfAdjointSpectralSubspace
    (A : H →L[ℂ] H) (hA : A.IsSymmetric)
    (s : Set ℝ) (hs : MeasurableSet s) : Submodule ℂ H :=
  (boundedSelfAdjointSpectralProjection A hA s hs).range

/-- The selected bounded spectral range has the canonical orthogonal
projection supplied by the underlying PVM projection. -/
noncomputable instance boundedSelfAdjointSpectralSubspace_hasOrthogonalProjection
    (A : H →L[ℂ] H) (hA : A.IsSymmetric)
    (s : Set ℝ) (hs : MeasurableSet s) :
    (boundedSelfAdjointSpectralSubspace A hA s hs).HasOrthogonalProjection := by
  unfold boundedSelfAdjointSpectralSubspace boundedSelfAdjointSpectralProjection
  infer_instance

/-- **The bounded spectral projection is the continuous functional calculus of
any continuous symbol agreeing with the indicator on the spectrum.** -/
theorem boundedSelfAdjointSpectralProjection_eq_cfcL_of_agrees
    (A : H →L[ℂ] H) (hA : A.IsSymmetric)
    (s : Set ℝ) (hs : MeasurableSet s) (g : C(spectrum ℂ A, ℂ))
    (hg : ∀ w : spectrum ℂ A,
      g w = (TauCeti.BorelCalculus.reCoord ⁻¹' s).indicator (fun _ => (1 : ℂ)) w) :
    boundedSelfAdjointSpectralProjection A hA s hs =
      cfcL ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mpr hA).isStarNormal g :=
  TauCeti.BorelCalculus.boundedPVM_proj_eq_cfcHom
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA) s hs g hg

/-- The selected spectral subspace is exactly the range of its spectral
projection. -/
@[simp] theorem boundedSelfAdjointSpectralSubspace_eq_range
    (A : H →L[ℂ] H) (hA : A.IsSymmetric)
    (s : Set ℝ) (hs : MeasurableSet s) :
    boundedSelfAdjointSpectralSubspace A hA s hs =
      (boundedSelfAdjointSpectralProjection A hA s hs).range :=
  rfl

/-- The genuine bounded spectral projection is the Mathlib star projection
onto its selected spectral range. -/
theorem boundedSelfAdjointSpectralProjection_eq_starProjection
    (A : H →L[ℂ] H) (hA : A.IsSymmetric)
    (s : Set ℝ) (hs : MeasurableSet s) :
    boundedSelfAdjointSpectralProjection A hA s hs =
      (boundedSelfAdjointSpectralSubspace A hA s hs).starProjection := by
  let P := (A.toLinearMap.toPMap ⊤).spectralPVM
    (LinearPMap.isSelfAdjoint_toPMap_top
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA))
  exact (P.starProjection_range_proj s hs).symm

/-- Every genuine bounded spectral projection is an orthogonal projection in
the continuation-facing predicate. -/
theorem boundedSelfAdjointSpectralProjection_isOrthogonalProjection
    (A : H →L[ℂ] H) (hA : A.IsSymmetric)
    (s : Set ℝ) (hs : MeasurableSet s) :
    IsOrthogonalProjection
      (boundedSelfAdjointSpectralProjection A hA s hs) := by
  let P : TauCeti.ProjValMeasure ℝ H := (A.toLinearMap.toPMap ⊤).spectralPVM
      (LinearPMap.isSelfAdjoint_toPMap_top
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA))
  change IsOrthogonalProjection (P.proj s hs)
  exact ⟨P.proj_idem s hs,
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (P.isSelfAdjoint_proj s hs)⟩

end DavisKahanExt
end TauCeti

/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Interop.Spectra.Basic
import DavisKahan.Interop.Spectra.PVMSubspace
import DavisKahan.Interop.Spectra.RealSpectralRestriction
import Spectra.SpectralTheory.ResolventForm
import Spectra.StoneBridge.CalculusBridge

/-!
# Canonical spectral projections

This module is the low-level spectral-projection surface used by the concrete
continuation development.  It is deliberately complex at the bounded Spectra
layer: the PVM is the genuine spectral measure of the bridged bounded
self-adjoint operator.  Real projections are supplied independently by the
complexification-and-descent API in
`DavisKahan.Interop.Spectra.RealSpectralRestriction`.

The former scalar-generic `spectralResolution` namespace and the nonexistent
`Spectra.SpectralTheory.SpectralTheorem` import are not reconstructed.  A
uniform `RCLike` PVM would require mathematical structure not present in the
pinned dependencies.  Downstream contour theory should identify its Riesz
operator with `boundedSelfAdjointSpectralProjection` instead.
-/

namespace ForMathlib
namespace DavisKahanExt

open Set
open scoped InnerProductSpace
open Spectra.QuantumMechanics.SpectralTheory
open DavisKahan.Experimental.SpectraBridge

universe v

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The genuine Spectra projection-valued measure of a bounded self-adjoint
operator. -/
noncomputable def boundedSelfAdjointSpectralPVM
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A) :
    Spectra.ProjValMeasure H :=
  spectralPVM (boundedSelfAdjointOperator A hA).selfAdjoint

/-- The genuine measurable spectral projection of a bounded self-adjoint
operator. -/
noncomputable def boundedSelfAdjointSpectralProjection
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A)
    (s : Set ℝ) (hs : MeasurableSet s) : H →L[ℂ] H :=
  (boundedSelfAdjointSpectralPVM A hA).proj s hs

/-- The selected spectral range of a bounded self-adjoint operator. -/
noncomputable def boundedSelfAdjointSpectralSubspace
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A)
    (s : Set ℝ) (hs : MeasurableSet s) : Submodule ℂ H :=
  pvmRangeSubspace (boundedSelfAdjointSpectralPVM A hA) s hs

/-- The selected bounded spectral range has the canonical orthogonal
projection supplied by the underlying PVM projection. -/
noncomputable instance boundedSelfAdjointSpectralSubspace_hasOrthogonalProjection
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A)
    (s : Set ℝ) (hs : MeasurableSet s) :
    (boundedSelfAdjointSpectralSubspace A hA s hs).HasOrthogonalProjection := by
  change
    (pvmRangeSubspace (boundedSelfAdjointSpectralPVM A hA) s hs).HasOrthogonalProjection
  infer_instance

/-- The bounded spectral projection is the group-calculus spectral projection
used by Spectra. -/
theorem boundedSelfAdjointSpectralProjection_eq_spectralProjection
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A)
    (s : Set ℝ) (hs : MeasurableSet s) :
    boundedSelfAdjointSpectralProjection A hA s hs =
      Spectra.QuantumMechanics.SpectralTheory.spectralProjection
        (Spectra.YosidaHille.genToGroup
          (boundedSelfAdjointOperator A hA).selfAdjoint) s hs :=
  rfl

/-- The selected spectral subspace is exactly the range of its spectral
projection. -/
@[simp] theorem boundedSelfAdjointSpectralSubspace_eq_range
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A)
    (s : Set ℝ) (hs : MeasurableSet s) :
    boundedSelfAdjointSpectralSubspace A hA s hs =
      (boundedSelfAdjointSpectralProjection A hA s hs).range :=
  rfl

/-- The genuine bounded spectral projection is the Mathlib star projection
onto its selected spectral range. -/
theorem boundedSelfAdjointSpectralProjection_eq_starProjection
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A)
    (s : Set ℝ) (hs : MeasurableSet s) :
    boundedSelfAdjointSpectralProjection A hA s hs =
      (boundedSelfAdjointSpectralSubspace A hA s hs).starProjection := by
  change
    (boundedSelfAdjointSpectralPVM A hA).proj s hs =
      (pvmRangeSubspace (boundedSelfAdjointSpectralPVM A hA) s hs).starProjection
  exact pvmProjection_eq_starProjection_rangeSubspace
    (boundedSelfAdjointSpectralPVM A hA) s hs

/-- Every genuine bounded spectral projection is an orthogonal projection in
the continuation-facing predicate. -/
theorem boundedSelfAdjointSpectralProjection_isOrthogonalProjection
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A)
    (s : Set ℝ) (hs : MeasurableSet s) :
    IsOrthogonalProjection
      (boundedSelfAdjointSpectralProjection A hA s hs) := by
  let P : Spectra.ProjValMeasure H := boundedSelfAdjointSpectralPVM A hA
  change IsOrthogonalProjection (P.proj s hs)
  constructor
  · apply ContinuousLinearMap.ext
    intro x
    change P.proj s hs (P.proj s hs x) = P.proj s hs x
    simpa only [mul_apply_eq_comp] using
      congrArg (fun T : H →L[ℂ] H => T x) (P.proj_idem s hs)
  · exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (P.isSelfAdjoint_proj s hs)

end DavisKahanExt
end ForMathlib

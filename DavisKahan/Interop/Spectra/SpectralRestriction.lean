/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Interop.Spectra.ClosedOperator
import DavisKahan.Interop.Spectra.PVMSubspace
import Spectra.SpectralTheory.Measure.GeneratorLink
import Spectra.SpectralTheory.Measure.PVM

/-!
# Spectral-subspace domain and intertwining adapters

This file begins the genuine spectral-restriction path needed to specialize the
unbounded sine-theta theorem to spectral projections of an operator and its
bounded perturbation.

For a self-adjoint DK closed operator `A`, the canonical Spectra projection
`E_A(B)` is packaged as a continuous linear map and its range as a closed
orthogonally complemented subspace.  The main analytic facts proved here are:

* `E_A(B)` preserves `A.domain` for every measurable set `B`;
* `A (E_A(B)x) = E_A(B) (A x)` on `A.domain`;
* consequently the spectral range is invariant under the domain-aware action
  of `A`.

These are the exact domain/intertwining obligations needed before the operator
part on the spectral range can be bundled as a self-adjoint closed operator.
-/

open scoped InnerProductSpace

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace SpectraBridge

open Spectra.OneParameterUnitaryGroup
open Spectra.YosidaHille
open Spectra.QuantumMechanics.SpectralTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The canonical Spectra spectral projection of a self-adjoint DK closed
operator. -/
noncomputable def selfAdjointSpectralProjection
    (A : DKClosedOperator (H := H)) (hA : A.IsSelfAdjoint)
    (B : Set ℝ) (hB : MeasurableSet B) : H →L[ℂ] H :=
  spectralProjection (genToGroup hA) B hB

/-- The range subspace of a canonical self-adjoint spectral projection. -/
noncomputable def selfAdjointSpectralSubspace
    (A : DKClosedOperator (H := H)) (hA : A.IsSelfAdjoint)
    (B : Set ℝ) (hB : MeasurableSet B) : Submodule ℂ H :=
  pvmRangeSubspace
    (Spectra.QuantumMechanics.SpectralTheory.PVM.spectralPVM hA) B hB

@[simp]
theorem selfAdjointSpectralSubspace_eq_range
    (A : DKClosedOperator (H := H)) (hA : A.IsSelfAdjoint)
    (B : Set ℝ) (hB : MeasurableSet B) :
    selfAdjointSpectralSubspace A hA B hB =
      (selfAdjointSpectralProjection A hA B hB).range :=
  rfl

/-- A canonical self-adjoint spectral range is complete. -/
noncomputable instance selfAdjointSpectralSubspace_completeSpace
    (A : DKClosedOperator (H := H)) (hA : A.IsSelfAdjoint)
    (B : Set ℝ) (hB : MeasurableSet B) :
    CompleteSpace (selfAdjointSpectralSubspace A hA B hB) := by
  unfold selfAdjointSpectralSubspace
  infer_instance

/-- A canonical self-adjoint spectral range is orthogonally complemented. -/
noncomputable instance selfAdjointSpectralSubspace_hasOrthogonalProjection
    (A : DKClosedOperator (H := H)) (hA : A.IsSelfAdjoint)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (selfAdjointSpectralSubspace A hA B hB).HasOrthogonalProjection := by
  unfold selfAdjointSpectralSubspace
  infer_instance

/-- The canonical inclusion of a spectral range into the ambient Hilbert
space. -/
noncomputable def selfAdjointSpectralSubspaceInclusion
    (A : DKClosedOperator (H := H)) (hA : A.IsSelfAdjoint)
    (B : Set ℝ) (hB : MeasurableSet B) :
    selfAdjointSpectralSubspace A hA B hB →L[ℂ] H :=
  Submodule.subtypeL (selfAdjointSpectralSubspace A hA B hB)

@[simp]
theorem selfAdjointSpectralSubspaceInclusion_apply
    (A : DKClosedOperator (H := H)) (hA : A.IsSelfAdjoint)
    (B : Set ℝ) (hB : MeasurableSet B)
    (x : selfAdjointSpectralSubspace A hA B hB) :
    selfAdjointSpectralSubspaceInclusion A hA B hB x = (x : H) :=
  rfl

/-- Inclusion of a spectral range preserves norms exactly. -/
theorem selfAdjointSpectralSubspaceInclusion_isometric
    (A : DKClosedOperator (H := H)) (hA : A.IsSelfAdjoint)
    (B : Set ℝ) (hB : MeasurableSet B) :
    IsometricEmbedding (selfAdjointSpectralSubspaceInclusion A hA B hB) := by
  intro x
  rfl

/-- The canonical spectral projection is the orthogonal projection onto its
range subspace. -/
theorem selfAdjointSpectralProjection_eq_starProjection
    (A : DKClosedOperator (H := H)) (hA : A.IsSelfAdjoint)
    (B : Set ℝ) (hB : MeasurableSet B) :
    selfAdjointSpectralProjection A hA B hB =
      (selfAdjointSpectralSubspace A hA B hB).starProjection := by
  exact pvmProjection_eq_starProjection_rangeSubspace
    (Spectra.QuantumMechanics.SpectralTheory.PVM.spectralPVM hA) B hB

/-- Every measurable spectral projection preserves the domain of its
self-adjoint operator. -/
theorem selfAdjointSpectralProjection_mem_domain
    (A : DKClosedOperator (H := H)) (hA : A.IsSelfAdjoint)
    {B : Set ℝ} (hB : MeasurableSet B) (x : A.domain) :
    selfAdjointSpectralProjection A hA B hB (x : H) ∈ A.domain := by
  let U := genToGroup hA
  have hgen : generator U = A.toLinearPMap := generator_genToGroup hA
  have hdom : (generator U).domain = A.domain :=
    congrArg LinearPMap.domain hgen
  have hxU : (x : H) ∈ (generator U).domain :=
    (le_of_eq hdom.symm) x.property
  have hxUproj :
      spectralProjection U B hB (x : H) ∈ (generator U).domain :=
    spectralProjection_mem_generatorDomain_of_mem U hB
      (⟨(x : H), hxU⟩ : (generator U).domain)
  exact (le_of_eq hdom) hxUproj

/-- A self-adjoint operator commutes with each measurable spectral projection
on its full operator domain. -/
theorem selfAdjoint_apply_spectralProjection
    (A : DKClosedOperator (H := H)) (hA : A.IsSelfAdjoint)
    {B : Set ℝ} (hB : MeasurableSet B) (x : A.domain) :
    A.toLinearMap
        ⟨selfAdjointSpectralProjection A hA B hB (x : H),
          selfAdjointSpectralProjection_mem_domain A hA hB x⟩ =
      selfAdjointSpectralProjection A hA B hB (A.toLinearMap x) := by
  let U := genToGroup hA
  have hgen : generator U = A.toLinearPMap := generator_genToGroup hA
  have hdom : (generator U).domain = A.domain :=
    congrArg LinearPMap.domain hgen
  have hxU : (x : H) ∈ (generator U).domain :=
    (le_of_eq hdom.symm) x.property
  let xU : (generator U).domain := ⟨(x : H), hxU⟩
  have hprojU : spectralProjection U B hB (x : H) ∈ (generator U).domain :=
    spectralProjection_mem_generatorDomain_of_mem U hB xU
  have hcomm := generator_spectralProjection_comm U hB xU
  have happly := (LinearPMap.ext_iff.mp hgen).2
  have hleft :
      generator U ⟨spectralProjection U B hB (x : H), hprojU⟩ =
        A.toLinearPMap
          ⟨spectralProjection U B hB (x : H),
            selfAdjointSpectralProjection_mem_domain A hA hB x⟩ :=
    happly
      (x := spectralProjection U B hB (x : H))
      (hf := hprojU)
      (hg := selfAdjointSpectralProjection_mem_domain A hA hB x)
  have hright : generator U xU = A.toLinearPMap x :=
    happly (x := (x : H)) (hf := hxU) (hg := x.property)
  change A.toLinearPMap
      ⟨spectralProjection U B hB (x : H),
        selfAdjointSpectralProjection_mem_domain A hA hB x⟩ =
    spectralProjection U B hB (A.toLinearPMap x)
  calc
    A.toLinearPMap
        ⟨spectralProjection U B hB (x : H),
          selfAdjointSpectralProjection_mem_domain A hA hB x⟩ =
        generator U ⟨spectralProjection U B hB (x : H), hprojU⟩ :=
      hleft.symm
    _ = spectralProjection U B hB (generator U xU) := hcomm
    _ = spectralProjection U B hB (A.toLinearPMap x) :=
      congrArg (fun z : H => spectralProjection U B hB z) hright

/-- The domain-aware image of a vector in a spectral range remains in that
spectral range. -/
theorem selfAdjoint_maps_spectralSubspace
    (A : DKClosedOperator (H := H)) (hA : A.IsSelfAdjoint)
    {B : Set ℝ} (hB : MeasurableSet B) (x : A.domain)
    (hx : (x : H) ∈ selfAdjointSpectralSubspace A hA B hB) :
    A.toLinearMap x ∈ selfAdjointSpectralSubspace A hA B hB := by
  let P := Spectra.QuantumMechanics.SpectralTheory.PVM.spectralPVM hA
  change A.toLinearMap x ∈ pvmRangeSubspace P B hB
  rw [mem_pvmRangeSubspace_iff P B hB]
  change selfAdjointSpectralProjection A hA B hB (A.toLinearMap x) =
    A.toLinearMap x
  have hfixP : P.proj B hB (x : H) = (x : H) :=
    pvmProjection_eq_self_of_mem_rangeSubspace P B hB hx
  have hfix : selfAdjointSpectralProjection A hA B hB (x : H) = (x : H) := by
    change P.proj B hB (x : H) = (x : H)
    exact hfixP
  have hsub :
      (⟨selfAdjointSpectralProjection A hA B hB (x : H),
        selfAdjointSpectralProjection_mem_domain A hA hB x⟩ : A.domain) = x :=
    Subtype.ext hfix
  calc
    selfAdjointSpectralProjection A hA B hB (A.toLinearMap x) =
        A.toLinearMap
          ⟨selfAdjointSpectralProjection A hA B hB (x : H),
            selfAdjointSpectralProjection_mem_domain A hA hB x⟩ :=
      (selfAdjoint_apply_spectralProjection A hA hB x).symm
    _ = A.toLinearMap x := congrArg A.toLinearMap hsub

end SpectraBridge
end Experimental
end DavisKahan
end ForMathlib

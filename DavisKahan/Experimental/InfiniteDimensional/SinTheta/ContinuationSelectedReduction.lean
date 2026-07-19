/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.ContinuationSelectedGraph
import Spectra.SpectralTheory.Measure.GeneratorLink

/-!
# Reduction of the selected continuation graph

The selected endpoint constructed by continuation is a genuine spectral
subspace of the perturbed self-adjoint operator.  This leaf proves directly
from Spectra's generator/projection commutation theorem that every such
bounded spectral subspace reduces its operator.  Transporting reduction
through the selected-graph identity then shows that the canonical contractive
selected endpoint graph is reducing.

No block-coordinate identification is made here.  The subsequent Riccati
bridge must transport this ambient reducing graph to the direct-sum block
model before invoking the bounded Riccati reduction theorem.
-/

namespace ForMathlib
namespace DavisKahanExt

open Set
open scoped InnerProductSpace unitInterval
open Spectra.OneParameterUnitaryGroup
open Spectra.QuantumMechanics.SpectralTheory
open Spectra.YosidaHille
open DavisKahan.Experimental.SpectraBridge

universe v

section SpectralSubspaceReduction

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A genuine bounded self-adjoint spectral projection commutes pointwise with
its operator. -/
theorem boundedSelfAdjointSpectralProjection_apply_comm
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A)
    (s : Set ℝ) (hs : MeasurableSet s) (x : H) :
    A (boundedSelfAdjointSpectralProjection A hA s hs x) =
      boundedSelfAdjointSpectralProjection A hA s hs (A x) := by
  let T := boundedSelfAdjointOperator A hA
  let U := genToGroup T.selfAdjoint
  have hTbounded : T.IsBounded := by
    change T.domain = ⊤
    simpa only [T] using boundedSelfAdjointOperator_domain A hA
  have hxT : x ∈ T.domain := by
    rw [hTbounded]
    exact Submodule.mem_top
  have hgen : generator U = T.toLinearPMap :=
    generator_genToGroup T.selfAdjoint
  have hdom : (generator U).domain = T.domain :=
    congrArg LinearPMap.domain hgen
  have hxU : x ∈ (generator U).domain :=
    (le_of_eq hdom.symm) hxT
  let xU : (generator U).domain := ⟨x, hxU⟩
  have hprojU : Spectra.QuantumMechanics.SpectralTheory.spectralProjection U s hs x ∈ (generator U).domain :=
    spectralProjection_mem_generatorDomain_of_mem U hs xU
  have hprojT : Spectra.QuantumMechanics.SpectralTheory.spectralProjection U s hs x ∈ T.domain :=
    (le_of_eq hdom) hprojU
  have hcomm := generator_spectralProjection_comm U hs xU
  have happly := (LinearPMap.ext_iff.mp hgen).2
  have hleft :
      generator U ⟨Spectra.QuantumMechanics.SpectralTheory.spectralProjection U s hs x, hprojU⟩ =
        T.toLinearPMap ⟨Spectra.QuantumMechanics.SpectralTheory.spectralProjection U s hs x, hprojT⟩ :=
    happly
      (x := Spectra.QuantumMechanics.SpectralTheory.spectralProjection U s hs x)
      (hf := hprojU)
      (hg := hprojT)
  have hright : generator U xU = T.toLinearPMap ⟨x, hxT⟩ :=
    happly (x := x) (hf := hxU) (hg := hxT)
  have hpartialComm :
      T.toLinearPMap ⟨Spectra.QuantumMechanics.SpectralTheory.spectralProjection U s hs x, hprojT⟩ =
        Spectra.QuantumMechanics.SpectralTheory.spectralProjection U s hs (T.toLinearPMap ⟨x, hxT⟩) := by
    calc
      T.toLinearPMap ⟨Spectra.QuantumMechanics.SpectralTheory.spectralProjection U s hs x, hprojT⟩ =
          generator U ⟨Spectra.QuantumMechanics.SpectralTheory.spectralProjection U s hs x, hprojU⟩ := hleft.symm
      _ = Spectra.QuantumMechanics.SpectralTheory.spectralProjection U s hs (generator U xU) := hcomm
      _ = Spectra.QuantumMechanics.SpectralTheory.spectralProjection U s hs (T.toLinearPMap ⟨x, hxT⟩) :=
        congrArg (fun z : H => Spectra.QuantumMechanics.SpectralTheory.spectralProjection U s hs z) hright
  have hboundedComm :
      T.boundedExtension hTbounded (Spectra.QuantumMechanics.SpectralTheory.spectralProjection U s hs x) =
        Spectra.QuantumMechanics.SpectralTheory.spectralProjection U s hs (T.boundedExtension hTbounded x) := by
    rw [T.boundedExtension_apply hTbounded,
      T.boundedExtension_apply hTbounded]
    exact hpartialComm
  have hTextension : T.boundedExtension hTbounded = A := by
    simpa only [T] using boundedExtension_boundedSelfAdjointOperator A hA
  rw [hTextension] at hboundedComm
  change
    A (Spectra.QuantumMechanics.SpectralTheory.spectralProjection
      (genToGroup (boundedSelfAdjointOperator A hA).selfAdjoint) s hs x) =
      Spectra.QuantumMechanics.SpectralTheory.spectralProjection
        (genToGroup (boundedSelfAdjointOperator A hA).selfAdjoint) s hs (A x)
  simpa only [T, U] using hboundedComm

/-- Every genuine bounded spectral subspace reduces its self-adjoint
operator. -/
theorem boundedSelfAdjointSpectralSubspace_reduces
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A)
    (s : Set ℝ) (hs : MeasurableSet s) :
    Reduces A (boundedSelfAdjointSpectralSubspace A hA s hs) := by
  apply reduces_orthogonalComplement hA
  intro x hx
  change x ∈ (boundedSelfAdjointSpectralProjection A hA s hs).range at hx
  rcases hx with ⟨y, rfl⟩
  change
    A (boundedSelfAdjointSpectralProjection A hA s hs y) ∈
      (boundedSelfAdjointSpectralProjection A hA s hs).range
  refine ⟨A y, ?_⟩
  exact (boundedSelfAdjointSpectralProjection_apply_comm A hA s hs y).symm

end SpectralSubspaceReduction

section SelectedEndpointReduction

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The graph of the canonical continuation-selected endpoint angular
operator reduces the perturbed bounded self-adjoint operator. -/
theorem selectedEndpointAngularOperator_graph_reduces_of_contour_bound
    (Γ : PiecewiseC1ClosedContour) (A K : H →L[ℂ] H)
    (delta : ℝ) (hdelta : 0 < delta)
    (s : Set ℝ) (hs : MeasurableSet s)
    (hA : IsSelfAdjointOperator A)
    (hAK : IsSelfAdjointOperator (A + K))
    (hself : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      IsSelfAdjointOperator (operatorPath A K t))
    (hsep : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x : unitInterval,
      ∀ lam ∈ realSpectrum (operatorPath A K t),
        delta ≤ ‖Γ.path x - (lam : ℂ)‖)
    (hidentify : ∀ t (ht : t ∈ Set.Icc (0 : ℝ) 1),
      fixedContourRieszOperator Γ (operatorPath A K t) =
        boundedSelfAdjointSpectralProjection (operatorPath A K t)
          (hself t ht) s hs)
    (hsmall : selectedBranchProjectionLipschitzConstant Γ K delta <
      Real.sqrt 2 / 2) :
    Reduces (A + K)
      (graphSubspace (boundedSelfAdjointSpectralSubspace A hA s hs)
        (selectedEndpointAngularOperator Γ A K delta hdelta s hs hA hAK
          hself hsep hidentify hsmall)) := by
  rw [graphSubspace_selectedEndpointAngularOperator Γ A K delta hdelta
    s hs hA hAK hself hsep hidentify hsmall]
  exact boundedSelfAdjointSpectralSubspace_reduces (A + K) hAK s hs

end SelectedEndpointReduction

end DavisKahanExt
end ForMathlib

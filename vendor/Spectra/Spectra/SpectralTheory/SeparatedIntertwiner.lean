/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Jon Crall, OpenAI GPT-5.6 Thinking
-/
import Mathlib.MeasureTheory.Measure.Support
import Spectra.QuantumMechanics.BornRule.Observable
import Spectra.Resolvent.Meromorphic
import Spectra.SpectralTheory.Algebra
import Spectra.YosidaHille.RectangularIntertwining

/-!
# Rectangular intertwiners of spectrally separated self-adjoint operators

A bounded map intertwining two self-adjoint generators intertwines all of their
spectral projections.  If the real spectra are disjoint, projection onto the
first spectrum is the identity on the target and zero on the source, forcing
the map to vanish.

This is the arbitrary-spectrum homogeneous uniqueness theorem needed by the
square-norm Davis--Kahan theorem.  It does not require interval/exterior or
ordered half-line geometry.
-/

open MeasureTheory Complex Spectra
open scoped InnerProductSpace
open Spectra.Operator
open Spectra.YosidaHille
open Spectra.Resolvent
-- The spectral (Borel) measure lives in `Spectra.Borel`, which is not opened by
-- any of the namespaces above.
open Spectra.Borel
-- The Born measure and its support estimate sit one namespace deeper than they are
-- cited below: under `BornRule.PVM` and `BornRule.Observable`, not under `BornRule`.
open Spectra.QuantumMechanics.BornRule.PVM
open Spectra.QuantumMechanics.BornRule.Observable

namespace Spectra.QuantumMechanics.SpectralTheory

noncomputable section

universe u v

variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The real spectrum of an unbounded self-adjoint operator is closed. -/
theorem isClosed_spectrum_of_isSelfAdjoint
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : SelfAdjointOperator H) :
    IsClosed (spectrum A.toLinearPMap) := by
  have hopen : IsOpen {x : ℝ | (x : ℂ) ∈ resolventSet A.toLinearPMap} :=
    (isOpen_resolventSet A.toLinearPMap).preimage Complex.continuous_ofReal
  change IsClosed ({x : ℝ | (x : ℂ) ∈ resolventSet A.toLinearPMap}ᶜ)
  exact hopen.isClosed_compl

private theorem spectralProjection_eq_zero_of_disjoint_spectrum
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : SelfAdjointOperator H)
    (S : Set ℝ) (hS : MeasurableSet S)
    (hdisj : Disjoint S (spectrum A.toLinearPMap)) :
    spectralProjection (genToGroup A.selfAdjoint) S hS = 0 := by
  apply ContinuousLinearMap.ext
  intro ψ
  rw [ContinuousLinearMap.zero_apply,
    spectralProjection_eq_zero_iff_measure_zero]
  let μ := borelMeasure (genToGroup A.selfAdjoint) ψ
  have hsupp : μ.support ⊆ spectrum A.toLinearPMap := by
    simpa [μ, bornMeasure, SelfAdjointOperator.spectralPVM] using
      bornMeasure_support_subset_spectrum A ψ
  have hsubset : S ⊆ μ.supportᶜ := by
    intro lam hlam hlsupp
    exact Set.disjoint_left.mp hdisj hlam (hsupp hlsupp)
  exact measure_mono_null hsubset μ.measure_compl_support

/-- The spectral projection of a self-adjoint operator onto its whole spectrum
is the identity. -/
theorem spectralProjection_spectrum_eq_id
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : SelfAdjointOperator H) :
    spectralProjection (genToGroup A.selfAdjoint)
        (spectrum A.toLinearPMap)
        (isClosed_spectrum_of_isSelfAdjoint A).measurableSet
      = ContinuousLinearMap.id ℂ H := by
  let S := spectrum A.toLinearPMap
  let hS : MeasurableSet S := (isClosed_spectrum_of_isSelfAdjoint A).measurableSet
  have hcomp : spectralProjection (genToGroup A.selfAdjoint) Sᶜ hS.compl = 0 := by
    apply ContinuousLinearMap.ext
    intro ψ
    rw [ContinuousLinearMap.zero_apply,
      spectralProjection_eq_zero_iff_measure_zero]
    let μ := borelMeasure (genToGroup A.selfAdjoint) ψ
    have hsupp : μ.support ⊆ S := by
      simpa [μ, S, bornMeasure, SelfAdjointOperator.spectralPVM] using
        bornMeasure_support_subset_spectrum A ψ
    have hsubset : Sᶜ ⊆ μ.supportᶜ := by
      intro lam hlam hlsupp
      exact hlam (hsupp hlsupp)
    exact measure_mono_null hsubset μ.measure_compl_support
  have hcompl := spectralProjection_compl
    (genToGroup A.selfAdjoint) S hS
  rw [hcomp] at hcompl
  exact (sub_eq_zero.mp hcompl.symm).symm

/-- A bounded generator intertwiner between self-adjoint operators with
disjoint spectra is zero. -/
theorem generatorIntertwiner_eq_zero_of_disjoint_spectrum
    (A : SelfAdjointOperator E)
    (B : SelfAdjointOperator F)
    (X : F →L[ℂ] E)
    (hX : GeneratorIntertwines
      (genToGroup A.selfAdjoint) (genToGroup B.selfAdjoint) X)
    (hdisj : Disjoint
      (spectrum A.toLinearPMap) (spectrum B.toLinearPMap)) :
    X = 0 := by
  let S := spectrum A.toLinearPMap
  let hS : MeasurableSet S := (isClosed_spectrum_of_isSelfAdjoint A).measurableSet
  have hintertwine := spectralProjection_intertwines_of_generator
    (genToGroup A.selfAdjoint) (genToGroup B.selfAdjoint) X hX S hS
  have hEA : spectralProjection (genToGroup A.selfAdjoint) S hS =
      ContinuousLinearMap.id ℂ E := by
    simpa [S, hS] using spectralProjection_spectrum_eq_id A
  have hEB : spectralProjection (genToGroup B.selfAdjoint) S hS = 0 :=
    spectralProjection_eq_zero_of_disjoint_spectrum B S hS hdisj
  rw [hEA, hEB] at hintertwine
  simpa using hintertwine

end
end Spectra.QuantumMechanics.SpectralTheory

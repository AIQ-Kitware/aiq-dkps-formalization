/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Sylvester.PairwiseSpectrumGap
import DavisKahan.Sylvester.ClosedSylvesterEquation
import Spectra.SpectralTheory.SeparatedIntertwiner

/-!
# Homogeneous Sylvester uniqueness at arbitrary spectral separation

This file converts a domain-aware closed Sylvester equation into the generator
intertwining relation used by the rectangular Stone theorem.  Disjoint spectra
then force the bounded intertwiner to vanish.  Unlike the older uniqueness
lemma, no interval/exterior or ordered half-line geometry is required.
-/

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open scoped InnerProductSpace
open TauCeti.DavisKahanExt
open Spectra.YosidaHille
open Spectra.Operator
-- `generator` belongs to the one-parameter unitary group namespace, which none of
-- the namespaces above re-exports.
open Spectra.OneParameterUnitaryGroup

noncomputable section

universe v

variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

private theorem generatorIntertwines_of_linearPMapHomogeneous
    {A : E →ₗ.[ℂ] E} {B : F →ₗ.[ℂ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {X : F →L[ℂ] E}
    (hEq : TauCeti.LinearPMap.SylvesterEquation A B X 0) :
    GeneratorIntertwines (genToGroup hA) (genToGroup hB) X := by
  have hgenA : generator (genToGroup hA) = A :=
    generator_genToGroup hA
  have hgenB : generator (genToGroup hB) = B :=
    generator_genToGroup hB
  have hdomA : (generator (genToGroup hA)).domain = A.domain :=
    congrArg LinearPMap.domain hgenA
  have hdomB : (generator (genToGroup hB)).domain = B.domain :=
    congrArg LinearPMap.domain hgenB
  refine ⟨?_, ?_⟩
  · intro x
    let xb : B.domain := ⟨(x : F), (le_of_eq hdomB) x.property⟩
    exact (le_of_eq hdomA.symm) (hEq.mapsTo_domain xb)
  · intro x
    let xb : B.domain := ⟨(x : F), (le_of_eq hdomB) x.property⟩
    have hmapA := hEq.mapsTo_domain xb
    have hAapply := (LinearPMap.ext_iff.mp hgenA).2
      (x := X (x : F))
      (hf := (le_of_eq hdomA.symm) hmapA)
      (hg := hmapA)
    have hBapply := (LinearPMap.ext_iff.mp hgenB).2
      (x := (x : F))
      (hf := x.property)
      (hg := xb.property)
    have heq := hEq.equation xb
    change generator (genToGroup hA)
        ⟨X (x : F), (le_of_eq hdomA.symm) hmapA⟩
      = X (generator (genToGroup hB) x)
    calc
      generator (genToGroup hA)
          ⟨X (x : F), (le_of_eq hdomA.symm) hmapA⟩
          = A ⟨X (x : F), hmapA⟩ := hAapply
      _ = X (B xb) := by
          simpa using sub_eq_zero.mp heq
      _ = X (generator (genToGroup hB) x) := by
          rw [hBapply]

/-- A bounded homogeneous Sylvester solution for raw self-adjoint partial maps
vanishes whenever their spectra are disjoint. -/
theorem linearPMapSylvester_homogeneous_eq_zero_of_disjoint_spectrum
    {A : E →ₗ.[ℂ] E} {B : F →ₗ.[ℂ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {X : F →L[ℂ] E}
    (hdisj : Disjoint
      (Spectra.Resolvent.spectrum A)
      (Spectra.Resolvent.spectrum B))
    (hEq : TauCeti.LinearPMap.SylvesterEquation A B X 0) :
    X = 0 := by
  let AO : SelfAdjointOperator E := ⟨A, hA⟩
  let BO : SelfAdjointOperator F := ⟨B, hB⟩
  exact Spectra.QuantumMechanics.SpectralTheory.generatorIntertwiner_eq_zero_of_disjoint_spectrum
    AO BO X (generatorIntertwines_of_linearPMapHomogeneous hA hB hEq) hdisj

/-- Positive pairwise spectral distance gives homogeneous uniqueness for raw
self-adjoint partial maps. -/
theorem linearPMapSylvester_homogeneous_eq_zero_of_pairwiseSpectrumGap
    {A : E →ₗ.[ℂ] E} {B : F →ₗ.[ℂ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {X : F →L[ℂ] E} {δ : ℝ}
    (hδ : 0 < δ)
    (hgap : LinearPMap.GenuinePairwiseSpectrumGap A B δ)
    (hEq : TauCeti.LinearPMap.SylvesterEquation A B X 0) :
    X = 0 := by
  exact linearPMapSylvester_homogeneous_eq_zero_of_disjoint_spectrum
    hA hB (hgap.disjoint hδ) hEq

/-- Two bounded raw partial-map Sylvester solutions coincide under positive
pairwise spectral separation. -/
theorem linearPMapSylvester_solution_unique_of_pairwiseSpectrumGap
    {A : E →ₗ.[ℂ] E} {B : F →ₗ.[ℂ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {X Y C : F →L[ℂ] E} {δ : ℝ}
    (hδ : 0 < δ)
    (hgap : LinearPMap.GenuinePairwiseSpectrumGap A B δ)
    (hX : TauCeti.LinearPMap.SylvesterEquation A B X C)
    (hY : TauCeti.LinearPMap.SylvesterEquation A B Y C) :
    X = Y := by
  have hhom : TauCeti.LinearPMap.SylvesterEquation A B (X - Y) 0 := by
    simpa using hX.sub hY
  exact sub_eq_zero.mp
    (linearPMapSylvester_homogeneous_eq_zero_of_pairwiseSpectrumGap
      hA hB hδ hgap hhom)

/-- A bounded homogeneous closed Sylvester solution vanishes whenever the two
self-adjoint spectra are disjoint. -/
theorem closedSylvester_homogeneous_eq_zero_of_disjoint_spectrum
    {A : ClosedOperator (𝕜 := ℂ) (E := E)}
    {B : ClosedOperator (𝕜 := ℂ) (E := F)}
    (hA : A.IsSelfAdjoint) (hB : B.IsSelfAdjoint)
    {X : F →L[ℂ] E}
    (hdisj : Disjoint
      (Spectra.Resolvent.spectrum A.toLinearPMap)
      (Spectra.Resolvent.spectrum B.toLinearPMap))
    (hEq : HasClosedSylvesterEquation A B X 0) :
    X = 0 := by
  exact linearPMapSylvester_homogeneous_eq_zero_of_disjoint_spectrum
    hA hB hdisj hEq

/-- Positive pairwise spectral distance implies homogeneous uniqueness. -/
theorem closedSylvester_homogeneous_eq_zero_of_pairwiseSpectrumGap
    {A : ClosedOperator (𝕜 := ℂ) (E := E)}
    {B : ClosedOperator (𝕜 := ℂ) (E := F)}
    (hA : A.IsSelfAdjoint) (hB : B.IsSelfAdjoint)
    {X : F →L[ℂ] E} {δ : ℝ}
    (hδ : 0 < δ)
    (hgap : GenuinePairwiseSpectrumGap A B δ)
    (hEq : HasClosedSylvesterEquation A B X 0) :
    X = 0 := by
  exact linearPMapSylvester_homogeneous_eq_zero_of_pairwiseSpectrumGap
    hA hB hδ hgap hEq

/-- Two bounded solutions of the same closed Sylvester equation coincide under
positive pairwise spectral separation. -/
theorem closedSylvester_solution_unique_of_pairwiseSpectrumGap
    {A : ClosedOperator (𝕜 := ℂ) (E := E)}
    {B : ClosedOperator (𝕜 := ℂ) (E := F)}
    (hA : A.IsSelfAdjoint) (hB : B.IsSelfAdjoint)
    {X Y C : F →L[ℂ] E} {δ : ℝ}
    (hδ : 0 < δ)
    (hgap : GenuinePairwiseSpectrumGap A B δ)
    (hX : HasClosedSylvesterEquation A B X C)
    (hY : HasClosedSylvesterEquation A B Y C) :
    X = Y := by
  exact linearPMapSylvester_solution_unique_of_pairwiseSpectrumGap
    hA hB hδ hgap hX hY

end

end ExactSinTheta
end Experimental
end DavisKahan
end TauCeti

/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Sylvester.PairwiseSpectrumGap
import DavisKahan.Experimental.InfiniteDimensional.Core.UnboundedSpectral
import Spectra.SpectralTheory.SeparatedIntertwiner

/-!
# Homogeneous Sylvester uniqueness at arbitrary spectral separation

This file converts a domain-aware closed Sylvester equation into the generator
intertwining relation used by the rectangular Stone theorem.  Disjoint spectra
then force the bounded intertwiner to vanish.  Unlike the older uniqueness
lemma, no interval/exterior or ordered half-line geometry is required.
-/

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open scoped InnerProductSpace
open ForMathlib.DavisKahanExt
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

private theorem generatorIntertwines_of_closedHomogeneous
    {A : ClosedOperator (𝕜 := ℂ) (E := E)}
    {B : ClosedOperator (𝕜 := ℂ) (E := F)}
    (hA : A.IsSelfAdjoint) (hB : B.IsSelfAdjoint)
    {X : F →L[ℂ] E}
    (hEq : HasClosedSylvesterEquation A B X 0) :
    GeneratorIntertwines (genToGroup hA) (genToGroup hB) X := by
  have hgenA : generator (genToGroup hA) = A.toLinearPMap :=
    generator_genToGroup hA
  have hgenB : generator (genToGroup hB) = B.toLinearPMap :=
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
          = A.toLinearPMap ⟨X (x : F), hmapA⟩ := hAapply
      _ = X (B.toLinearPMap xb) := by
          simpa using sub_eq_zero.mp heq
      _ = X (generator (genToGroup hB) x) := by
          rw [hBapply]
          -- The two domain elements carry the same vector with different
          -- membership proofs, so they agree by extensionality.
          congr 2

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
  let AO : SelfAdjointOperator E := ⟨A.toLinearPMap, hA⟩
  let BO : SelfAdjointOperator F := ⟨B.toLinearPMap, hB⟩
  exact Spectra.QuantumMechanics.SpectralTheory.generatorIntertwiner_eq_zero_of_disjoint_spectrum
    AO BO X (generatorIntertwines_of_closedHomogeneous hA hB hEq) hdisj

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
  exact closedSylvester_homogeneous_eq_zero_of_disjoint_spectrum
    hA hB (hgap.disjoint hδ) hEq

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
  have hhom : HasClosedSylvesterEquation A B (X - Y) 0 := by
    simpa using hX.sub hY
  exact sub_eq_zero.mp
    (closedSylvester_homogeneous_eq_zero_of_pairwiseSpectrumGap
      hA hB hδ hgap hhom)

end

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib

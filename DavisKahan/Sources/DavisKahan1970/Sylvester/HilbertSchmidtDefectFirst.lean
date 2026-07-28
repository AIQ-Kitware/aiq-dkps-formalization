/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.Released under Apache 2.0 license as described in the file LICENSE.Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Sources.DavisKahan1970.Ideals.HilbertSchmidtBasis
import DavisKahan.Sylvester.HomogeneousUniqueness
import Spectra.Spaces.Tensor.HilbertSchmidtGeneratorBridge
import Spectra.SpectralTheory.Calculus.SpectralGapInverse
import Spectra.YosidaHille.Basic

/-!
# Defect-first reduction for the square-norm Sylvester theorem

This file contains the non-circular core of Davis--Kahan Theorem 6.2.
Starting from a Hilbert--Schmidt defect `C`, represent `C` by its Hilbert tensor
`c`.  If the tensor Sylvester flow has vector spectral gap `delta` at `c`, the
bounded reciprocal functional calculus produces a tensor `z0` with

`generator z0 = c` and `‖z0‖ <= delta⁻¹ ‖c‖`.

The generator graph bridge turns `z0` into a bounded operator `X0` satisfying
the original closed Sylvester equation.  Operator-norm homogeneous uniqueness
then identifies every supplied bounded solution `X` with `X0`.  In particular,
no Hilbert--Schmidt membership of `X` is assumed before it is proved.The remaining spectral task is therefore precise: derive the vector spectral
gap of the defect tensor from pairwise separation of the two operator spectra.
-/

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open scoped InnerProductSpace
open TauCeti.DavisKahanExt
open Spectra.YosidaHille

noncomputable section

universe v

variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

private theorem hasClosedSylvesterEquation_of_tensorGenerator
    {A : ClosedOperator (𝕜 := ℂ) (E := E)}
    {B : ClosedOperator (𝕜 := ℂ) (E := F)}
    (hA : A.IsSelfAdjoint) (hB : B.IsSelfAdjoint)
    {z c : Spectra.HilbertSchmidtTensor.Space E F}
    (hz : z ∈ (Spectra.OneParameterUnitaryGroup.generator
      (Spectra.HilbertSchmidtTensor.sylvesterGroup
        (genToGroup hA) (genToGroup hB))).domain)
    (hzc : Spectra.OneParameterUnitaryGroup.generator
      (Spectra.HilbertSchmidtTensor.sylvesterGroup
        (genToGroup hA) (genToGroup hB)) ⟨z, hz⟩ = c) :
    HasClosedSylvesterEquation A B
      (Spectra.HilbertSchmidtTensor.toOperator z)
      (Spectra.HilbertSchmidtTensor.toOperator c) := by
  let U := genToGroup hA
  let V := genToGroup hB
  have hgen := Spectra.HilbertSchmidtTensor.toOperator_hasGeneratorSylvesterEquation U V hz hzc
  have hAU : Spectra.OneParameterUnitaryGroup.generator U = A.toLinearPMap :=
    generator_genToGroup hA
  have hBV : Spectra.OneParameterUnitaryGroup.generator V = B.toLinearPMap :=
    generator_genToGroup hB
  have hdomA : (Spectra.OneParameterUnitaryGroup.generator U).domain = A.domain :=
    congrArg LinearPMap.domain hAU
  have hdomB : (Spectra.OneParameterUnitaryGroup.generator V).domain = B.domain :=
    congrArg LinearPMap.domain hBV
  refine ⟨?_, ?_⟩
  · intro x
    let xV : (Spectra.OneParameterUnitaryGroup.generator V).domain :=
      ⟨(x : F), (le_of_eq hdomB.symm) x.property⟩
    exact (le_of_eq hdomA) (hgen.mapsTo_domain xV)
  · intro x
    let xV : (Spectra.OneParameterUnitaryGroup.generator V).domain :=
      ⟨(x : F), (le_of_eq hdomB.symm) x.property⟩
    have hmap := hgen.mapsTo_domain xV
    have hAapply := (LinearPMap.ext_iff.mp hAU).2
      (x := Spectra.HilbertSchmidtTensor.toOperator z (x : F))
      (hf := hmap)
      (hg := (le_of_eq hdomA) hmap)
    have hBapply := (LinearPMap.ext_iff.mp hBV).2
      (x := (x : F))
      (hf := xV.property)
      (hg := x.property)
    have heq := hgen.equation xV
    change A.toLinearPMap
        ⟨Spectra.HilbertSchmidtTensor.toOperator z (x : F),
          (le_of_eq hdomA) hmap⟩ -
      Spectra.HilbertSchmidtTensor.toOperator z (B.toLinearPMap x) =
        Spectra.HilbertSchmidtTensor.toOperator c (x : F)
    calc
      A.toLinearPMap
          ⟨Spectra.HilbertSchmidtTensor.toOperator z (x : F),
            (le_of_eq hdomA) hmap⟩ -
          Spectra.HilbertSchmidtTensor.toOperator z (B.toLinearPMap x)
          = Spectra.OneParameterUnitaryGroup.generator U
              ⟨Spectra.HilbertSchmidtTensor.toOperator z (x : F), hmap⟩ -
            Spectra.HilbertSchmidtTensor.toOperator z
              (Spectra.OneParameterUnitaryGroup.generator V xV) := by
                rw [hAapply, hBapply]
      _ = Spectra.HilbertSchmidtTensor.toOperator c (x : F) := heq

/-- Defect-first square-norm estimate, reduced to the vector spectral gap of
the Hilbert--Schmidt defect tensor. -/
theorem paperHilbertSchmidt_sylvester_defectFirst
    {A : ClosedOperator (𝕜 := ℂ) (E := E)}
    {B : ClosedOperator (𝕜 := ℂ) (E := F)}
    {X C : F →L[ℂ] E}
    (hA : A.IsSelfAdjoint) (hB : B.IsSelfAdjoint)
    {δ : ℝ} (hδ : 0 < δ)
    (hEq : HasClosedSylvesterEquation A B X C)
    (hunique : ∀ {Y : F →L[ℂ] E},
      HasClosedSylvesterEquation A B Y 0 → Y = 0)
    (hC : IsPaperHilbertSchmidt C)
    (hCgap : Spectra.QuantumMechanics.SpectralTheory.HasVectorSpectralGap
      (Spectra.HilbertSchmidtTensor.sylvesterGroup
        (genToGroup hA) (genToGroup hB))
      (paperHilbertSchmidtTensor C hC) δ) :
    IsPaperHilbertSchmidt X ∧
      δ * paperHilbertSchmidtNorm X ≤ paperHilbertSchmidtNorm C := by
  let W := Spectra.HilbertSchmidtTensor.sylvesterGroup
    (genToGroup hA) (genToGroup hB)
  let c := paperHilbertSchmidtTensor C hC
  let z0 := Spectra.QuantumMechanics.SpectralTheory.spectralGapSolution
    W δ hδ c
  have hz0 : z0 ∈ (Spectra.OneParameterUnitaryGroup.generator W).domain :=
    Spectra.QuantumMechanics.SpectralTheory.spectralGapSolution_mem_generatorDomain W hδ c
  have hgen : Spectra.OneParameterUnitaryGroup.generator W ⟨z0, hz0⟩ = c :=
    Spectra.QuantumMechanics.SpectralTheory.generator_spectralGapSolution
      W hδ c hCgap
  let X0 := Spectra.HilbertSchmidtTensor.toOperator z0
  have hEq0raw := hasClosedSylvesterEquation_of_tensorGenerator
    hA hB hz0 hgen
  have hcOp : Spectra.HilbertSchmidtTensor.toOperator c = C := by
    exact toOperator_paperHilbertSchmidtTensor C hC
  have hEq0 : HasClosedSylvesterEquation A B X0 C := by
    simpa [X0, hcOp] using hEq0raw
  have hhom : HasClosedSylvesterEquation A B (X - X0) 0 := by
    simpa using hEq.sub hEq0
  have hXX0 : X = X0 := sub_eq_zero.mp (hunique hhom)
  have hX0 : IsPaperHilbertSchmidt X0 :=
    isPaperHilbertSchmidt_toOperator z0
  refine ⟨hXX0 ▸ hX0, ?_⟩
  -- `X0` is a local definition, not an equation, so it is unfolded rather
  -- than rewritten with.
  rw [hXX0]
  simp only [X0]
  rw [paperHilbertSchmidtNorm_toOperator]
  calc
    δ * ‖z0‖ ≤ δ * (δ⁻¹ * ‖c‖) :=
      mul_le_mul_of_nonneg_left
        (Spectra.QuantumMechanics.SpectralTheory.norm_spectralGapSolution_le W hδ c) hδ.le
    _ = ‖c‖ := by field_simp
    _ = paperHilbertSchmidtNorm C :=
      norm_paperHilbertSchmidtTensor C hC

end

end ExactSinTheta
end Experimental
end DavisKahan
end TauCeti
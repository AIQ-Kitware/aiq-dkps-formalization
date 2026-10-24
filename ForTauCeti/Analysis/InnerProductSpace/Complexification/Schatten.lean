/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.Complexification.FiniteDimensional
public import ForTauCeti.Analysis.InnerProductSpace.Complexification.FunctionalCalculus
public import ForTauCeti.Analysis.InnerProductSpace.SchattenConjugation

/-! # The real symmetry of Schatten variations on a complexification -/

public section

noncomputable section

namespace TauCeti.RealComplexification

open scoped ComplexConjugate RealComplexification

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- Coordinate conjugation commutes with the operator exponential. -/
theorem conjugateOperator_exp
    (A : RealComplexification E →L[ℂ] RealComplexification E) :
    conjugateOperator (NormedSpace.exp A) = NormedSpace.exp (conjugateOperator A) := by
  let +nondep : NormedAlgebra ℚ
      (RealComplexification E →L[ℂ] RealComplexification E) :=
    .restrictScalars ℚ ℂ _
  simpa only [conjugateOperatorHom_apply] using
    NormedSpace.map_exp conjugateOperatorHom continuous_conjugateOperatorHom A

/-- The Schatten phase gradient of an actual real normal operator is
reversed by coordinate conjugation. -/
theorem conjugateOperator_schattenUnitaryGradient [FiniteDimensional ℝ E]
    (p : ℝ) (U : RealComplexification E →L[ℂ] RealComplexification E)
    [IsStarNormal U] (hU : conjugateOperator U = U) :
    conjugateOperator (schattenUnitaryGradient p U) = -schattenUnitaryGradient p U := by
  have hcomm (z : RealComplexification E) : U (conjugation z) = conjugation (U z) := by
    have h := congrArg (fun T : RealComplexification E →L[ℂ] RealComplexification E =>
      T (conjugation z)) hU
    simpa only [conjugateOperator_apply, conjugation_involutive] using h.symm
  have hG := schattenUnitaryGradient_apply_conjugation p U
    (canonicalConjugation (E := E)).toLinearEquiv.toLinearMap hcomm
  apply ContinuousLinearMap.ext
  intro z
  rw [conjugateOperator_apply]
  have h := hG z
  change schattenUnitaryGradient p U (conjugation z) =
    -conjugation (schattenUnitaryGradient p U z) at h
  rw [h]
  simp

/-- Hermitian directions reversed by conjugation generate real unitary
curves under multiplication by `i`. -/
theorem conjugateOperator_exp_I_smul
    (H : RealComplexification E →L[ℂ] RealComplexification E)
    (hH : conjugateOperator H = -H) (t : ℝ) :
    conjugateOperator (NormedSpace.exp (t • (Complex.I • H))) =
      NormedSpace.exp (t • (Complex.I • H)) := by
  rw [conjugateOperator_exp, conjugateOperator_real_smul,
    conjugateOperator_complex_smul, Complex.conj_I, hH]
  simp

end TauCeti.RealComplexification

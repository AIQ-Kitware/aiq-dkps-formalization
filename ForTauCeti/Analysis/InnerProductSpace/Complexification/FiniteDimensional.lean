/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.Complexification.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Dimensions of the concrete Hilbert complexification -/

public section

namespace TauCeti.RealComplexification

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

instance instFiniteDimensionalReal : FiniteDimensional ℝ (RealComplexification E) :=
  inferInstanceAs (FiniteDimensional ℝ (WithLp 2 (E × E)))

instance instFiniteDimensionalComplex : FiniteDimensional ℂ (RealComplexification E) :=
  Module.Finite.of_restrictScalars_finite ℝ ℂ _

/-- Complexification doubles the real dimension. -/
theorem finrank_real :
    Module.finrank ℝ (RealComplexification E) = 2 * Module.finrank ℝ E := by
  calc
    Module.finrank ℝ (RealComplexification E) = Module.finrank ℝ (E × E) :=
      (WithLp.linearEquiv 2 ℝ (E × E)).finrank_eq
    _ = _ := by rw [Module.finrank_prod]; omega

/-- The complex dimension of the complexification is the original real dimension. -/
theorem finrank_complex :
    Module.finrank ℂ (RealComplexification E) = Module.finrank ℝ E := by
  have h := Module.finrank_mul_finrank ℝ ℂ (RealComplexification E)
  rw [Complex.finrank_real_complex, finrank_real] at h
  omega

end TauCeti.RealComplexification

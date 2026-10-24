/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.SchattenUnitaryVariation

/-!
# Conjugation reverses the Schatten unitary gradient

For a normal operator commuting with a conjugate-linear map, the real
Schatten phase gradient anticommutes with that map. The proof uses the
accepted normal eigenbasis and the conjugation identity for the scalar
phase derivative. No real basis or chosen eigenphases are needed.
-/

public section

noncomputable section

namespace TauCeti

open scoped ComplexConjugate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- A conjugate-linear symmetry of a normal operator reverses its
self-adjoint Schatten phase gradient. -/
theorem schattenUnitaryGradient_apply_conjugation
    (p : ℝ) (U : E →L[ℂ] E) [IsStarNormal U]
    (J : E →ₛₗ[starRingEnd ℂ] E) (hUJ : ∀ x, U (J x) = J (U x)) (x : E) :
    schattenUnitaryGradient p U (J x) = -J (schattenUnitaryGradient p U x) := by
  let := ContinuousLinearMap.isStarNormal_toLinearMap U
  obtain ⟨b, mu, hmu⟩ :=
    LinearMap.exists_orthonormalBasis_apply_eq_smul_of_isStarNormal U.toLinearMap
      (ι := Fin (Module.finrank ℂ E)) (by simp)
  let G := schattenUnitaryGradient p U
  have h : G.toLinearMap.comp J = -(J.comp G.toLinearMap) := by
    apply b.toBasis.ext
    intro i
    have hU : U (b i) = mu i • b i := hmu i
    have hJU : U (J (b i)) = conj (mu i) • J (b i) := by
      rw [hUJ, hU, map_smulₛₗ]
    change G (J (b i)) = -J (G (b i))
    rw [schattenUnitaryGradient_apply_of_apply_eq_smul p U _ _ hJU,
      schattenUnitaryGradient_apply_of_apply_eq_smul p U _ _ hU,
      map_smulₛₗ, schattenPhaseDerivative_conj]
    simp
  exact congrArg (fun T : E →ₛₗ[starRingEnd ℂ] E => T x) h

end TauCeti

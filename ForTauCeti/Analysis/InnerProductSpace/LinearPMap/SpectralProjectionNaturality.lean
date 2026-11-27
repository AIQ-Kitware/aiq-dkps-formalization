/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SpectralMeasure
public import ForTauCeti.Analysis.InnerProductSpace.BorelCalculus.BorelNatural

/-!
# Spectral projections are natural under a unitary intertwiner

A unitary `e` commuting with a self-adjoint partial map `A` commutes with every
spectral projection `E_A(B)`.

The native Cayley intertwining theorem and the spectral commutant of the
bounded Cayley transform give the commutation law. The comparison below
relates the real and complex indicators using `Complex.inverseCayleyCoord`.
-/

public section

open scoped InnerProductSpace

namespace TauCeti
namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)

/-- The real spectral projection equals the complex spectral projection of its
inverse-Cayley preimage. -/
theorem specProjection_eq_specProjC (B : Set ℝ) (hB : MeasurableSet B) :
    specProjection hA B hB =
      BorelCalculus.specProjC (hA.isStarNormal_cayley)
        (Complex.measurable_inverseCayleyCoord hB) := by
  have := hA.isStarNormal_cayley
  rw [specProjection_eq_borelCalculus, BorelCalculus.specProjC_def]
  congr 1
  ext w
  by_cases hw : Complex.inverseCayleyCoord (w : ℂ) ∈ B <;> simp [hw]

/-- **Spectral projections are natural under a unitary intertwiner.**

If the unitary `e` preserves `dom A` and commutes with `A` there, then it commutes
with every spectral projection of `A`. -/
theorem specProjection_apply_of_unitary_intertwines (e : H ≃ₗᵢ[ℂ] H)
    (hmaps : ∀ x : A.domain, e (x : H) ∈ A.domain)
    (hint : ∀ x : A.domain, A ⟨e (x : H), hmaps x⟩ = e (A x))
    (B : Set ℝ) (hB : MeasurableSet B) (x : H) :
    e (specProjection hA B hB x) = specProjection hA B hB (e x) := by
  let X := e.toLinearIsometry.toContinuousLinearMap
  have hX : A.Intertwines A X := ⟨hmaps, fun y => (hint y).symm⟩
  have hcay : Commute X A.cayley :=
    hX.comp_cayley_eq hA.neg_I_mem_resolventSet hA.neg_I_mem_resolventSet
  have := hA.isStarNormal_cayley
  rw [specProjection_def, hA.spectralPVM_proj]
  have hproj := (A.cayley.forall_commute_spectralPVM_proj_iff X).mpr hcay
    ((fun w : _root_.spectrum ℂ A.cayley => Complex.inverseCayleyCoord (w : ℂ)) ⁻¹' B)
    ((Complex.measurable_inverseCayleyCoord.comp measurable_subtypeVal) hB)
  exact DFunLike.congr_fun hproj.eq x

end LinearPMap
end TauCeti

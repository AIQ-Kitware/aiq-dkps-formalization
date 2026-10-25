/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedNonacuteClassification
public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedDefectReplacement
public import DavisKahan.Geometry.Polar.TransportUniqueness

/-!
# Independent phase and defect parameters

Every compatible phase projection and every unitary identification of
the crossed defects determine exactly one ambient transporter. It attains
the global weighted nuclear and Charbonnier minimum. The phase parameter
may have redundant choices on inactive directions; the transporter for
each prescribed pair of parameters is unique.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

omit [FiniteDimensional ℂ E] in
private theorem weighted_relative_eq_of_agree_off_kernel
    (C : E →L[ℂ] E) (hC : IsSelfAdjoint C) (R T S : E ≃ₗᵢ[ℂ] E)
    (hagree : ∀ x ∈ C.kerᗮ, T x = S x) :
    C * (R.trans T.symm : E →L[ℂ] E) = C * (R.trans S.symm : E →L[ℂ] E) := by
  have hCx (x : E) : C x ∈ C.kerᗮ := by
    intro y hy
    change inner ℂ y (C x) = 0
    calc
      inner ℂ y (C x) = inner ℂ (C y) x := (hC.isSymmetric y x).symm
      _ = 0 := by rw [show C y = 0 from hy, inner_zero_left]
  have hcomp : (T : E →L[ℂ] E) * C = (S : E →L[ℂ] E) * C := by
    ext x
    exact hagree (C x) (hCx x)
  have hstar : C * star (T : E →L[ℂ] E) = C * star (S : E →L[ℂ] E) := by
    simpa only [star_mul, hC.star_eq] using congrArg star hcomp
  change C * ((T.symm : E →L[ℂ] E) * (R : E →L[ℂ] E)) =
    C * ((S.symm : E →L[ℂ] E) * (R : E →L[ℂ] E))
  rw [← T.adjoint_eq_symm, ← S.adjoint_eq_symm]
  change C * (star (T : E →L[ℂ] E) * (R : E →L[ℂ] E)) =
    C * (star (S : E →L[ℂ] E) * (R : E →L[ℂ] E))
  rw [← mul_assoc, ← mul_assoc, hstar]

/-- Every pair consisting of a compatible phase projection and an
arbitrary crossed-defect isometry admits a globally optimal weighted
transporter, uniquely determined by these prescribed actions. -/
theorem exists_unique_weighted_transport_from_phase_and_defect_complex
    (a b : ℝ) (hb : 0 < b) (hab : b < a)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L)
    (P : E →L[ℂ] E) (hP : IsStarProjection P)
    (hPR : Commute P (nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL)))
    (hPJ : ∀ x, P (K.reflection x) = K.reflection (P x))
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L) :
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
        nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
          unitary (E →L[ℂ] E))
    let C := Proposition35.section3CosAngleOperator K L
    let U := weightedPhaseFactor a b C
    ∃! T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L ∧
      (∀ x : halmosSourceDefect K L, T x = (D x : E)) ∧
      (∀ y : halmosTargetDefect K L, T y = (D.symm y : E)) ∧
      C * (R.trans T.symm : E →L[ℂ] E) = C * (U * P + star U * (1 - P)) ∧
      UnitarilyInvariantSeminorm.nuclear ℂ E E
        ((a : ℂ) • T.toLinearMap - (b : ℂ) • LinearMap.id) = weightedRotationMinimum a b C ∧
      ∀ S : E ≃ₗᵢ[ℂ] E, K.map S.toLinearMap = L →
        UnitarilyInvariantSeminorm.nuclear ℂ E E
            ((a : ℂ) • T.toLinearMap - (b : ℂ) • LinearMap.id) ≤
          UnitarilyInvariantSeminorm.nuclear ℂ E E
            ((a : ℂ) • S.toLinearMap - (b : ℂ) • LinearMap.id) := by
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
      nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
        unitary (E →L[ℂ] E))
  let C := Proposition35.section3CosAngleOperator K L
  obtain ⟨S, hS, hSphase, hSatt, _⟩ :=
    exists_weighted_transport_from_projection_complex a b hb hab K L hKL P hP hPR hPJ
  obtain ⟨T, hT, hsrc, htgt, hagree, hatt, hmin⟩ :=
    exists_weighted_minimizer_prescribing_defects_complex a b hb hab K L hKL S hS hSatt D
  have hC := ((ContinuousLinearMap.nonneg_iff_isPositive).mp
    (Proposition35.section3CosAngleOperator_nonneg K L)).isSelfAdjoint
  have hphase := (weighted_relative_eq_of_agree_off_kernel C hC R T S hagree).trans
    (congrArg (fun B => C * B) hSphase)
  refine ⟨T, ⟨hT, hsrc, htgt, hphase, hatt, hmin⟩, ?_⟩
  rintro W ⟨_, hWsrc, hWtgt, hWphase, _, _⟩
  exact transport_eq_of_phase_and_defect_actions_complex K L R W T D
    hWsrc hWtgt hsrc htgt (hWphase.trans hphase.symm)

/-- The complete prescribed phase-and-defect family also has a unique
attaining transporter for the literal Charbonnier cost. Its comparison
quantifier ranges over every ambient admissible unitary. -/
theorem exists_unique_smoothed_transport_from_phase_and_defect_complex
    (tau : ℝ) (htau : 0 < tau)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L)
    (P : E →L[ℂ] E) (hP : IsStarProjection P)
    (hPR : Commute P (nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL)))
    (hPJ : ∀ x, P (K.reflection x) = K.reflection (P x))
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L) :
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
        nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
          unitary (E →L[ℂ] E))
    let C := Proposition35.section3CosAngleOperator K L
    let U := weightedPhaseFactor (smoothingRadius tau) (smoothingRadius tau)⁻¹ C
    ∃! T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L ∧
      (∀ x : halmosSourceDefect K L, T x = (D x : E)) ∧
      (∀ y : halmosTargetDefect K L, T y = (D.symm y : E)) ∧
      C * (R.trans T.symm : E →L[ℂ] E) = C * (U * P + star U * (1 - P)) ∧
      smoothedDisplacementCost tau T.toLinearMap = smoothedTransportMinimum tau K L ∧
      ∀ S : E ≃ₗᵢ[ℂ] E, K.map S.toLinearMap = L →
        smoothedDisplacementCost tau T.toLinearMap ≤ smoothedDisplacementCost tau S.toLinearMap := by
  let a := smoothingRadius tau
  have ha : 1 < a := one_lt_smoothingRadius tau htau
  have ha0 : 0 < a := zero_lt_one.trans ha
  obtain ⟨T, ⟨hT, hsrc, htgt, hphase, hatt, hmin⟩, _⟩ :=
    exists_unique_weighted_transport_from_phase_and_defect_complex
      a a⁻¹ (inv_pos.mpr ha0) (((inv_lt_one₀ ha0).mpr ha).trans ha) K L hKL P hP hPR hPJ D
  have hTc := smoothedDisplacementCost_eq_weightedNuclear tau htau
    (Unitary.linearIsometryEquiv.symm T)
  change smoothedDisplacementCost tau T.toLinearMap =
    UnitarilyInvariantSeminorm.nuclear ℂ E E
      ((a : ℂ) • T.toLinearMap - ((a⁻¹ : ℝ) : ℂ) • LinearMap.id) -
        Module.finrank ℂ E * tau at hTc
  refine ⟨T, ⟨hT, hsrc, htgt, hphase, ?_, ?_⟩, ?_⟩
  · rw [hTc, hatt]
    rfl
  · intro S hS
    have hSc := smoothedDisplacementCost_eq_weightedNuclear tau htau
      (Unitary.linearIsometryEquiv.symm S)
    change smoothedDisplacementCost tau S.toLinearMap =
      UnitarilyInvariantSeminorm.nuclear ℂ E E
        ((a : ℂ) • S.toLinearMap - ((a⁻¹ : ℝ) : ℂ) • LinearMap.id) -
          Module.finrank ℂ E * tau at hSc
    rw [hTc, hSc]
    exact sub_le_sub_right (hmin S hS) _
  · rintro W ⟨_, hWsrc, hWtgt, hWphase, _, _⟩
    exact transport_eq_of_phase_and_defect_actions_complex K L _ W T D
      hWsrc hWtgt hsrc htgt (hWphase.trans hphase.symm)

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

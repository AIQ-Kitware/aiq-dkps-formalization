/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedOptimizerNoMixing

/-!
# Rotation commutation after removing the exceptional kernel

The relative phase of a nonacute optimizer need not commute with the
chosen defect completion. Multiplication by the principal cosine removes
that freedom and restores global rotation commutation. This is the
reduction for an intrinsic phase projection on the positive-cosine part.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- For every ambient weighted optimizer, the cosine times its relative
phase commutes with the entire completed canonical rotation. Right angles,
arbitrary multiplicities, and fixed directions are included. -/
theorem minimizing_weighted_transport_cosine_mul_relative_commutes_rotation_complex
    (a b : ℝ) (hb : 0 < b) (hab : b < a)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L)
    (T : E ≃ₗᵢ[ℂ] E) (hT : K.map T.toLinearMap = L)
    (hatt : UnitarilyInvariantSeminorm.nuclear ℂ E E
      ((a : ℂ) • T.toLinearMap - (b : ℂ) • LinearMap.id) =
        weightedRotationMinimum a b (Proposition35.section3CosAngleOperator K L)) :
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
        nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
          unitary (E →L[ℂ] E))
    Commute (Proposition35.section3CosAngleOperator K L * (R.trans T.symm : E →L[ℂ] E))
      (R : E →L[ℂ] E) := by
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
      nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
        unitary (E →L[ℂ] E))
  let C := Proposition35.section3CosAngleOperator K L
  let Z : E →L[ℂ] E := R.trans T.symm
  have hC := ((ContinuousLinearMap.nonneg_iff_isPositive).mp
    (Proposition35.section3CosAngleOperator_nonneg K L)).toLinearMap
  obtain ⟨_, _, _, _, hZC, _⟩ :=
    minimizing_weighted_transport_twisted_average_complex a b hb hab K L hKL T hT hatt
  have hCZ (x : E) : C (Z x) = Z (C x) := (DFunLike.congr_fun hZC.eq x).symm
  have hCR (x : E) : C (R x) = R (C x) :=
    (DFunLike.congr_fun
      (Proposition35.nonacuteDirectRotation_comm_cosine K L
        (finiteCrossedDefectEquiv K L hKL)).eq x).symm
  let e := hC.isSymmetric.eigenvectorBasis rfl
  let c := hC.isSymmetric.eigenvalues rfl
  have he (i) : C (e i) = (c i : ℂ) • e i := hC.isSymmetric.apply_eigenvectorBasis rfl i
  apply ContinuousLinearMap.coe_injective
  apply e.toBasis.ext
  intro i
  change C (Z (R (e i))) = R (C (Z (e i)))
  by_cases hz : c i = 0
  · have hzero : C (e i) = 0 := by rw [he, hz, Complex.ofReal_zero, zero_smul]
    calc
      C (Z (R (e i))) = Z (C (R (e i))) := hCZ _
      _ = Z (R (C (e i))) := congrArg Z (hCR _)
      _ = 0 := by rw [hzero, map_zero, map_zero]
      _ = R (C (Z (e i))) := by rw [hCZ, hzero, map_zero, map_zero]
  · have hcpos : 0 < c i := lt_of_le_of_ne (hC.nonneg_eigenvalues rfl i) (Ne.symm hz)
    have hZR := minimizing_weighted_transport_relative_commutes_rotation_on_positive_cosine_complex
      a b hb hab K L hKL T hT hatt (c i) hcpos (e i) (he i)
    change Z (R (e i)) = R (Z (e i)) at hZR
    rw [hZR]
    exact hCR _

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

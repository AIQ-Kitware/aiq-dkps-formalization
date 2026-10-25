/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SchattenProjectionAttainment
public import DavisKahan.FiniteDimensional.DirectRotation.SchattenDefectReplacement
public import DavisKahan.Geometry.Polar.TransportUniqueness

/-!
# Joint attainment of prescribed Schatten phase and defect parameters

Every compatible phase projection and every crossed-defect identification
occur jointly in one global optimizer. The cosine-weighted relative phase
retains the prescribed phase away from right angles. The actual defect
actions determine the remainder. Each such parameter pair determines
exactly one global optimizer; inactive projection parameters may be redundant.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open scoped ENNReal BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- Every compatible orthogonal phase projection and arbitrary unitary
crossed-defect identification jointly determine exactly one globally
minimizing ambient Schatten transporter. -/
theorem exists_unique_schatten_transport_from_phase_and_defect_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
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
    let F := schattenPhaseFactor p.toReal C
    ∃! T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L ∧
      (∀ x : halmosSourceDefect K L, T x = (D x : E)) ∧
      (∀ y : halmosTargetDefect K L, T y = (D.symm y : E)) ∧
      C * (T.trans R.symm : E →L[ℂ] E) = C * (F * P + star F * (1 - P)) ∧
      UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - T.toLinearMap) ^ p.toReal =
          ∑ i : Fin (Module.finrank ℂ K), phaseMinimum p.toReal (K.principalAngles L i) ∧
      IsMinOn
        (fun V : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
          (LinearMap.id - V.toLinearMap) ^ p.toReal)
        {V | V ∈ unitary (E →L[ℂ] E) ∧ V * K.starProjection * star V = L.starProjection}
        (T : E →L[ℂ] E) := by
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
      nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
        unitary (E →L[ℂ] E))
  let C := Proposition35.section3CosAngleOperator K L
  let F := schattenPhaseFactor p.toReal C
  have hC : IsSelfAdjoint C :=
    (ContinuousLinearMap.nonneg_iff_isPositive.mp
      (Proposition35.section3CosAngleOperator_nonneg K L)).isSelfAdjoint
  have hRC : Commute (R : E →L[ℂ] E) C := by
    change Commute (nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL))
      (Proposition35.section3CosAngleOperator K L)
    rw [Proposition35.section3CosAngleOperator_eq_canonicalAbsoluteValue]
    exact nonacuteDirectRotation_comm_absoluteValue K L _
  have hRsC : Commute (R.symm : E →L[ℂ] E) C := by
    rw [← R.adjoint_eq_symm]
    change Commute (star (R : E →L[ℂ] E)) C
    rw [commute_iff_eq]
    simpa only [star_mul, hC.star_eq] using (congrArg star hRC.eq).symm
  have hcosine (T : E ≃ₗᵢ[ℂ] E) (hT : K.map T.toLinearMap = L)
      (hmin : IsMinOn
        (fun V : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
          (LinearMap.id - V.toLinearMap) ^ p.toReal)
        {V | V ∈ unitary (E →L[ℂ] E) ∧ V * K.starProjection * star V = L.starProjection}
        (T : E →L[ℂ] E)) : Commute (T : E →L[ℂ] E) C := by
    let U := Unitary.linearIsometryEquiv.symm T
    have hmap : K.map (Unitary.linearIsometryEquiv U).toLinearMap = L := by
      simpa only [U, MulEquiv.apply_symm_apply] using hT
    exact Proposition35.commute_section3CosAngleOperator_of_commute_sinAngleOperator K L _
      (commute_sinAngleOperator_of_isLocalMinOn_transports_complex
        p hp hp1 hp2 K L U hmap hmin.isLocalMinOn)
  obtain ⟨S, hS, hSphase, _, hSmin⟩ :=
    exists_schatten_transport_from_projection_complex p hp hp1 hp2 K L hKL P hP hPR hPJ
  let U := Unitary.linearIsometryEquiv.symm S
  have hUmap : K.map (Unitary.linearIsometryEquiv U).toLinearMap = L := by
    simpa only [U, MulEquiv.apply_symm_apply] using hS
  obtain ⟨T, ⟨hT, hsrc, htgt, hagree, hcost, hbound⟩, _⟩ :=
    exists_unique_schatten_minimizer_prescribing_defects_complex p hp hp1 hp2
      K L U hUmap hSmin.isLocalMinOn D
  have hTmin : IsMinOn
      (fun V : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - V.toLinearMap) ^ p.toReal)
      {V | V ∈ unitary (E →L[ℂ] E) ∧ V * K.starProjection * star V = L.starProjection}
      (T : E →L[ℂ] E) := by
    intro V hV
    let V' : unitary (E →L[ℂ] E) := ⟨V, hV.1⟩
    have hh := hbound (Unitary.linearIsometryEquiv V')
      ((map_eq_iff_conjugate_starProjection_complex K L V').mpr hV.2)
    have hcoe : (Unitary.linearIsometryEquiv V').toLinearMap = V.toLinearMap := rfl
    rw [hcoe] at hh
    exact hh
  have hTC := hcosine T hT hTmin
  have hSC := hcosine S hS hSmin
  have hCx (x : E) : C x ∈ C.kerᗮ := by
    intro y hy
    change inner ℂ y (C x) = 0
    calc
      inner ℂ y (C x) = inner ℂ (C y) x := (hC.isSymmetric y x).symm
      _ = 0 := by rw [show C y = 0 from hy, inner_zero_left]
  have hcomp : (T : E →L[ℂ] E) * C = (S : E →L[ℂ] E) * C := by
    ext x
    exact hagree (C x) (hCx x)
  have hleft : C * (T : E →L[ℂ] E) = C * (S : E →L[ℂ] E) :=
    hTC.eq.symm.trans (hcomp.trans hSC.eq)
  have hphase : C * (T.trans R.symm : E →L[ℂ] E) = C * (F * P + star F * (1 - P)) := by
    calc
      _ = (R.symm : E →L[ℂ] E) * (C * (T : E →L[ℂ] E)) := by
        change C * ((R.symm : E →L[ℂ] E) * (T : E →L[ℂ] E)) = _
        rw [← mul_assoc, ← hRsC.eq, mul_assoc]
      _ = (R.symm : E →L[ℂ] E) * (C * (S : E →L[ℂ] E)) := by rw [hleft]
      _ = C * (S.trans R.symm : E →L[ℂ] E) := by
        change _ = C * ((R.symm : E →L[ℂ] E) * (S : E →L[ℂ] E))
        rw [← mul_assoc, hRsC.eq, mul_assoc]
      _ = _ := congrArg (fun A => C * A) hSphase
  refine ⟨T, ⟨hT, hsrc, htgt, hphase, hcost, hTmin⟩, ?_⟩
  rintro W ⟨_, hWsrc, hWtgt, hWphase, _, _⟩
  exact transport_eq_of_right_phase_and_defect_actions_complex K L R W T hRC
    D hWsrc hWtgt hsrc htgt (hWphase.trans hphase.symm)

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

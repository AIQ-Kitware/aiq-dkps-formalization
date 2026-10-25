/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.Complexification.SingularValues
public import ForTauCeti.Analysis.InnerProductSpace.Complexification.FunctionalCalculus
public import Mathlib.Topology.Order.LocalExtr

/-!
# Real unitary transport and conjugation-fixed complex transport

Complexification preserves and reflects unitarity. For finite real spaces
it also preserves the literal Schatten displacement cost. Hence a global
minimum among conjugation-fixed complex transporters descends to a global
minimum among all real transporters. The source operator may be arbitrary.
The operator descent is the existing real-part restriction, not a choice
of principal-plane coordinates.
-/

public section

noncomputable section

namespace TauCeti.RealComplexification

open scoped ENNReal TauCeti.RealComplexification

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Complexification preserves and reflects unitarity, in any complete
real Hilbert space. No finite-dimensional argument is needed. -/
theorem mem_unitary_complexify_iff (T : E →L[ℝ] E) :
    complexify T ∈ unitary
      (RealComplexification E →L[ℂ] RealComplexification E) ↔
        T ∈ unitary (E →L[ℝ] E) := by
  constructor
  · intro hT
    obtain ⟨hl, hr⟩ := Unitary.mem_iff.mp hT
    refine Unitary.mem_iff.mpr ⟨?_, ?_⟩
    · apply complexify_injective
      change complexifyStarAlgHom (star T * T) = complexifyStarAlgHom 1
      simpa only [map_mul, map_star, map_one, complexifyStarAlgHom_apply] using hl
    · apply complexify_injective
      change complexifyStarAlgHom (T * star T) = complexifyStarAlgHom 1
      simpa only [map_mul, map_star, map_one, complexifyStarAlgHom_apply] using hr
  · exact fun hT => Unitary.map_mem complexifyStarAlgHom hT

/-- A conjugation-fixed self-adjoint operator restricts to a real
self-adjoint operator. -/
theorem isSelfAdjoint_realify_of_fixed
    (P : RealComplexification E →L[ℂ] RealComplexification E)
    (hfix : conjugateOperator P = P) (hP : IsSelfAdjoint P) :
    IsSelfAdjoint (realify P) := by
  have hcomplex : complexify (realify P) = P := complexify_realPartOperator hfix
  change star (realify P) = realify P
  apply complexify_injective
  change complexifyStarAlgHom (star (realify P)) = complexify (realify P)
  rw [map_star, complexifyStarAlgHom_apply, hcomplex]
  exact hP

section FiniteDimensional

variable [FiniteDimensional ℝ E]

omit [CompleteSpace E] in
/-- The actual Schatten distance from the identity is unchanged by
complexification, including singular displacements. -/
theorem schatten_displacement_complexify
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (T : E →L[ℝ] E) :
    UnitarilyInvariantSeminorm.schatten ℂ (RealComplexification E) (RealComplexification E) p
      (LinearMap.id - (complexify T).toLinearMap) =
        UnitarilyInvariantSeminorm.schatten ℝ E E p (LinearMap.id - T.toLinearMap) := by
  have hdisp : complexify (1-T) = 1-complexify T := by
    rw [complexify_sub, show complexify (1 : E →L[ℝ] E) = 1 from complexify_id]
  change UnitarilyInvariantSeminorm.schatten ℂ _ _ p
    (1-complexify T).toLinearMap = UnitarilyInvariantSeminorm.schatten ℝ E E p
      (1-T).toLinearMap
  rw [← hdisp]
  exact schatten_complexify p hp _

/-- A global conjugation-fixed complex minimum descends to a global
minimum among every real unitary transporter of the source operator.
This assertion does not replace real feasibility by unrestricted complex
feasibility. -/
theorem isMinOn_real_transport_of_complexify
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (P T : E →L[ℝ] E)
    (hmin : IsMinOn
      (fun W : RealComplexification E →L[ℂ] RealComplexification E =>
        UnitarilyInvariantSeminorm.schatten ℂ (RealComplexification E) (RealComplexification E) p
          (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (RealComplexification E →L[ℂ] RealComplexification E) ∧
        W * complexify P * star W = complexify T * complexify P * star (complexify T) ∧
        conjugateOperator W = W} (complexify T)) :
    IsMinOn
      (fun W : E →L[ℝ] E => UnitarilyInvariantSeminorm.schatten ℝ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℝ] E) ∧ W * P * star W = T * P * star T} T := by
  intro W hW
  have htrans : complexify W * complexify P * star (complexify W) =
      complexify T * complexify P * star (complexify T) := by
    have h := congrArg complexifyStarAlgHom hW.2
    simpa only [map_mul, map_star, complexifyStarAlgHom_apply] using h
  have hle := hmin ⟨(mem_unitary_complexify_iff W).mpr hW.1, htrans,
    conjugateOperator_complexify W⟩
  change UnitarilyInvariantSeminorm.schatten ℂ _ _ p
      (LinearMap.id - (complexify T).toLinearMap) ^ p.toReal ≤
    UnitarilyInvariantSeminorm.schatten ℂ _ _ p
      (LinearMap.id - (complexify W).toLinearMap) ^ p.toReal at hle
  change UnitarilyInvariantSeminorm.schatten ℝ E E p
      (LinearMap.id - T.toLinearMap) ^ p.toReal ≤
    UnitarilyInvariantSeminorm.schatten ℝ E E p
      (LinearMap.id - W.toLinearMap) ^ p.toReal
  simpa only [schatten_displacement_complexify p hp] using hle

/-- A global real minimum is a global minimum among all conjugation-fixed
complex transporters. Every fixed competitor is the complexification of
its actual real restriction; no competitors are discarded. -/
theorem isMinOn_complexify_transport_of_real
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (P T : E →L[ℝ] E)
    (hmin : IsMinOn
      (fun W : E →L[ℝ] E => UnitarilyInvariantSeminorm.schatten ℝ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℝ] E) ∧ W * P * star W = T * P * star T} T) :
    IsMinOn
      (fun W : RealComplexification E →L[ℂ] RealComplexification E =>
        UnitarilyInvariantSeminorm.schatten ℂ (RealComplexification E) (RealComplexification E) p
          (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (RealComplexification E →L[ℂ] RealComplexification E) ∧
        W * complexify P * star W = complexify T * complexify P * star (complexify T) ∧
        conjugateOperator W = W} (complexify T) := by
  intro W hW
  have hWc : complexify (realify W) = W := complexify_realPartOperator hW.2.2
  have hunit : realify W ∈ unitary (E →L[ℝ] E) := by
    apply (mem_unitary_complexify_iff _).mp
    rw [hWc]
    exact hW.1
  have htrans : realify W * P * star (realify W) = T * P * star T := by
    apply complexify_injective
    change complexifyStarAlgHom (realify W * P * star (realify W)) =
      complexifyStarAlgHom (T * P * star T)
    simpa only [map_mul, map_star, complexifyStarAlgHom_apply, hWc] using hW.2.1
  have hle := hmin ⟨hunit, htrans⟩
  change UnitarilyInvariantSeminorm.schatten ℂ _ _ p
      (LinearMap.id - (complexify T).toLinearMap) ^ p.toReal ≤
    UnitarilyInvariantSeminorm.schatten ℂ _ _ p (LinearMap.id - W.toLinearMap) ^ p.toReal
  rw [← hWc, schatten_displacement_complexify p hp,
    schatten_displacement_complexify p hp]
  exact hle

/-- The same descent with complex input operators stated as actual fixed
points of conjugation. -/
theorem isMinOn_realify_transport
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (P U : RealComplexification E →L[ℂ] RealComplexification E)
    (hP : conjugateOperator P = P) (hU : conjugateOperator U = U)
    (hmin : IsMinOn
      (fun W : RealComplexification E →L[ℂ] RealComplexification E =>
        UnitarilyInvariantSeminorm.schatten ℂ (RealComplexification E) (RealComplexification E) p
          (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (RealComplexification E →L[ℂ] RealComplexification E) ∧
        W * P * star W = U * P * star U ∧ conjugateOperator W = W} U) :
    IsMinOn
      (fun W : E →L[ℝ] E => UnitarilyInvariantSeminorm.schatten ℝ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℝ] E) ∧
        W * realify P * star W = realify U * realify P * star (realify U)} (realify U) := by
  have hPc : complexify (realify P) = P := complexify_realPartOperator hP
  have hUc : complexify (realify U) = U := complexify_realPartOperator hU
  apply isMinOn_real_transport_of_complexify p hp
  simpa only [hPc, hUc] using hmin

end FiniteDimensional

end TauCeti.RealComplexification

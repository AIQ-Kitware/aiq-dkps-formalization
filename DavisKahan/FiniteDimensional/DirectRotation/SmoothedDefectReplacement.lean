/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.SmoothedRightDefect
import DavisKahan.FiniteDimensional.DirectRotation.KernelTransportReplacement
import DavisKahan.Geometry.Polar.CanonicalSymmetry

/-!
# Arbitrary right-angle defect identifications attain the global minimum

Any weighted or Charbonnier optimizer can keep its whole positive-cosine
action while replacing the right-angle action by an arbitrary unitary
identification of the actual crossed defects, paired with its inverse.
The ambient extension is constructed and compared with every competitor.
-/

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- The literal Charbonnier cost splits off the whole actual right-angle
kernel with coefficient `eta-tau = (sqrt(tau^2+4)-tau)/2` per dimension.
Only feasibility, cosine preservation, and reflection on the kernel are
assumed; the transporter need not be globally optimal. -/
theorem smoothed_transport_split_cosine_kernel_complex
    (tau : ℝ) (htau : 0 < tau)
    (K L : Submodule ℂ E) (T : E ≃ₗᵢ[ℂ] E) (hT : K.map T.toLinearMap = L)
    (hTC : Commute (T : E →L[ℂ] E) (Proposition35.section3CosAngleOperator K L))
    (hself : ∀ x : E, Proposition35.section3CosAngleOperator K L x = 0 →
      T x = star (T : E →L[ℂ] E) x) :
    let N := (Proposition35.section3CosAngleOperator K L).ker
    ∃ Tpos : Nᗮ ≃ₗᵢ[ℂ] Nᗮ,
      (∀ x : Nᗮ, (Tpos x : E) = T x) ∧
      smoothedDisplacementCost tau T.toLinearMap =
        smoothedDisplacementCost tau Tpos.toLinearMap +
          (smoothingRadius tau - tau) * Module.finrank ℂ N := by
  let a := smoothingRadius tau
  let N := (Proposition35.section3CosAngleOperator K L).ker
  have ha : 1 < a := one_lt_smoothingRadius tau htau
  have ha0 : 0 < a := zero_lt_one.trans ha
  obtain ⟨_, Tpos, _, hTpos, _, hcost⟩ := weighted_transport_split_cosine_kernel
    a a⁻¹ (inv_pos.mpr ha0).le (((inv_lt_one₀ ha0).mpr ha).trans ha).le K L T hT hTC hself
  have hTc := smoothedDisplacementCost_eq_weightedNuclear tau htau
    (Unitary.linearIsometryEquiv.symm T)
  change smoothedDisplacementCost tau T.toLinearMap =
    UnitarilyInvariantSeminorm.nuclear ℂ E E
      ((a : ℂ) • T.toLinearMap - ((a⁻¹ : ℝ) : ℂ) • LinearMap.id) -
        Module.finrank ℂ E * tau at hTc
  have hTpc := smoothedDisplacementCost_eq_weightedNuclear tau htau
    (Unitary.linearIsometryEquiv.symm Tpos)
  change smoothedDisplacementCost tau Tpos.toLinearMap =
    UnitarilyInvariantSeminorm.nuclear ℂ Nᗮ Nᗮ
      ((a : ℂ) • Tpos.toLinearMap - ((a⁻¹ : ℝ) : ℂ) • LinearMap.id) -
        Module.finrank ℂ Nᗮ * tau at hTpc
  change UnitarilyInvariantSeminorm.nuclear ℂ E E
      ((a : ℂ) • T.toLinearMap - ((a⁻¹ : ℝ) : ℂ) • LinearMap.id) =
    UnitarilyInvariantSeminorm.nuclear ℂ Nᗮ Nᗮ
      ((a : ℂ) • Tpos.toLinearMap - ((a⁻¹ : ℝ) : ℂ) • LinearMap.id) +
        a * Module.finrank ℂ N at hcost
  have hdim : (Module.finrank ℂ E : ℝ) =
      (Module.finrank ℂ N : ℝ) + (Module.finrank ℂ Nᗮ : ℝ) := by
    exact_mod_cast N.finrank_add_finrank_orthogonal.symm
  refine ⟨Tpos, hTpos, ?_⟩
  change smoothedDisplacementCost tau T.toLinearMap =
    smoothedDisplacementCost tau Tpos.toLinearMap + (a - tau) * Module.finrank ℂ N
  rw [hTc, hTpc, hcost, hdim]
  ring

/-- Every ambient weighted optimizer has exactly one crossed-defect
isometry parameter, with its inverse on the other defect. -/
theorem minimizing_weighted_transport_unique_defect_equiv_complex
    (a b : ℝ) (hb : 0 < b) (hab : b < a)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L)
    (T : E ≃ₗᵢ[ℂ] E) (hT : K.map T.toLinearMap = L)
    (hatt : UnitarilyInvariantSeminorm.nuclear ℂ E E
      ((a : ℂ) • T.toLinearMap - (b : ℂ) • LinearMap.id) =
        weightedRotationMinimum a b (Proposition35.section3CosAngleOperator K L)) :
    ∃! D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L,
      (∀ x : halmosSourceDefect K L, T x = (D x : E)) ∧
      (∀ y : halmosTargetDefect K L, T y = (D.symm y : E)) :=
  Proposition35.exists_unique_defect_equiv_of_selfAdjoint_on_cosine_kernel K L T hT
    (minimizing_weighted_transport_selfAdjoint_on_right_defect_complex
      a b hb hab K L hKL T hT hatt)

/-- All Charbonnier optimizers, including mixed-angle pairs, have a unique
actual crossed-defect identification paired with its inverse. -/
theorem smoothed_minimizer_unique_defect_equiv_complex
    (tau : ℝ) (htau : 0 < tau)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L)
    (T : E ≃ₗᵢ[ℂ] E) (hT : K.map T.toLinearMap = L)
    (hmin : ∀ A : E ≃ₗᵢ[ℂ] E, K.map A.toLinearMap = L →
      smoothedDisplacementCost tau T.toLinearMap ≤ smoothedDisplacementCost tau A.toLinearMap) :
    ∃! D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L,
      (∀ x : halmosSourceDefect K L, T x = (D x : E)) ∧
      (∀ y : halmosTargetDefect K L, T y = (D.symm y : E)) :=
  Proposition35.exists_unique_defect_equiv_of_selfAdjoint_on_cosine_kernel K L T hT
    (smoothed_minimizer_selfAdjoint_on_right_defect_complex tau htau K L hKL T hT hmin)

/-- Every actual defect isometry and its inverse can replace the defect
action of a weighted optimizer independently of all positive-angle choices.
The result is globally optimal over all ambient transporters. -/
theorem exists_weighted_minimizer_prescribing_defects_complex
    (a b : ℝ) (hb : 0 < b) (hab : b < a)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L)
    (T : E ≃ₗᵢ[ℂ] E) (hT : K.map T.toLinearMap = L)
    (hatt : UnitarilyInvariantSeminorm.nuclear ℂ E E
      ((a : ℂ) • T.toLinearMap - (b : ℂ) • LinearMap.id) =
        weightedRotationMinimum a b (Proposition35.section3CosAngleOperator K L))
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L) :
    ∃ W : E ≃ₗᵢ[ℂ] E, K.map W.toLinearMap = L ∧
      (∀ x : halmosSourceDefect K L, W x = (D x : E)) ∧
      (∀ y : halmosTargetDefect K L, W y = (D.symm y : E)) ∧
      (∀ x ∈ (Proposition35.section3CosAngleOperator K L).kerᗮ, W x = T x) ∧
      UnitarilyInvariantSeminorm.nuclear ℂ E E
        ((a : ℂ) • W.toLinearMap - (b : ℂ) • LinearMap.id) =
          weightedRotationMinimum a b (Proposition35.section3CosAngleOperator K L) ∧
      ∀ A : E ≃ₗᵢ[ℂ] E, K.map A.toLinearMap = L →
        UnitarilyInvariantSeminorm.nuclear ℂ E E
            ((a : ℂ) • W.toLinearMap - (b : ℂ) • LinearMap.id) ≤
          UnitarilyInvariantSeminorm.nuclear ℂ E E
            ((a : ℂ) • A.toLinearMap - (b : ℂ) • LinearMap.id) := by
  let C := Proposition35.section3CosAngleOperator K L
  let N := C.ker
  have hTC := minimizing_weighted_transport_commutes_cosine_complex
    a b hb hab K L hKL T hT hatt
  have hTself := minimizing_weighted_transport_selfAdjoint_on_right_defect_complex
    a b hb hab K L hKL T hT hatt
  obtain ⟨V, hV, hVself, hVC, hVsource, hVtarget⟩ :=
    exists_selfAdjoint_transport_prescribing_defects K L D
  have hVinv : ∀ x ∈ N, V x ∈ N := by
    intro x hx
    change C (V x) = 0
    have h := DFunLike.congr_fun hVC.eq x
    change V (C x) = C (V x) at h
    rw [show C x = 0 from hx, map_zero] at h
    exact h.symm
  obtain ⟨S, hS, _, _⟩ := V.exists_restriction_of_finite_invariant N hVinv
  have hSself : IsSelfAdjoint (S : N →L[ℂ] N) := by
    apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    intro x y
    change inner ℂ (S x : E) (y : E) = inner ℂ (x : E) (S y : E)
    rw [hS, hS]
    exact hVself.isSymmetric x y
  have hanti (x : N) : (S ⟨K.reflection x,
      Proposition35.reflection_mem_cosine_kernel K L x x.property⟩ : E) =
        -K.reflection (S x) := by
    rw [hS, hS]
    exact Proposition35.transport_anticommutes_reflection_on_cosine_kernel K L V hV hVC x
      x.property
  obtain ⟨W, hW, hWC, hWself, hWS, hagree⟩ :=
    exists_transport_replacing_cosine_kernel K L T hT hTC S hSself hanti
  have hWcost : UnitarilyInvariantSeminorm.nuclear ℂ E E
      ((a : ℂ) • W.toLinearMap - (b : ℂ) • LinearMap.id) =
        weightedRotationMinimum a b C :=
    (weighted_transport_cost_eq_of_eq_on_cosine_kernel_orthogonal a b hb.le hab.le
      K L W T hW hT hWC hTC hWself hTself hagree).trans hatt
  have hsource (x : halmosSourceDefect K L) : (x : E) ∈ N := by
    rw [show N = C.ker from rfl,
      Proposition35.ker_section3CosAngleOperator_eq_crossedDefectSum]
    exact Submodule.mem_sup_left x.property
  have htarget (x : halmosTargetDefect K L) : (x : E) ∈ N := by
    rw [show N = C.ker from rfl,
      Proposition35.ker_section3CosAngleOperator_eq_crossedDefectSum]
    exact Submodule.mem_sup_right x.property
  refine ⟨W, hW, ?_, ?_, hagree, hWcost, ?_⟩
  · intro x
    exact (hWS ⟨x, hsource x⟩).trans ((hS _).trans (hVsource x))
  · intro x
    exact (hWS ⟨x, htarget x⟩).trans ((hS _).trans (hVtarget x))
  · intro A hA
    obtain ⟨B, _, hBcost, hBmin⟩ :=
      exists_unitary_minimizing_weighted_transport a b hb hab K L hKL
    rw [hWcost, ← hBcost]
    exact hBmin A hA

/-- An arbitrary unitary identification of the actual crossed defects
occurs in a global Charbonnier optimizer with any given optimizer's entire
positive-cosine action. No right-angle multiplicity or ambient extension
hypothesis is imposed. -/
theorem exists_smoothed_minimizer_prescribing_defects_complex
    (tau : ℝ) (htau : 0 < tau)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L)
    (T : E ≃ₗᵢ[ℂ] E) (hT : K.map T.toLinearMap = L)
    (hmin : ∀ A : E ≃ₗᵢ[ℂ] E, K.map A.toLinearMap = L →
      smoothedDisplacementCost tau T.toLinearMap ≤ smoothedDisplacementCost tau A.toLinearMap)
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L) :
    ∃ W : E ≃ₗᵢ[ℂ] E, K.map W.toLinearMap = L ∧
      (∀ x : halmosSourceDefect K L, W x = (D x : E)) ∧
      (∀ y : halmosTargetDefect K L, W y = (D.symm y : E)) ∧
      (∀ x ∈ (Proposition35.section3CosAngleOperator K L).kerᗮ, W x = T x) ∧
      smoothedDisplacementCost tau W.toLinearMap = smoothedTransportMinimum tau K L ∧
      ∀ A : E ≃ₗᵢ[ℂ] E, K.map A.toLinearMap = L →
        smoothedDisplacementCost tau W.toLinearMap ≤ smoothedDisplacementCost tau A.toLinearMap := by
  let a := smoothingRadius tau
  have ha : 1 < a := one_lt_smoothingRadius tau htau
  have ha0 : 0 < a := zero_lt_one.trans ha
  obtain ⟨W, hW, hs, ht, hagree, hatt, hWmin⟩ :=
    exists_weighted_minimizer_prescribing_defects_complex a a⁻¹
      (inv_pos.mpr ha0) (((inv_lt_one₀ ha0).mpr ha).trans ha) K L hKL T hT
      (smoothed_minimizer_weighted_cost_eq_complex tau htau K L hKL T hT hmin) D
  have hWc := smoothedDisplacementCost_eq_weightedNuclear tau htau
    (Unitary.linearIsometryEquiv.symm W)
  change smoothedDisplacementCost tau W.toLinearMap =
    UnitarilyInvariantSeminorm.nuclear ℂ E E
      ((a : ℂ) • W.toLinearMap - ((a⁻¹ : ℝ) : ℂ) • LinearMap.id) -
        Module.finrank ℂ E * tau at hWc
  refine ⟨W, hW, hs, ht, hagree, ?_, ?_⟩
  · rw [hWc, hatt]
    rfl
  · intro A hA
    have hAc := smoothedDisplacementCost_eq_weightedNuclear tau htau
      (Unitary.linearIsometryEquiv.symm A)
    change smoothedDisplacementCost tau A.toLinearMap =
      UnitarilyInvariantSeminorm.nuclear ℂ E E
        ((a : ℂ) • A.toLinearMap - ((a⁻¹ : ℝ) : ℂ) • LinearMap.id) -
          Module.finrank ℂ E * tau at hAc
    rw [hWc, hAc]
    exact sub_le_sub_right (hWmin A hA) _

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

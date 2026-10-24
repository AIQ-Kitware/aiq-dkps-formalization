/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.SmoothedRotationOptimization
import DavisKahan.FiniteDimensional.DirectRotation.SmoothedSpectralCost
import DavisKahan.FiniteDimensional.DirectRotation.ComplexCrossedDefects
import DavisKahan.Geometry.Polar.NonacuteCompression
import ForTauCeti.Analysis.InnerProductSpace.Projection.UnitaryTransport

/-!
# Exact smoothed transport for arbitrary equal-rank subspaces

The completed nonacute rotation supplies the operator hypotheses of the
weighted nuclear optimizer. No principal-coordinate decomposition is assumed.
-/

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

attribute [local instance 100] ContinuousLinearMap.realAlgebra
  ContinuousLinearMap.realIsScalarTower ContinuousLinearMap.continuousFunctionalCalculusReal
attribute [local instance] ContinuousLinearMap.instStarOrderedRingRCLike

private theorem canonical_rotation_model
    (U V : Submodule ℂ E)
    (D : halmosSourceDefect U V ≃ₗᵢ[ℂ] halmosTargetDefect U V) :
    let R := nonacuteDirectRotation U V D
    let C := Proposition35.section3CosAngleOperator U V
    let B := -Complex.I • (R - C)
    C.toLinearMap.IsPositive ∧ B.toLinearMap.IsSymmetric ∧
      (∀ x, R x = C x + Complex.I • B x) ∧
      C.toLinearMap * C.toLinearMap + B.toLinearMap * B.toLinearMap = 1 ∧
      (∀ x, B (U.reflection x) = -U.reflection (B x)) := by
  let R := nonacuteDirectRotation U V D
  let C := Proposition35.section3CosAngleOperator U V
  let K := R - C
  let B := -Complex.I • K
  have hC : C.toLinearMap.IsPositive :=
    ((ContinuousLinearMap.nonneg_iff_isPositive).mp
      (Proposition35.section3CosAngleOperator_nonneg U V)).toLinearMap
  have hK : star K = -K := Proposition35.star_nonacuteDirectRotation_sub_cosine U V D
  have hB : IsSelfAdjoint B := by
    change star (-Complex.I • K) = -Complex.I • K
    rw [star_smul, hK]
    simp
  have hBsq : B * B = -(K * K) := by
    change (-Complex.I • K) * (-Complex.I • K) = _
    rw [smul_mul_assoc, mul_smul_comm, smul_smul]
    simp
  refine ⟨hC, ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hB, ?_, ?_, ?_⟩
  · intro x
    change R x = C x + Complex.I • (-Complex.I • K x)
    rw [smul_smul]
    simp only [mul_neg, Complex.I_mul_I, neg_neg, one_smul]
    change R x = C x + (R x - C x)
    abel
  · have h := nonacuteDirectRotation_cosine_sq_sub_skew_sq U V D
    change C * C - K * K = 1 at h
    have hpy : C * C + B * B = 1 := by
      rw [hBsq]
      simpa only [sub_eq_add_neg] using h
    exact congrArg ContinuousLinearMap.toLinearMap hpy
  · intro x
    change -Complex.I • K (U.reflection x) = -U.reflection (-Complex.I • K x)
    rw [show K (U.reflection x) = -U.reflection (K x) from
      nonacuteDirectRotation_skew_reflection U V D x, map_smul]
    simp

/-- Every equal-rank complex subspace pair has a paired eigenbasis of its
completed canonical rotation, with matching cosine eigenvalues and source
reflection exchanging each positive-negative eigenphase pair. -/
theorem exists_subspace_paired_rotation_reflection_basis_complex
    (U V : Submodule ℂ E) (hUV : Module.finrank ℂ U = Module.finrank ℂ V) :
    let R := nonacuteDirectRotation U V (finiteCrossedDefectEquiv U V hUV)
    ∃ n m : ℕ, ∃ (e : OrthonormalBasis ((Fin 2 × Fin n) ⊕ Fin m) ℂ E)
      (theta : Fin n → ℝ) (eps : Fin m → ℝ),
      (∀ i, theta i ∈ Set.Ioc 0 (Real.pi / 2)) ∧
      (∀ i, Proposition35.section3CosAngleOperator U V (e (.inl (0, i))) =
        (Real.cos (theta i) : ℂ) • e (.inl (0, i))) ∧
      (∀ i, Proposition35.section3CosAngleOperator U V (e (.inl (1, i))) =
        (Real.cos (theta i) : ℂ) • e (.inl (1, i))) ∧
      (∀ j, Proposition35.section3CosAngleOperator U V (e (.inr j)) = e (.inr j)) ∧
      (∀ i, R (e (.inl (0, i))) =
        Complex.exp ((theta i : ℂ) * Complex.I) • e (.inl (0, i))) ∧
      (∀ i, R (e (.inl (1, i))) =
        Complex.exp ((-theta i : ℝ) * Complex.I) • e (.inl (1, i))) ∧
      (∀ j, R (e (.inr j)) = e (.inr j)) ∧
      (∀ i, U.reflection (e (.inl (0, i))) = e (.inl (1, i))) ∧
      (∀ j, U.reflection (e (.inr j)) = (eps j : ℂ) • e (.inr j)) := by
  let D := finiteCrossedDefectEquiv U V hUV
  let R := nonacuteDirectRotation U V D
  let C := Proposition35.section3CosAngleOperator U V
  let B := -Complex.I • (R - C)
  let R' := Unitary.linearIsometryEquiv (⟨R, nonacuteDirectRotation_mem_unitary U V D⟩ :
    unitary (E →L[ℂ] E))
  obtain ⟨hC, hB, hR, hpy, hanti⟩ := canonical_rotation_model U V D
  obtain ⟨n, m, e, theta, eps, hθ, hC0, hC1, hCf, hR0, hR1, hRf, hJ0, hJf⟩ :=
    exists_paired_rotation_eigenbasis R' U.reflection C.toLinearMap B.toLinearMap
      hC hB hR hpy U.reflection_involutive hanti
  exact ⟨n, m, e, theta, eps, hθ, hC0, hC1, hCf, hR0, hR1, hRf, hJ0, hJf⟩

/-- Every orthogonal projection commuting with the canonical rotation and
source reflection admits a common paired rotation frame. Its eigenvalue is
zero or one on each pair, with the same value on its two reflected halves. -/
theorem exists_subspace_paired_rotation_projection_basis_complex
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L)
    (P : E →L[ℂ] E) (hP : IsStarProjection P)
    (hPR : Commute P (nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL)))
    (hPJ : ∀ x, P (K.reflection x) = K.reflection (P x)) :
    let R := nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL)
    Commute P (Proposition35.section3CosAngleOperator K L) ∧
    ∃ n m : ℕ, ∃ (e : OrthonormalBasis ((Fin 2 × Fin n) ⊕ Fin m) ℂ E)
      (theta : Fin n → ℝ) (eps : Fin m → ℝ) (sign : Fin n → Bool),
      (∀ i, theta i ∈ Set.Ioc 0 (Real.pi / 2)) ∧
      (∀ i, Proposition35.section3CosAngleOperator K L (e (.inl (0, i))) =
        (Real.cos (theta i) : ℂ) • e (.inl (0, i))) ∧
      (∀ i, Proposition35.section3CosAngleOperator K L (e (.inl (1, i))) =
        (Real.cos (theta i) : ℂ) • e (.inl (1, i))) ∧
      (∀ j, Proposition35.section3CosAngleOperator K L (e (.inr j)) = e (.inr j)) ∧
      (∀ i, R (e (.inl (0, i))) =
        Complex.exp ((theta i : ℂ) * Complex.I) • e (.inl (0, i))) ∧
      (∀ i, R (e (.inl (1, i))) =
        Complex.exp ((-theta i : ℝ) * Complex.I) • e (.inl (1, i))) ∧
      (∀ j, R (e (.inr j)) = e (.inr j)) ∧
      (∀ i, K.reflection (e (.inl (0, i))) = e (.inl (1, i))) ∧
      (∀ j, K.reflection (e (.inr j)) = (eps j : ℂ) • e (.inr j)) ∧
      ∀ r i, P (e (.inl (r, i))) = (if sign i then (1 : ℂ) else 0) • e (.inl (r, i)) := by
  classical
  let D := finiteCrossedDefectEquiv K L hKL
  let R := nonacuteDirectRotation K L D
  let C := Proposition35.section3CosAngleOperator K L
  let B := -Complex.I • (R - C)
  have hPRs : Commute P (star R) := by
    change P * star R = star R * P
    simpa only [star_mul, hP.isSelfAdjoint.star_eq] using (congrArg star hPR.eq).symm
  have hPC : Commute P C := by
    have h := (hPR.add_right hPRs).eq
    change P * (R + star R) = (R + star R) * P at h
    rw [nonacuteDirectRotation_add_star_eq_two_cosine K L D] at h
    apply smul_right_injective (E →L[ℂ] E) (by norm_num : (2 : ℂ) ≠ 0)
    change (2 : ℂ) • (P * C) = (2 : ℂ) • (C * P)
    simpa only [two_smul, mul_add, add_mul] using h
  have hPB : Commute B P := ((hPR.sub_right hPC).smul_right (-Complex.I)).symm
  let R' := Unitary.linearIsometryEquiv (⟨R, nonacuteDirectRotation_mem_unitary K L D⟩ :
    unitary (E →L[ℂ] E))
  obtain ⟨hC, hB, hR, hpy, hanti⟩ := canonical_rotation_model K L D
  obtain ⟨n, m, e, theta, eps, nu, hθ, hC0, hC1, hCf, hR0, hR1, hRf, hJ0, hJf, hPe⟩ :=
    exists_paired_rotation_joint_eigenbasis R' K.reflection C.toLinearMap B.toLinearMap
      P.toLinearMap hC hB hR hpy K.reflection_involutive hanti hP.isSelfAdjoint.isSymmetric
      (show Commute B.toLinearMap P.toLinearMap from
        congrArg ContinuousLinearMap.toLinearMap hPB.eq) hPJ
  have hnu (i : Fin n) : nu i = 0 ∨ nu i = 1 := by
    have h := congrArg (fun A : E →L[ℂ] E => A (e (.inl (0, i)))) hP.isIdempotentElem.eq
    change P (P (e (.inl (0, i)))) = P (e (.inl (0, i))) at h
    rw [show P (e (.inl (0, i))) = _ from hPe 0 i, map_smul,
      show P (e (.inl (0, i))) = _ from hPe 0 i, smul_smul] at h
    have heq := smul_left_injective ℂ (e.orthonormal.ne_zero (.inl (0, i))) h
    have hfac : nu i * (nu i - 1) = 0 := by calc
      _ = nu i * nu i - nu i := by ring
      _ = 0 := sub_eq_zero.mpr heq
    exact (mul_eq_zero.mp hfac).imp id sub_eq_zero.mp
  refine ⟨hPC, n, m, e, theta, eps, fun i => decide (nu i = 1), hθ,
    hC0, hC1, hCf, hR0, hR1, hRf, hJ0, hJf, ?_⟩
  intro r i
  have hp : P (e (.inl (r, i))) = nu i • e (.inl (r, i)) := hPe r i
  rcases hnu i with hi | hi
  · simpa [hi] using hp
  · simpa [hi] using hp

/-- The completed canonical rotation admits paired eigenphases and
matching cosine eigenvalues, including its right-angle planes. -/
theorem exists_subspace_paired_rotation_basis
    (U V : Submodule ℂ E) (hUV : Module.finrank ℂ U = Module.finrank ℂ V) :
    let R := nonacuteDirectRotation U V (finiteCrossedDefectEquiv U V hUV)
    ∃ n m : ℕ, ∃ (e : OrthonormalBasis ((Fin 2 × Fin n) ⊕ Fin m) ℂ E)
      (theta : Fin n → ℝ),
      (∀ i, theta i ∈ Set.Ioc 0 (Real.pi / 2)) ∧
      (∀ i, Proposition35.section3CosAngleOperator U V (e (.inl (0, i))) =
        (Real.cos (theta i) : ℂ) • e (.inl (0, i))) ∧
      (∀ i, Proposition35.section3CosAngleOperator U V (e (.inl (1, i))) =
        (Real.cos (theta i) : ℂ) • e (.inl (1, i))) ∧
      (∀ j, Proposition35.section3CosAngleOperator U V (e (.inr j)) = e (.inr j)) ∧
      (∀ i, R (e (.inl (0, i))) =
        Complex.exp ((theta i : ℂ) * Complex.I) • e (.inl (0, i))) ∧
      (∀ i, R (e (.inl (1, i))) =
        Complex.exp ((-theta i : ℝ) * Complex.I) • e (.inl (1, i))) ∧
      (∀ j, R (e (.inr j)) = e (.inr j)) ∧
      (∀ i, U.reflection (e (.inl (0, i))) = e (.inl (1, i))) := by
  obtain ⟨n, m, e, theta, _, hθ, hC0, hC1, hCf, hR0, hR1, hRf, hJ0, _⟩ :=
    exists_subspace_paired_rotation_reflection_basis_complex U V hUV
  exact ⟨n, m, e, theta, hθ, hC0, hC1, hCf, hR0, hR1, hRf, hJ0⟩

/-- Every equal-rank complex subspace pair has a paired cosine eigenbasis
whose pairs are exchanged by reflection in the source. -/
theorem exists_subspace_paired_cosine_basis
    (U V : Submodule ℂ E) (hUV : Module.finrank ℂ U = Module.finrank ℂ V) :
    ∃ n m : ℕ, ∃ (e : OrthonormalBasis ((Fin 2 × Fin n) ⊕ Fin m) ℂ E)
      (theta : Fin n → ℝ),
      (∀ i, theta i ∈ Set.Ioc 0 (Real.pi / 2)) ∧
      (∀ i, Proposition35.section3CosAngleOperator U V (e (.inl (0, i))) =
        (Real.cos (theta i) : ℂ) • e (.inl (0, i))) ∧
      (∀ i, Proposition35.section3CosAngleOperator U V (e (.inl (1, i))) =
        (Real.cos (theta i) : ℂ) • e (.inl (1, i))) ∧
      (∀ j, Proposition35.section3CosAngleOperator U V (e (.inr j)) = e (.inr j)) ∧
      (∀ i, U.reflection (e (.inl (0, i))) = e (.inl (1, i))) := by
  obtain ⟨n, m, e, theta, hθ, hC0, hC1, hCf, _, _, _, hJ0⟩ :=
    exists_subspace_paired_rotation_basis U V hUV
  exact ⟨n, m, e, theta, hθ, hC0, hC1, hCf, hJ0⟩

/-- The canonical rotation of any equal-rank pair admits an exact weighted
nuclear approximation by a unitary commuting with the source reflection.
The same unitary minimizes over all commuting contractions. -/
theorem exists_unitary_minimizing_subspace_commutant
    (a b : ℝ) (hb : 0 < b) (hab : b < a)
    (U V : Submodule ℂ E) (hUV : Module.finrank ℂ U = Module.finrank ℂ V) :
    let D := finiteCrossedDefectEquiv U V hUV
    let R := nonacuteDirectRotation U V D
    ∃ Z : E ≃ₗᵢ[ℂ] E,
      (∀ x, Z (U.reflection x) = U.reflection (Z x)) ∧
      UnitarilyInvariantSeminorm.nuclear ℂ E E
        ((a : ℂ) • R.toLinearMap - (b : ℂ) • Z.toLinearMap) =
          weightedRotationMinimum a b (Proposition35.section3CosAngleOperator U V) ∧
      ∀ T : E →L[ℂ] E, ‖T‖ ≤ 1 →
        (∀ x, T (U.reflection x) = U.reflection (T x)) →
        UnitarilyInvariantSeminorm.nuclear ℂ E E
            ((a : ℂ) • R.toLinearMap - (b : ℂ) • Z.toLinearMap) ≤
          UnitarilyInvariantSeminorm.nuclear ℂ E E
            ((a : ℂ) • R.toLinearMap - (b : ℂ) • T.toLinearMap) := by
  let D := finiteCrossedDefectEquiv U V hUV
  let R := nonacuteDirectRotation U V D
  let C := Proposition35.section3CosAngleOperator U V
  let B := -Complex.I • (R - C)
  let R' := Unitary.linearIsometryEquiv (⟨R, nonacuteDirectRotation_mem_unitary U V D⟩ :
    unitary (E →L[ℂ] E))
  obtain ⟨hC, hB, hR, hpy, hanti⟩ := canonical_rotation_model U V D
  exact exists_unitary_minimizing_weightedRotation a b hb hab R' U.reflection
    C.toLinearMap B.toLinearMap hC hB hR hpy U.reflection_involutive hanti

omit [CompleteSpace E] in
private theorem weighted_nuclear_right_quotient
    (a b : ℝ) (R Z : E ≃ₗᵢ[ℂ] E) :
    UnitarilyInvariantSeminorm.nuclear ℂ E E
        ((a : ℂ) • (Z.symm.trans R).toLinearMap - (b : ℂ) • LinearMap.id) =
      UnitarilyInvariantSeminorm.nuclear ℂ E E
        ((a : ℂ) • R.toLinearMap - (b : ℂ) • Z.toLinearMap) := by
  have hfactor :
      (a : ℂ) • (Z.symm.trans R).toLinearMap - (b : ℂ) • LinearMap.id =
        ((a : ℂ) • R.toLinearMap - (b : ℂ) • Z.toLinearMap) ∘ₗ Z.symm.toLinearMap := by
    ext x
    simp
  rw [hfactor]
  exact (UnitarilyInvariantSeminorm.nuclear ℂ E E).map_comp_linearIsometryEquiv Z.symm _

/-- The exact weighted nuclear transport minimum for arbitrary equal-rank
complex subspaces. The competitors are all ambient unitaries carrying the
source onto the target; mixing different principal planes cannot improve
the spectral-trace value. -/
theorem exists_unitary_minimizing_weighted_transport
    (a b : ℝ) (hb : 0 < b) (hab : b < a)
    (U V : Submodule ℂ E) (hUV : Module.finrank ℂ U = Module.finrank ℂ V) :
    ∃ W : E ≃ₗᵢ[ℂ] E,
      U.map W.toLinearMap = V ∧
      UnitarilyInvariantSeminorm.nuclear ℂ E E
        ((a : ℂ) • W.toLinearMap - (b : ℂ) • LinearMap.id) =
          weightedRotationMinimum a b (Proposition35.section3CosAngleOperator U V) ∧
      ∀ T : E ≃ₗᵢ[ℂ] E, U.map T.toLinearMap = V →
        UnitarilyInvariantSeminorm.nuclear ℂ E E
            ((a : ℂ) • W.toLinearMap - (b : ℂ) • LinearMap.id) ≤
          UnitarilyInvariantSeminorm.nuclear ℂ E E
            ((a : ℂ) • T.toLinearMap - (b : ℂ) • LinearMap.id) := by
  let D := finiteCrossedDefectEquiv U V hUV
  let Rop := nonacuteDirectRotation U V D
  let R := Unitary.linearIsometryEquiv
    (⟨Rop, nonacuteDirectRotation_mem_unitary U V D⟩ : unitary (E →L[ℂ] E))
  have hRref (x : E) : R (U.reflection x) = V.reflection (R x) := by
    exact nonacuteDirectRotation_reflection_intertwines U V D x
  obtain ⟨Z, hZcomm, hcost, hmin⟩ :=
    exists_unitary_minimizing_subspace_commutant a b hb hab U V hUV
  have hZinv (x : E) : Z.symm (U.reflection x) = U.reflection (Z.symm x) := by
    apply Z.injective
    rw [Z.apply_symm_apply, hZcomm, Z.apply_symm_apply]
  let W := Z.symm.trans R
  have hWmap : U.map W.toLinearMap = V := by
    apply (Submodule.map_eq_iff_intertwines_reflection U V W).mpr
    intro x
    change R (Z.symm (U.reflection x)) = V.reflection (R (Z.symm x))
    rw [hZinv, hRref]
  have hWcost := weighted_nuclear_right_quotient a b R Z
  refine ⟨W, hWmap, hWcost.trans hcost, ?_⟩
  intro T hT
  have hTref := (Submodule.map_eq_iff_intertwines_reflection U V T).mp hT
  let Z' := R.trans T.symm
  have hZ'comm (x : E) : Z' (U.reflection x) = U.reflection (Z' x) := by
    apply T.injective
    change T (T.symm (R (U.reflection x))) = T (U.reflection (T.symm (R x)))
    rw [T.apply_symm_apply, hTref, T.apply_symm_apply, hRref]
  have hbound := hmin (Z' : E →L[ℂ] E)
    Z'.toLinearIsometry.norm_toContinuousLinearMap_le hZ'comm
  have hquot : Z'.symm.trans R = T := by
    ext x
    simp [Z']
  calc
    _ = UnitarilyInvariantSeminorm.nuclear ℂ E E
        ((a : ℂ) • R.toLinearMap - (b : ℂ) • Z.toLinearMap) := hWcost
    _ ≤ UnitarilyInvariantSeminorm.nuclear ℂ E E
        ((a : ℂ) • R.toLinearMap - (b : ℂ) • Z'.toLinearMap) := hbound
    _ = _ := by rw [← weighted_nuclear_right_quotient a b R Z', hquot]

/-- The exact smoothed transport value as a spectral function of `cos Θ`.
The ambient zero-singular-value contribution is subtracted explicitly. -/
def smoothedTransportMinimum (tau : ℝ) (U V : Submodule ℂ E) : ℝ :=
  weightedRotationMinimum (smoothingRadius tau) (smoothingRadius tau)⁻¹
      (Proposition35.section3CosAngleOperator U V) - Module.finrank ℂ E * tau

/-- The literal Charbonnier singular-value cost has an attaining global
minimum for every equal-rank complex subspace pair, with its exact value
given by the explicit spectral trace. No restriction to scalar phases or
to competitors preserving principal planes is imposed. -/
theorem exists_unitary_minimizing_smoothed_transport
    (tau : ℝ) (hτ : 0 < tau)
    (U V : Submodule ℂ E) (hUV : Module.finrank ℂ U = Module.finrank ℂ V) :
    ∃ W : E ≃ₗᵢ[ℂ] E,
      U.map W.toLinearMap = V ∧
      smoothedDisplacementCost tau W.toLinearMap = smoothedTransportMinimum tau U V ∧
      ∀ T : E ≃ₗᵢ[ℂ] E, U.map T.toLinearMap = V →
        smoothedDisplacementCost tau W.toLinearMap ≤
          smoothedDisplacementCost tau T.toLinearMap := by
  let a := smoothingRadius tau
  have ha : 1 < a := one_lt_smoothingRadius tau hτ
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have hab : a⁻¹ < a := lt_trans ((inv_lt_one₀ ha0).mpr ha) ha
  have hcost (T : E ≃ₗᵢ[ℂ] E) :
      smoothedDisplacementCost tau T.toLinearMap =
        UnitarilyInvariantSeminorm.nuclear ℂ E E
          ((a : ℂ) • T.toLinearMap - ((a⁻¹ : ℝ) : ℂ) • LinearMap.id) -
            Module.finrank ℂ E * tau :=
    smoothedDisplacementCost_eq_weightedNuclear tau hτ (Unitary.linearIsometryEquiv.symm T)
  obtain ⟨W, hWmap, hWcost, hmin⟩ :=
    exists_unitary_minimizing_weighted_transport a a⁻¹ (inv_pos.mpr ha0) hab U V hUV
  refine ⟨W, hWmap, ?_, ?_⟩
  · rw [hcost, hWcost]
    rfl
  · intro T hT
    rw [hcost, hcost]
    exact sub_le_sub_right (hmin T hT) _

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

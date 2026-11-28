/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.KyFan
public import Mathlib.Analysis.InnerProductSpace.Trace
public import ForTauCeti.Analysis.InnerProductSpace.SchattenSpectralCalculus
import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Nuclear.Maximizers

/-!
# Nuclear norm support by unitary trace pairings

TauCeti's contraction trace bound supplies the unitary support inequality.
Its characterization of attaining contractions supplies the positivity
criterion for equality in the real trace bound.
-/

public section

noncomputable section

namespace TauCeti

open scoped InnerProductSpace
open UnitarilyInvariantSeminorm (opNorm opNorm_apply norm_trace_adjoint_comp_le_opNorm_mul_nuclear
  re_trace_adjoint_comp_eq_nuclear_iff)

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- Every isometric change of source coordinates defines a unitary trace
support functional for the nuclear norm. -/
theorem re_trace_isometry_comp_le_nuclear (U : E ≃ₗᵢ[𝕜] E) (A : E →ₗ[𝕜] E) :
    RCLike.re (LinearMap.trace 𝕜 E (U.toLinearMap ∘ₗ A)) ≤
      UnitarilyInvariantSeminorm.nuclear 𝕜 E E A := by
  have hD : opNorm 𝕜 E E U.symm.toLinearMap ≤ 1 := by
    rw [opNorm_apply]
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    change ‖U.symm x‖ ≤ 1 * ‖x‖
    rw [U.symm.norm_map, one_mul]
  have h := norm_trace_adjoint_comp_le_opNorm_mul_nuclear U.symm.toLinearMap A
  rw [LinearIsometryEquiv.adjoint_toLinearMap_eq_symm, LinearIsometryEquiv.symm_symm] at h
  exact (RCLike.re_le_norm _).trans (h.trans (mul_le_of_le_one_left (apply_nonneg _ _) hD))

/-- A complete orthonormal family gives a real nuclear-norm support bound. -/
theorem re_sum_inner_le_nuclear {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι 𝕜 E) (A : E →ₗ[𝕜] E)
    (u : ι → E) (hu : Orthonormal 𝕜 u) :
    (∑ i, RCLike.re ⟪u i, A (b i)⟫_𝕜) ≤
      UnitarilyInvariantSeminorm.nuclear 𝕜 E E A := by
  calc
    _ = RCLike.re (∑ i, ⟪u i, A (b i)⟫_𝕜) := (map_sum _ _ _).symm
    _ ≤ ‖∑ i, ⟪u i, A (b i)⟫_𝕜‖ := RCLike.re_le_norm _
    _ ≤ A.kyFanSum (Fintype.card ι) := A.norm_sum_inner_le_kyFanSum hu b.orthonormal
    _ = _ := A.kyFanSum_eq_nuclear (by
      rw [← Module.finrank_eq_card_basis b.toBasis]
      exact LinearMap.finrank_range_le A)

/-- The nuclear norm of a diagonalizable normal map is the sum of the
absolute eigenvalues, in any finite orthonormal eigenbasis. -/
theorem nuclear_eq_sum_norm_eigenvalues {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι 𝕜 E) (A : E →ₗ[𝕜] E) (mu : ι → 𝕜)
    (hA : ∀ i, A (b i) = mu i • b i) :
    UnitarilyInvariantSeminorm.nuclear 𝕜 E E A = ∑ i, ‖mu i‖ := by
  simpa only [ENNReal.toReal_one, Real.rpow_one, UnitarilyInvariantSeminorm.schatten_one] using
    schatten_rpow_eq_sum_norm_eigenvalues b A mu hA 1 ENNReal.one_ne_top

/-- Equality in the real trace bound holds exactly for positive operators.
Zero singular values and the zero-dimensional space are included. -/
theorem re_trace_eq_nuclear_iff_isPositive (A : E →ₗ[𝕜] E) :
    RCLike.re (LinearMap.trace 𝕜 E A) =
      UnitarilyInvariantSeminorm.nuclear 𝕜 E E A ↔ A.IsPositive := by
  have hD : opNorm 𝕜 E E (LinearMap.id : E →ₗ[𝕜] E) ≤ 1 := by
    rw [opNorm_apply]
    exact ContinuousLinearMap.norm_id_le
  have h := re_trace_adjoint_comp_eq_nuclear_iff (A := A) hD
  rw [LinearMap.adjoint_id, LinearMap.id_comp, LinearMap.id_comp] at h
  exact h.trans ⟨fun hA => hA ▸ A.isPositive_operatorAbs,
    fun hA => (hA.eq_operatorAbs (by rw [hA.adjoint_eq])).symm⟩

/-- Equality in a unitary nuclear support functional is positivity after
the corresponding change of target coordinates. -/
theorem re_trace_isometry_comp_eq_nuclear_iff_isPositive
    (U : E ≃ₗᵢ[𝕜] E) (A : E →ₗ[𝕜] E) :
    RCLike.re (LinearMap.trace 𝕜 E (U.toLinearMap ∘ₗ A)) =
      UnitarilyInvariantSeminorm.nuclear 𝕜 E E A ↔
        (U.toLinearMap ∘ₗ A).IsPositive := by
  rw [← (UnitarilyInvariantSeminorm.nuclear 𝕜 E E).map_linearIsometryEquiv_comp U A]
  exact re_trace_eq_nuclear_iff_isPositive _

omit [FiniteDimensional 𝕜 E] in
/-- The trace of an operator reversed by an involution vanishes. This
algebraic symmetry requires no spectral decomposition. -/
theorem trace_eq_zero_of_anticommute_involution
    (A : E →ₗ[𝕜] E) (J : E ≃ₗᵢ[𝕜] E) (hJ : Function.Involutive J)
    (hanti : ∀ x, A (J x) = -J (A x)) : LinearMap.trace 𝕜 E A = 0 := by
  have hJJ : J.toLinearMap * J.toLinearMap = 1 := by ext x; exact hJ x
  have hconj : J.toLinearMap * A * J.toLinearMap = -A := by
    ext x
    change J (A (J x)) = -A x
    rw [hanti, map_neg, hJ]
  have h := LinearMap.trace_mul_cycle 𝕜 J.toLinearMap A J.toLinearMap
  rw [hconj, hJJ, one_mul, map_neg] at h
  exact CharZero.neg_eq_self_iff.mp h

/-- The weighted nuclear displacement of a self-adjoint unitary is an
affine function of its trace, for `0 ≤ b ≤ a`. -/
theorem nuclear_weighted_selfAdjoint_unitary [CompleteSpace E]
    (a b : ℝ) (hb : 0 ≤ b) (hab : b ≤ a)
    (U : unitary (E →L[𝕜] E)) (hU : IsSelfAdjoint (U : E →L[𝕜] E)) :
    UnitarilyInvariantSeminorm.nuclear 𝕜 E E
        ((a : 𝕜) • (U : E →L[𝕜] E).toLinearMap - (b : 𝕜) • LinearMap.id) =
      a * Module.finrank 𝕜 E - b * RCLike.re (LinearMap.trace 𝕜 E (U : E →L[𝕜] E).toLinearMap) := by
  let e := hU.isSymmetric.eigenvectorBasis rfl
  let mu := hU.isSymmetric.eigenvalues rfl
  have he (i : Fin (Module.finrank 𝕜 E)) :
      (U : E →L[𝕜] E) (e i) = (mu i : 𝕜) • e i :=
    hU.isSymmetric.apply_eigenvectorBasis rfl i
  have hnorm (i : Fin (Module.finrank 𝕜 E)) : |mu i| = 1 := by
    have h := ContinuousLinearMap.norm_map_of_mem_unitary U.property (e i)
    rw [he, norm_smul, e.norm_eq_one, mul_one] at h
    simpa only [RCLike.norm_ofReal] using h
  let lam (i : Fin (Module.finrank 𝕜 E)) : 𝕜 := (a : 𝕜) * (mu i : 𝕜) - (b : 𝕜)
  have hcost (i : Fin (Module.finrank 𝕜 E)) : ‖lam i‖ = a - b * mu i := by
    rcases (abs_eq zero_le_one).mp (hnorm i) with hi | hi
    · simp only [lam, hi, RCLike.ofReal_one, mul_one]
      rw [← RCLike.ofReal_sub, RCLike.norm_ofReal, abs_of_nonneg (sub_nonneg.mpr hab)]
    · have hlam : lam i = -((a + b : ℝ) : 𝕜) := by
        simp only [lam, hi, RCLike.ofReal_neg, RCLike.ofReal_one, mul_neg, mul_one,
          RCLike.ofReal_add]
        ring
      rw [hlam, norm_neg, RCLike.norm_ofReal,
        abs_of_nonneg (add_nonneg (hb.trans hab) hb), hi]
      ring
  have hAe (i : Fin (Module.finrank 𝕜 E)) :
      ((a : 𝕜) • (U : E →L[𝕜] E).toLinearMap -
        (b : 𝕜) • (LinearMap.id : E →ₗ[𝕜] E)) (e i) =
        lam i • e i := by
    change (a : 𝕜) • (U : E →L[𝕜] E) (e i) - (b : 𝕜) • e i = _
    rw [he, smul_smul, ← sub_smul]
  have htrace : RCLike.re (LinearMap.trace 𝕜 E (U : E →L[𝕜] E).toLinearMap) = ∑ i, mu i := by
    rw [LinearMap.trace_eq_sum_inner _ e, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    change RCLike.re ⟪e i, (U : E →L[𝕜] E) (e i)⟫_𝕜 = mu i
    rw [he, inner_smul_right, e.inner_eq_one, mul_one, RCLike.ofReal_re]
  rw [nuclear_eq_sum_norm_eigenvalues e _ lam hAe, htrace]
  simp_rw [hcost]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.mul_sum]
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end TauCeti

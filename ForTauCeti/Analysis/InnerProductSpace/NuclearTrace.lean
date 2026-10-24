/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.KyFan
public import Mathlib.Analysis.InnerProductSpace.Trace
public import ForTauCeti.Analysis.InnerProductSpace.SchattenSpectralCalculus

/-!
# Nuclear norm support by unitary trace pairings

The accepted Ky Fan maximum principle bounds the absolute trace by the
nuclear norm. Unitary invariance then gives a support inequality for every
unitary trace pairing. These are classical consequences of Ky Fan duality.
-/

public section

noncomputable section

namespace TauCeti

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- The absolute trace is bounded by the sum of singular values. -/
theorem norm_trace_le_nuclear (A : E →ₗ[𝕜] E) :
    ‖LinearMap.trace 𝕜 E A‖ ≤ UnitarilyInvariantSeminorm.nuclear 𝕜 E E A := by
  let b := stdOrthonormalBasis 𝕜 E
  rw [LinearMap.trace_eq_sum_inner _ b]
  calc
    _ ≤ A.kyFanSum (Module.finrank 𝕜 E) := by
      simpa using A.norm_sum_inner_le_kyFanSum b.orthonormal b.orthonormal
    _ = _ := A.kyFanSum_eq_nuclear (LinearMap.finrank_range_le A)

/-- Every isometric change of source coordinates defines a unitary trace
support functional for the nuclear norm. -/
theorem re_trace_isometry_comp_le_nuclear (U : E ≃ₗᵢ[𝕜] E) (A : E →ₗ[𝕜] E) :
    RCLike.re (LinearMap.trace 𝕜 E (U.toLinearMap ∘ₗ A)) ≤
      UnitarilyInvariantSeminorm.nuclear 𝕜 E E A := by
  calc
    _ ≤ ‖LinearMap.trace 𝕜 E (U.toLinearMap ∘ₗ A)‖ := RCLike.re_le_norm _
    _ ≤ UnitarilyInvariantSeminorm.nuclear 𝕜 E E (U.toLinearMap ∘ₗ A) :=
      norm_trace_le_nuclear _
    _ = _ := (UnitarilyInvariantSeminorm.nuclear 𝕜 E E).map_linearIsometryEquiv_comp U A

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
  classical
  constructor
  · intro heq
    let B := A.operatorAbs
    have hB : B.IsPositive := A.isPositive_operatorAbs
    let e := hB.isSymmetric.eigenvectorBasis rfl
    let mu := hB.isSymmetric.eigenvalues rfl
    have hmu (i : Fin (Module.finrank 𝕜 E)) : 0 ≤ mu i := hB.nonneg_eigenvalues rfl i
    have hBe (i : Fin (Module.finrank 𝕜 E)) : B (e i) = (mu i : 𝕜) • e i :=
      hB.isSymmetric.apply_eigenvectorBasis rfl i
    have hnorm (i : Fin (Module.finrank 𝕜 E)) : ‖A (e i)‖ = mu i := by
      rw [← A.norm_operatorAbs_apply, hBe, norm_smul, e.norm_eq_one,
        RCLike.norm_ofReal, abs_of_nonneg (hmu i), mul_one]
    have hsum : (∑ i, RCLike.re ⟪e i, A (e i)⟫_𝕜) = ∑ i, mu i := by
      have hnu := nuclear_eq_sum_norm_eigenvalues e B (fun i => (mu i : 𝕜)) hBe
      simp only [RCLike.norm_ofReal, abs_of_nonneg (hmu _)] at hnu
      rw [(UnitarilyInvariantSeminorm.nuclear 𝕜 E E).map_operatorAbs A] at hnu
      rw [LinearMap.trace_eq_sum_inner A e, map_sum] at heq
      exact heq.trans hnu
    have hle (i : Fin (Module.finrank 𝕜 E)) :
        RCLike.re ⟪e i, A (e i)⟫_𝕜 ≤ mu i := by
      calc
        _ ≤ ‖e i‖ * ‖A (e i)‖ := re_inner_le_norm _ _
        _ = _ := by rw [e.norm_eq_one, hnorm, one_mul]
    have hdiag (i : Fin (Module.finrank 𝕜 E)) :
        RCLike.re ⟪e i, A (e i)⟫_𝕜 = mu i :=
      (Finset.sum_eq_sum_iff_of_le (fun j _ => hle j)).mp hsum i (Finset.mem_univ i)
    have hAB : A = B := by
      apply e.toBasis.ext
      intro i
      change A (e i) = B (e i)
      rw [hBe]
      apply eq_of_norm_le_re_inner_eq_norm_sq (𝕜 := 𝕜)
      · rw [hnorm, norm_smul, RCLike.norm_ofReal, abs_of_nonneg (hmu i),
          e.norm_eq_one, mul_one]
      · rw [inner_smul_right, RCLike.mul_re, RCLike.ofReal_re, RCLike.ofReal_im,
          zero_mul, sub_zero, inner_re_symm, hdiag, norm_smul,
          RCLike.norm_ofReal, abs_of_nonneg (hmu i), e.norm_eq_one, mul_one]
        ring
    exact hAB ▸ hB
  · intro hA
    let e := hA.isSymmetric.eigenvectorBasis rfl
    let mu := hA.isSymmetric.eigenvalues rfl
    have hmu (i : Fin (Module.finrank 𝕜 E)) : 0 ≤ mu i := hA.nonneg_eigenvalues rfl i
    have he (i : Fin (Module.finrank 𝕜 E)) : A (e i) = (mu i : 𝕜) • e i :=
      hA.isSymmetric.apply_eigenvectorBasis rfl i
    rw [nuclear_eq_sum_norm_eigenvalues e A (fun i => (mu i : 𝕜)) he,
      LinearMap.trace_eq_sum_inner A e, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [he, inner_smul_right, e.inner_eq_one, mul_one, RCLike.ofReal_re,
      RCLike.norm_ofReal, abs_of_nonneg (hmu i)]

/-- Equality in a unitary nuclear support functional is positivity after
the corresponding change of target coordinates. -/
theorem re_trace_isometry_comp_eq_nuclear_iff_isPositive
    (U : E ≃ₗᵢ[𝕜] E) (A : E →ₗ[𝕜] E) :
    RCLike.re (LinearMap.trace 𝕜 E (U.toLinearMap ∘ₗ A)) =
      UnitarilyInvariantSeminorm.nuclear 𝕜 E E A ↔
        (U.toLinearMap ∘ₗ A).IsPositive := by
  rw [← (UnitarilyInvariantSeminorm.nuclear 𝕜 E E).map_linearIsometryEquiv_comp U A]
  exact re_trace_eq_nuclear_iff_isPositive _

end TauCeti

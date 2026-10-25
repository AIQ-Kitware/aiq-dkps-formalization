/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SchattenOptimizerAngles
public import DavisKahan.Geometry.Angle.CosineKernel

/-!
# Every Schatten optimizer on the actual right-angle defect

All positive-gradient paired means are strictly acute. Orthogonality of
sine eigenspaces therefore puts the entire right-angle space in the
actual gradient kernel. The unitary is a reflection there, so its action
is exactly one unitary identification of the two crossed defects, paired
with its inverse. The ambient pair and every competing unitary are
unrestricted; no prescribed defect coordinates are assumed.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open scoped ENNReal InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- The whole right-angle space lies in the actual gradient kernel of
every local minimizing complex transporter, including mixed-angle pairs. -/
theorem gradient_eq_zero_of_sinAngleOperator_eq_self_of_isLocalMinOn_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) (U : unitary (E →L[ℂ] E))
    (hmap : K.map (Unitary.linearIsometryEquiv U).toLinearMap = L)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = L.starProjection}
      (U : E →L[ℂ] E)) (x : E) (hx : K.sinAngleOperator L x = x) :
    schattenUnitaryGradient p.toReal (U : E →L[ℂ] E) x = 0 := by
  let G := schattenUnitaryGradient p.toReal (U : E →L[ℂ] E)
  let Z := G.toLinearMap.ker
  have ht := (map_eq_iff_conjugate_starProjection_complex K L U).mp hmap
  obtain ⟨n, e, alpha, beta, V, W, R, d, hV, hW, _, _, hd, _, hVe, hWe,
      hmean, _, _⟩ := schatten_transport_spectral_decomposition_of_isLocalMinOn_complex
        p hp hp1 hp2 K L.starProjection U ht hmin
  let bf := stdOrthonormalBasis ℂ Z
  let b := ((e.prod e).prod bf).map d
  have hb0 (i : Fin n) : b (.inl (.inl i)) = (e i : E) := by
    simp [b, OrthonormalBasis.prod_apply, hd]
  have hb1 (i : Fin n) : b (.inl (.inr i)) = K.reflection (e i) := by
    simp [b, OrthonormalBasis.prod_apply, hd]
  have hbf (j : Fin (Module.finrank ℂ Z)) : b (.inr j) = (bf j : E) := by
    simp [b, OrthonormalBasis.prod_apply, hd]
  have hu (i) : (U : E →L[ℂ] E) (e i : E) =
      Complex.exp ((alpha i : ℂ) * Complex.I) • (e i : E) := by
    rw [← hV, hVe]
    rfl
  have hw (i) : (U : E →L[ℂ] E) (K.reflection (e i)) =
      Complex.exp (((-beta i : ℝ) : ℂ) * Complex.I) • K.reflection (e i) := by
    rw [← hW, hWe, Submodule.coe_smul, map_smul]
  have hs (i) := Submodule.sinAngleOperator_apply_of_paired_phase_eigenvectors_complex
    K L (Unitary.linearIsometryEquiv U) hmap (e i) (alpha i) (beta i) (hu i) (hw i)
    ⟨(hmean i).1.le, (hmean i).2.le⟩
  have hsne (i) : Real.sin ((alpha i + beta i) / 2) ≠ 1 := by
    have hlt := Real.strictMonoOn_sin
      ⟨by linarith [(hmean i).1, Real.pi_pos], (hmean i).2.le⟩
      ⟨by linarith [Real.pi_pos], le_rfl⟩ (hmean i).2
    rw [Real.sin_pi_div_two] at hlt
    exact hlt.ne
  have hS := (K.isPositive_sinAngleOperator L).isSelfAdjoint.isSymmetric
  apply hS.apply_eq_zero_of_eigenvector_of_basis b 1 x
    (by simpa only [ContinuousLinearMap.coe_coe, RCLike.ofReal_one, one_smul] using hx)
  intro i
  rcases i with i | j
  · rcases i with i | i
    · right
      refine ⟨_, hsne i, ?_⟩
      rw [hb0]
      exact (hs i).1
    · right
      refine ⟨_, hsne i, ?_⟩
      rw [hb1]
      exact (hs i).2
  · left
    rw [hbf]
    exact (bf j).property

/-- Every local Schatten minimizer is self-adjoint on its entire actual
right-angle defect. Other angles, multiplicities and ambient eigenvalues
are unrestricted. -/
theorem selfAdjoint_on_right_defect_of_isLocalMinOn_transports_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) (U : unitary (E →L[ℂ] E))
    (hmap : K.map (Unitary.linearIsometryEquiv U).toLinearMap = L)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = L.starProjection}
      (U : E →L[ℂ] E)) (x : E) (hx : Proposition35.section3CosAngleOperator K L x = 0) :
    (U : E →L[ℂ] E) x = star (U : E →L[ℂ] E) x := by
  have hxS := (Proposition35.sinAngleOperator_apply_eq_self_iff_cosine_eq_zero K L x).mpr hx
  have hxG := gradient_eq_zero_of_sinAngleOperator_eq_self_of_isLocalMinOn_complex
    p hp hp1 hp2 K L U hmap hmin x hxS
  let Z := (schattenUnitaryGradient p.toReal (U : E →L[ℂ] E)).toLinearMap.ker
  obtain ⟨R, hR, hself, _, _⟩ := gradient_kernel_principalAngle_lower_bound p hp K L U hmap
  let z : Z := ⟨x, hxG⟩
  have hRR : R (R z) = z := by
    have h := congrArg (fun A : Z →L[ℂ] Z => A z)
      (Unitary.star_mul_self_of_mem (Unitary.linearIsometryEquiv.symm R).property)
    change star (R : Z →L[ℂ] Z) (R z) = z at h
    rwa [hself.star_eq] at h
  have hUU : (U : E →L[ℂ] E) ((U : E →L[ℂ] E) x) = x := by
    calc
      _ = (U : E →L[ℂ] E) (R z : E) := congrArg (U : E →L[ℂ] E) (hR z).symm
      _ = (R (R z) : E) := (hR (R z)).symm
      _ = x := congrArg (fun y : Z => (y : E)) hRR
  apply (Unitary.linearIsometryEquiv U).injective
  exact hUU.trans (congrArg (fun A : E →L[ℂ] E => A x)
    (Unitary.mul_star_self_of_mem U.property)).symm

/-- Every ambient local Schatten minimum determines exactly one unitary
identification of the crossed defects and acts by its inverse on the
other defect. The pair may also have arbitrary positive and zero angles. -/
theorem exists_unique_defect_equiv_of_isLocalMinOn_transports_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) (U : unitary (E →L[ℂ] E))
    (hmap : K.map (Unitary.linearIsometryEquiv U).toLinearMap = L)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = L.starProjection}
      (U : E →L[ℂ] E)) :
    ∃! D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L,
      (∀ x : halmosSourceDefect K L, (U : E →L[ℂ] E) x = (D x : E)) ∧
      (∀ y : halmosTargetDefect K L, (U : E →L[ℂ] E) y = (D.symm y : E)) := by
  apply Proposition35.exists_unique_defect_equiv_of_selfAdjoint_on_cosine_kernel
    K L (Unitary.linearIsometryEquiv U) hmap
  intro x hx
  rw [show (Unitary.linearIsometryEquiv U) x = (U : E →L[ℂ] E) x from rfl,
    Unitary.coe_linearIsometryEquiv_apply]
  exact selfAdjoint_on_right_defect_of_isLocalMinOn_transports_complex
    p hp hp1 hp2 K L U hmap hmin x hx

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SchattenEqualAnglePhases
public import ForTauCeti.Analysis.InnerProductSpace.FiniteUnitaryRestriction

/-!
# Compatibility of the intrinsic Schatten phase projection

On every interior angle space the relative phase commutes with canonical
rotation. It also commutes with source reflection by transport feasibility.
Consequently the unique supercritical projection commutes with both
restricted geometric operators. Other angles, including right angles,
remain unrestricted.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open Set
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- Every relative phase commutes with canonical rotation on every
interior angle space. No whole-space commutation on right-angle defects
or restriction on the canonical defect completion is asserted. -/
theorem relative_phase_commutes_canonical_on_angle_of_isLocalMinOn_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) (U : unitary (E →L[ℂ] E))
    (hmap : K.map (Unitary.linearIsometryEquiv U).toLinearMap = L)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = L.starProjection}
      (U : E →L[ℂ] E))
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (theta : ℝ) (hθ : theta ∈ Ioo 0 (Real.pi / 2))
    (x : E) (hx : K.sinAngleOperator L x = (Real.sin theta : ℂ) • x) :
    let R := nonacuteDirectRotation K L D
    let Z := star R * (U : E →L[ℂ] E)
    Z (R x) = R (Z x) := by
  classical
  let G := schattenUnitaryGradient p.toReal (U : E →L[ℂ] E)
  let N := G.toLinearMap.ker
  let R := nonacuteDirectRotation K L D
  let Z := star R * (U : E →L[ℂ] E)
  let A := Z * R - R * Z
  have hsinpos : 0 < Real.sin theta :=
    Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hsinlt : Real.sin theta < 1 := by
    have h := Real.strictMonoOn_sin
      ⟨by linarith [hθ.1, Real.pi_pos], hθ.2.le⟩
      ⟨by linarith [Real.pi_pos], le_rfl⟩ hθ.2
    simpa only [Real.sin_pi_div_two] using h
  have hxorth := mem_gradient_kernel_orthogonal_of_sin_eigenvector_of_isLocalMinOn_complex
    p hp hp1 K L U hmap hmin (Real.sin theta) hsinpos.ne' hsinlt.ne x hx
  obtain ⟨n, e, angle, eps, _, _, _, _, hR0, hR1, hZ0, hZ1, _, _⟩ :=
    positive_gradient_canonical_relative_phase_basis_of_isLocalMinOn_complex
      p hp hp1 hp2 K L U hmap hmin D
  change ∀ i, R (e i : E) = Complex.exp ((angle i : ℂ) * Complex.I) • (e i : E) at hR0
  change ∀ i, R (K.reflection (e i)) =
    Complex.exp (((-angle i : ℝ) : ℂ) * Complex.I) • K.reflection (e i) at hR1
  change ∀ i, Z (e i : E) =
    Complex.exp (((eps i * optimalPhase p.toReal (angle i) : ℝ) : ℂ) * Complex.I) • (e i : E)
    at hZ0
  change ∀ i, Z (K.reflection (e i)) =
    Complex.exp (((eps i * optimalPhase p.toReal (angle i) : ℝ) : ℂ) * Complex.I) •
      K.reflection (e i) at hZ1
  have ht := (map_eq_iff_conjugate_starProjection_complex K L U).mp hmap
  obtain ⟨_, _, _, _, _, _, _, d, _, _, _, _, hd, _, _, _, _, _, _⟩ :=
    schatten_transport_spectral_decomposition_of_isLocalMinOn_complex p hp hp1 hp2
      K L.starProjection U ht hmin
  let bf := stdOrthonormalBasis ℂ N
  let b := ((e.prod e).prod bf).map d
  have hb0 (i : Fin n) : b (.inl (.inl i)) = (e i : E) := by
    simp [b, OrthonormalBasis.prod_apply, hd]
  have hb1 (i : Fin n) : b (.inl (.inr i)) = K.reflection (e i) := by
    simp [b, OrthonormalBasis.prod_apply, hd]
  have hbf (j) : b (.inr j) = (bf j : E) := by
    simp [b, OrthonormalBasis.prod_apply, hd]
  have hAz (v : E) (a b : ℂ) (hR : R v = a • v) (hZ : Z v = b • v) : A v = 0 := by
    change Z (R v) - R (Z v) = 0
    simp only [hR, hZ, map_smul, smul_smul, mul_comm, sub_self]
  have hAx : A x = 0 := by
    rw [← b.sum_repr' x, map_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [map_smul]
    rcases i with i | j
    · rcases i with i | i
      · rw [hb0, hAz _ _ _ (hR0 i) (hZ0 i), smul_zero]
      · rw [hb1, hAz _ _ _ (hR1 i) (hZ1 i), smul_zero]
    · rw [hbf, (Submodule.mem_orthogonal N x).mp hxorth _ (bf j).property, zero_smul]
  exact sub_eq_zero.mp hAx

/-- The unique supercritical phase projection commutes with both actual
geometric restrictions: canonical rotation and source reflection. All
restrictions act by the original ambient operators, including when the
angle space is empty. -/
theorem relative_phase_unique_compatible_projection_on_angle_of_isLocalMinOn_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) (U : unitary (E →L[ℂ] E))
    (hmap : K.map (Unitary.linearIsometryEquiv U).toLinearMap = L)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = L.starProjection}
      (U : E →L[ℂ] E))
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (theta : ℝ) (hθ : theta ∈ Ioo 0 (Real.pi / 2)) (hcrit : criticalAngle p.toReal < theta) :
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation K L D, nonacuteDirectRotation_mem_unitary K L D⟩ :
        unitary (E →L[ℂ] E))
    let Z := Unitary.linearIsometryEquiv
      (star (Unitary.linearIsometryEquiv.symm R) * U)
    let N := Module.End.eigenspace (K.sinAngleOperator L).toLinearMap (Real.sin theta : ℂ)
    let delta := optimalPhase p.toReal theta
    ∃ V A J : N ≃ₗᵢ[ℂ] N,
      (∀ x : N, (V x : E) = Z x) ∧
      (∀ x : N, (A x : E) = R x) ∧
      (∀ x : N, (J x : E) = K.reflection x) ∧
      ∃! P : N →L[ℂ] N, IsStarProjection P ∧
        (V : N →L[ℂ] N) =
          ((Real.cos delta : ℂ) - (Real.sin delta : ℂ) * Complex.I) • 1 +
          (2 * (Real.sin delta : ℂ) * Complex.I) • P ∧
        Commute P (A : N →L[ℂ] N) ∧ Commute P (J : N →L[ℂ] N) := by
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L D, nonacuteDirectRotation_mem_unitary K L D⟩ :
      unitary (E →L[ℂ] E))
  let Z := Unitary.linearIsometryEquiv
    (star (Unitary.linearIsometryEquiv.symm R) * U)
  let N := Module.End.eigenspace (K.sinAngleOperator L).toLinearMap (Real.sin theta : ℂ)
  let delta := optimalPhase p.toReal theta
  have hRcomm := nonacuteDirectRotation_comm_sinAngleOperator K L D
  have hJcomm := K.commute_reflection_iff.mpr (K.commute_starProjection_sinAngleOperator L)
  have hinv (T : E ≃ₗᵢ[ℂ] E) (hc : Commute (T : E →L[ℂ] E) (K.sinAngleOperator L)) :
      ∀ x ∈ N, T x ∈ N := by
    intro x hx
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    change K.sinAngleOperator L x = (Real.sin theta : ℂ) • x at hx
    have h := congrArg (fun B : E →L[ℂ] E => B x) hc.eq
    change T (K.sinAngleOperator L x) = K.sinAngleOperator L (T x) at h
    rw [hx, map_smul] at h
    exact h.symm
  obtain ⟨A, hA, _, _⟩ := R.exists_restriction_of_finite_invariant N (hinv R hRcomm)
  obtain ⟨J, hJ, _, _⟩ := K.reflection.exists_restriction_of_finite_invariant N
    (hinv K.reflection hJcomm)
  obtain ⟨V, hV, P, hP, huni⟩ := relative_phase_unique_projection_on_angle_of_isLocalMinOn_complex
    p hp hp1 hp2 K L U hmap hmin D theta hθ hcrit
  have hVR : Commute (V : N →L[ℂ] N) (A : N →L[ℂ] N) := by
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    change (V (A x) : E) = (A (V x) : E)
    rw [hV, hA, hA, hV]
    exact relative_phase_commutes_canonical_on_angle_of_isLocalMinOn_complex
      p hp hp1 hp2 K L U hmap hmin D theta hθ x (Module.End.mem_eigenspace_iff.mp x.property)
  have hRmap : K.map R.toLinearMap = L := by
    apply (Submodule.map_eq_iff_intertwines_reflection K L R).mpr
    exact fun x => nonacuteDirectRotation_reflection_intertwines K L D x
  have hZJ := Submodule.relative_transport_commutes_reflection K L
    (Unitary.linearIsometryEquiv U) R hmap hRmap
  have hVJ : Commute (V : N →L[ℂ] N) (J : N →L[ℂ] N) := by
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    change (V (J x) : E) = (J (V x) : E)
    rw [hV, hJ, hJ, hV]
    exact hZJ x
  have hk : 2 * (Real.sin delta : ℂ) * Complex.I ≠ 0 := by
    have hstrict : p.toReal * Real.cos theta < 2 - p.toReal := by
      apply lt_of_not_ge
      intro h
      exact hcrit.not_ge ((critical_inequality_iff p.toReal theta hp1 hp2
        ⟨hθ.1.le, by linarith [hθ.2, Real.pi_pos]⟩).mp h)
    have hδ := optimalPhase_mem_Ioo_of_supercritical p.toReal theta hp1 hp2 hθ.1 hθ.2 hstrict
    exact mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr
        (Real.sin_pos_of_pos_of_lt_pi hδ.1 (by linarith [hδ.2, hθ.2, Real.pi_pos])).ne'))
      Complex.I_ne_zero
  have hPcomm (B : N →L[ℂ] N) (hc : Commute (V : N →L[ℂ] N) B) : Commute P B := by
    have hscalar : Commute B
        (((Real.cos delta : ℂ) - (Real.sin delta : ℂ) * Complex.I) • (1 : N →L[ℂ] N)) := by
      apply ContinuousLinearMap.ext
      intro x
      change B (((Real.cos delta : ℂ) - (Real.sin delta : ℂ) * Complex.I) • x) =
        ((Real.cos delta : ℂ) - (Real.sin delta : ℂ) * Complex.I) • B x
      exact map_smul B _ x
    have h := hc.symm.sub_right hscalar
    rw [hP.2, add_sub_cancel_left] at h
    apply ContinuousLinearMap.ext
    intro x
    change P (B x) = B (P x)
    have hx := congrArg (fun C : N →L[ℂ] N => C x) h.eq
    change B ((2 * (Real.sin delta : ℂ) * Complex.I) • P x) =
      (2 * (Real.sin delta : ℂ) * Complex.I) • P (B x) at hx
    rw [map_smul] at hx
    exact (smul_right_injective N hk hx).symm
  refine ⟨V, A, J, hV, hA, hJ, P, ⟨hP.1, hP.2, hPcomm _ hVR, hPcomm _ hVJ⟩, ?_⟩
  intro Q hQ
  exact huni Q ⟨hQ.1, hQ.2.1⟩

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

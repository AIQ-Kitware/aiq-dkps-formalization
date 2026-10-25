/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SchattenOptimizerPhases
public import DavisKahan.FiniteDimensional.DirectRotation.SchattenKernelAngles
public import ForTauCeti.Analysis.InnerProductSpace.UnitaryScalarRealPart

/-!
# Intrinsic two-phase parameters of every Schatten optimizer

On every positive acute geometric angle space, the relative unitary of
every ambient local minimum has the prescribed scalar real part. The
gradient-kernel sine operator is a projection, so its zero/right spectrum
cannot contribute to this interior angle space. No acuteness assumption
is imposed on other principal angles. Supercritical spaces therefore
carry a unique orthogonal two-phase projection, with arbitrary multiplicity.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open Set
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

omit [FiniteDimensional ℂ E] in
private theorem add_star_apply_of_phase_eigenvector
    (V : unitary (E →L[ℂ] E)) (t : ℝ) (x : E)
    (hx : (V : E →L[ℂ] E) x = Complex.exp ((t : ℂ) * Complex.I) • x) :
    (V : E →L[ℂ] E) x + star (V : E →L[ℂ] E) x = (2 * (Real.cos t : ℂ)) • x := by
  rw [hx, unitary_star_apply_of_apply_eq_smul V _ (Complex.norm_exp_ofReal_mul_I t) x hx,
    ← add_smul]
  congr 1
  have hs : star (Complex.exp ((t : ℂ) * Complex.I)) =
      Complex.exp (-(t : ℂ) * Complex.I) := by
    change (starRingEnd ℂ) (Complex.exp ((t : ℂ) * Complex.I)) = _
    rw [← Complex.exp_conj]
    congr 1
    simp
  rw [hs, ← Complex.two_cos, ← Complex.ofReal_cos]

/-- The relative unitary preserves every intrinsic sine-angle space,
including right and zero spaces, for every canonical defect completion. -/
theorem relative_phase_commute_sinAngleOperator_of_isLocalMinOn_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) (U : unitary (E →L[ℂ] E))
    (hmap : K.map (Unitary.linearIsometryEquiv U).toLinearMap = L)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = L.starProjection}
      (U : E →L[ℂ] E))
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L) :
    Commute (star (nonacuteDirectRotation K L D) * (U : E →L[ℂ] E))
      (K.sinAngleOperator L) := by
  have hR := nonacuteDirectRotation_comm_sinAngleOperator K L D
  have hstar : Commute (star (nonacuteDirectRotation K L D)) (K.sinAngleOperator L) := by
    have h := congrArg star hR.eq
    rw [commute_iff_eq]
    simpa only [star_mul, (K.isPositive_sinAngleOperator L).isSelfAdjoint.star_eq] using h.symm
  exact hstar.mul_left
    (commute_sinAngleOperator_of_isLocalMinOn_transports_complex p hp hp1 hp2 K L U hmap hmin)

set_option maxHeartbeats 800000 in
/-- On every positive acute geometric angle space, the actual relative
unitary has scalar real part `cos(optimalPhase(p,theta))`. Other angles
may be zero, critical or right, with arbitrary multiplicity. -/
theorem relative_phase_add_star_on_angle_of_isLocalMinOn_complex
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
    let Z := star (nonacuteDirectRotation K L D) * (U : E →L[ℂ] E)
    Z x + star Z x = (2 * (Real.cos (optimalPhase p.toReal theta) : ℂ)) • x := by
  classical
  let G := schattenUnitaryGradient p.toReal (U : E →L[ℂ] E)
  let H := Module.End.pointSpectralSubspace G.toLinearMap (Ioi 0)
  let N := G.toLinearMap.ker
  let K₀ := K.comap N.subtype
  let L₀ := L.comap N.subtype
  let S := K.sinAngleOperator L
  let S₀ := K₀.sinAngleOperator L₀
  let R : unitary (E →L[ℂ] E) :=
    ⟨nonacuteDirectRotation K L D, nonacuteDirectRotation_mem_unitary K L D⟩
  let Z := star R * U
  let A := (Z : E →L[ℂ] E) + star (Z : E →L[ℂ] E) -
    (2 * (Real.cos (optimalPhase p.toReal theta) : ℂ)) • 1
  have ht := (map_eq_iff_conjugate_starProjection_complex K L U).mp hmap
  obtain ⟨n, e, angle, eps, ha, heps, _, _, _, _, hZ0, hZ1, hs0, hs1⟩ :=
    positive_gradient_canonical_relative_phase_basis_of_isLocalMinOn_complex
      p hp hp1 hp2 K L U hmap hmin D
  change ∀ i, (Z : E →L[ℂ] E) (e i : E) =
    Complex.exp (((eps i * optimalPhase p.toReal (angle i) : ℝ) : ℂ) * Complex.I) • (e i : E)
    at hZ0
  change ∀ i, (Z : E →L[ℂ] E) (K.reflection (e i)) =
    Complex.exp (((eps i * optimalPhase p.toReal (angle i) : ℝ) : ℂ) * Complex.I) •
      K.reflection (e i) at hZ1
  obtain ⟨_, _, _, _, _, _, _, d, _, _, _, _, hd, _, _, _, _, _, _⟩ :=
    schatten_transport_spectral_decomposition_of_isLocalMinOn_complex p hp hp1 hp2
      K L.starProjection U ht hmin
  have hG : IsSelfAdjoint G := isSelfAdjoint_schattenUnitaryGradient _ _
  obtain ⟨hPK, hPL⟩ := gradient_square_reduces_projections_of_isLocalMinOn_transports
    p hp hp1 K L.starProjection U ht hmin
  have hK : ∀ z ∈ N, K.starProjection z ∈ N :=
    hG.isSymmetric.mapsTo_ker_of_commute_square
      (show Commute K.starProjection.toLinearMap (G.toLinearMap * G.toLinearMap) from
        congrArg ContinuousLinearMap.toLinearMap hPK.eq)
  have hL : ∀ z ∈ N, L.starProjection z ∈ N :=
    hG.isSymmetric.mapsTo_ker_of_commute_square
      (show Commute L.starProjection.toLinearMap (G.toLinearMap * G.toLinearMap) from
        congrArg ContinuousLinearMap.toLinearMap hPL.eq)
  have hS₀ := (K₀.isPositive_sinAngleOperator L₀).toLinearMap
  let bf := hS₀.isSymmetric.eigenvectorBasis rfl
  let nu := hS₀.isSymmetric.eigenvalues rfl
  have hbf (j) : S₀ (bf j) = (nu j : ℂ) • bf j :=
    hS₀.isSymmetric.apply_eigenvectorBasis rfl j
  have hproj := gradient_kernel_sinAngleOperator_isStarProjection_of_isLocalMinOn_complex
    p hp hp1 K L U hmap hmin
  have hbool (j) : nu j = 0 ∨ nu j = 1 := by
    have h := congrArg (fun B : N →L[ℂ] N => B (bf j)) hproj.isIdempotentElem.eq
    change S₀ (S₀ (bf j)) = S₀ (bf j) at h
    rw [hbf, map_smul, hbf, smul_smul] at h
    have hc := smul_left_injective ℂ (bf.toBasis.ne_zero j) h
    have hr : nu j * nu j = nu j := by exact_mod_cast hc
    have hz : nu j * (nu j - 1) = 0 := by nlinarith only [hr]
    exact (mul_eq_zero.mp hz).imp id sub_eq_zero.mp
  let b := ((e.prod e).prod bf).map d
  have hb0 (i : Fin n) : b (.inl (.inl i)) = (e i : E) := by
    simp [b, OrthonormalBasis.prod_apply, hd]
  have hb1 (i : Fin n) : b (.inl (.inr i)) = K.reflection (e i) := by
    simp [b, OrthonormalBasis.prod_apply, hd]
  have hbf' (j) : b (.inr j) = (bf j : E) := by
    simp [b, OrthonormalBasis.prod_apply, hd]
  have hsinpos : 0 < Real.sin theta :=
    Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hsinlt : Real.sin theta < 1 := by
    have h := Real.strictMonoOn_sin
      ⟨by linarith [hθ.1, Real.pi_pos], hθ.2.le⟩
      ⟨by linarith [Real.pi_pos], le_rfl⟩ hθ.2
    simpa only [Real.sin_pi_div_two] using h
  have hAz (i : Fin n) (v : E)
      (hv : (Z : E →L[ℂ] E) v =
        Complex.exp (((eps i * optimalPhase p.toReal (angle i) : ℝ) : ℂ) * Complex.I) • v)
      (heq : angle i = theta) : A v = 0 := by
    change (Z : E →L[ℂ] E) v + star (Z : E →L[ℂ] E) v -
      (2 * (Real.cos (optimalPhase p.toReal theta) : ℂ)) • v = 0
    rw [add_star_apply_of_phase_eigenvector Z _ v hv]
    have hc : Real.cos (eps i * optimalPhase p.toReal (angle i)) =
        Real.cos (optimalPhase p.toReal theta) := by
      rw [heq]
      rcases heps i with hi | hi <;> simp [hi]
    rw [hc, sub_self]
  have hne (i) (hi : angle i ≠ theta) : Real.sin (angle i) ≠ Real.sin theta := by
    exact fun heq => hi (Real.strictMonoOn_sin.injOn
      ⟨by linarith [(ha i).1, Real.pi_pos], (ha i).2.le⟩
      ⟨by linarith [hθ.1, Real.pi_pos], hθ.2.le⟩ heq)
  have hAx : A x = 0 := by
    have hS := (K.isPositive_sinAngleOperator L).isSelfAdjoint.isSymmetric
    apply hS.apply_eq_zero_of_eigenvector_of_basis b (Real.sin theta) x hx
    intro i
    rcases i with i | j
    · rcases i with i | i
      · rw [hb0]
        by_cases hi : angle i = theta
        · exact Or.inl (hAz i _ (hZ0 i) hi)
        · exact Or.inr ⟨_, hne i hi, hs0 i⟩
      · rw [hb1]
        by_cases hi : angle i = theta
        · exact Or.inl (hAz i _ (hZ1 i) hi)
        · exact Or.inr ⟨_, hne i hi, hs1 i⟩
    · right
      refine ⟨nu j, ?_, ?_⟩
      · rcases hbool j with hj | hj
        · rw [hj]
          exact hsinpos.ne
        · rw [hj]
          exact hsinlt.ne'
      · rw [hbf']
        exact Submodule.sinAngleOperator_apply_of_comap_eigenvector K L N hK hL
          (bf j) (nu j) (hS₀.nonneg_eigenvalues rfl j) (hbf j)
  exact sub_eq_zero.mp hAx

/-- Every actual supercritical acute angle space has a unique two-phase
orthogonal projection parameter. No angle elsewhere is excluded. -/
theorem relative_phase_unique_projection_on_angle_of_isLocalMinOn_complex
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
    let R : unitary (E →L[ℂ] E) :=
      ⟨nonacuteDirectRotation K L D, nonacuteDirectRotation_mem_unitary K L D⟩
    let Z := Unitary.linearIsometryEquiv (star R * U)
    let N := Module.End.eigenspace (K.sinAngleOperator L).toLinearMap (Real.sin theta : ℂ)
    let delta := optimalPhase p.toReal theta
    ∃ V : N ≃ₗᵢ[ℂ] N, (∀ x : N, (V x : E) = Z x) ∧
      ∃! P : N →L[ℂ] N, IsStarProjection P ∧
        (V : N →L[ℂ] N) =
          ((Real.cos delta : ℂ) - (Real.sin delta : ℂ) * Complex.I) • 1 +
          (2 * (Real.sin delta : ℂ) * Complex.I) • P := by
  let R : unitary (E →L[ℂ] E) :=
    ⟨nonacuteDirectRotation K L D, nonacuteDirectRotation_mem_unitary K L D⟩
  let Z := Unitary.linearIsometryEquiv (star R * U)
  let N := Module.End.eigenspace (K.sinAngleOperator L).toLinearMap (Real.sin theta : ℂ)
  let delta := optimalPhase p.toReal theta
  have hcomm := relative_phase_commute_sinAngleOperator_of_isLocalMinOn_complex
    p hp hp1 hp2 K L U hmap hmin D
  have hinv : ∀ x ∈ N, Z x ∈ N := by
    intro x hx
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    change K.sinAngleOperator L x = (Real.sin theta : ℂ) • x at hx
    have h := congrArg (fun A : E →L[ℂ] E => A x) hcomm.eq
    change (Z : E →L[ℂ] E) (K.sinAngleOperator L x) = K.sinAngleOperator L (Z x) at h
    rw [hx, map_smul] at h
    exact h.symm
  have hstrict : p.toReal * Real.cos theta < 2 - p.toReal := by
    apply lt_of_not_ge
    intro h
    exact hcrit.not_ge ((critical_inequality_iff p.toReal theta hp1 hp2
      ⟨hθ.1.le, by linarith [hθ.2, Real.pi_pos]⟩).mp h)
  have hδ := optimalPhase_mem_Ioo_of_supercritical p.toReal theta hp1 hp2 hθ.1 hθ.2 hstrict
  apply exists_restriction_unique_phase_projection_complex Z N hinv
    (Real.cos delta) (Real.sin delta)
    (by nlinarith [Real.sin_sq_add_cos_sq delta])
    (Real.sin_pos_of_pos_of_lt_pi hδ.1 (by linarith [hδ.2, hθ.2, Real.pi_pos])).ne'
  intro x
  exact relative_phase_add_star_on_angle_of_isLocalMinOn_complex
    p hp hp1 hp2 K L U hmap hmin D theta hθ x (Module.End.mem_eigenspace_iff.mp x.property)

/-- Every optimizer equals canonical rotation on each subcritical or
critical positive angle space, even when other angles are supercritical
or right. The entire ambient pair need not lie below the cutoff. -/
theorem apply_eq_canonical_on_angle_le_critical_of_isLocalMinOn_complex
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
    (hcrit : theta ≤ criticalAngle p.toReal)
    (x : E) (hx : K.sinAngleOperator L x = (Real.sin theta : ℂ) • x) :
    (U : E →L[ℂ] E) x = nonacuteDirectRotation K L D x := by
  let R : unitary (E →L[ℂ] E) :=
    ⟨nonacuteDirectRotation K L D, nonacuteDirectRotation_mem_unitary K L D⟩
  let Z := Unitary.linearIsometryEquiv (star R * U)
  let N := Module.End.eigenspace (K.sinAngleOperator L).toLinearMap (Real.sin theta : ℂ)
  have hzero := (optimalPhase_eq_zero_iff_le_criticalAngle p.toReal theta hp1 hp2
    hθ.1 hθ.2).mpr hcrit
  have hcomm := relative_phase_commute_sinAngleOperator_of_isLocalMinOn_complex
    p hp hp1 hp2 K L U hmap hmin D
  have hinv : ∀ y ∈ N, Z y ∈ N := by
    intro y hy
    rw [Module.End.mem_eigenspace_iff] at hy ⊢
    change K.sinAngleOperator L y = (Real.sin theta : ℂ) • y at hy
    have h := congrArg (fun A : E →L[ℂ] E => A y) hcomm.eq
    change (Z : E →L[ℂ] E) (K.sinAngleOperator L y) = K.sinAngleOperator L (Z y) at h
    rw [hy, map_smul] at h
    exact h.symm
  obtain ⟨V, hV, hreal⟩ := exists_restriction_add_star_eq_scalar_complex Z N hinv 1 (by
    intro y
    have h := relative_phase_add_star_on_angle_of_isLocalMinOn_complex
      p hp hp1 hp2 K L U hmap hmin D theta hθ y
      (Module.End.mem_eigenspace_iff.mp y.property)
    change (Z : E →L[ℂ] E) y + star (Z : E →L[ℂ] E) y = _
    rw [show (Z : E →L[ℂ] E) = star (nonacuteDirectRotation K L D) * (U : E →L[ℂ] E) by rfl]
    simpa only [hzero, Real.cos_zero, Complex.ofReal_one] using h)
  obtain ⟨P, _, heq⟩ := (unitary_add_star_eq_scalar_iff_projection_complex
    (Unitary.linearIsometryEquiv.symm V) 1 0 (by norm_num)).mp hreal
  have hVone : (V : N →L[ℂ] N) = 1 := by simpa using heq
  let x' : N := ⟨x, Module.End.mem_eigenspace_iff.mpr hx⟩
  have hZfix : Z x = x := by
    rw [← hV x']
    exact congrArg (fun y : N => (y : E)) (congrArg (fun A : N →L[ℂ] N => A x') hVone)
  change star (R : E →L[ℂ] E) ((U : E →L[ℂ] E) x) = x at hZfix
  have hcancel := congrArg (fun A : E →L[ℂ] E => A ((U : E →L[ℂ] E) x))
    (Unitary.mul_star_self_of_mem R.property)
  change (R : E →L[ℂ] E) (star (R : E →L[ℂ] E) ((U : E →L[ℂ] E) x)) =
    (U : E →L[ℂ] E) x at hcancel
  exact hcancel.symm.trans (congrArg (R : E →L[ℂ] E) hZfix)

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

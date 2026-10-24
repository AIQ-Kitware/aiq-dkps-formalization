/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.SchattenGradientNoMixing
import ForTauCeti.Analysis.InnerProductSpace.JointEigenbasis

/-!
# Exact scalar costs on paired Schatten-gradient levels

At a constrained local minimum, the two large-phase projections on a
positive submaximal gradient level have zero product. A joint orthonormal
eigenbasis therefore leaves only the phase pairs `(a,a)`, `(b,a)`, and
`(a,b)`. Each pair attains the scalar minimum at its mean angle.

The public theorem constructs the basis on the actual gradient eigenspace,
retains the action of the ambient transporter on both reflection-paired
vectors, and computes the literal Schatten cost of both unitary restrictions.
An empty gradient eigenspace gives an empty sum. The separate zero-gradient
reflection bound and assembly over all gradient levels are still needed for
the unrestricted principal-angle theorem.
-/

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open Set
open scoped ENNReal BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

private theorem orthogonal_two_phase_basis
    (a b : ℝ) (V W : E ≃ₗᵢ[ℂ] E) (A B : E →L[ℂ] E)
    (hA : IsStarProjection A) (hB : IsStarProjection B) (hAB : A * B = 0)
    (hV : (V : E →L[ℂ] E) = Complex.exp ((a : ℂ) * Complex.I) • 1 +
      (Complex.exp ((b : ℂ) * Complex.I) - Complex.exp ((a : ℂ) * Complex.I)) • A)
    (hW : (W : E →L[ℂ] E) = Complex.exp (((-a : ℝ) : ℂ) * Complex.I) • 1 +
      (Complex.exp (((-b : ℝ) : ℂ) * Complex.I) -
        Complex.exp (((-a : ℝ) : ℂ) * Complex.I)) • B) :
    ∃ (e : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E)
      (alpha beta : Fin (Module.finrank ℂ E) → ℝ),
      (∀ i, (alpha i = a ∧ beta i = a) ∨
        (alpha i = b ∧ beta i = a) ∨ (alpha i = a ∧ beta i = b)) ∧
      (∀ i, V (e i) = Complex.exp ((alpha i : ℂ) * Complex.I) • e i) ∧
      (∀ i, W (e i) = Complex.exp (((-beta i : ℝ) : ℂ) * Complex.I) • e i) := by
  classical
  have hBA : B * A = 0 := by
    have h := congrArg star hAB
    simpa only [star_mul, hA.isSelfAdjoint.star_eq, hB.isSelfAdjoint.star_eq, star_zero]
      using h
  have hcomm : Commute A.toLinearMap B.toLinearMap := by
    change (A * B).toLinearMap = (B * A).toLinearMap
    rw [hAB, hBA]
  obtain ⟨e, mu, nu, hmu, hnu⟩ :=
    hA.isSelfAdjoint.isSymmetric.exists_joint_orthonormalBasis
      hB.isSelfAdjoint.isSymmetric hcomm
  replace hmu : ∀ i, A (e i) = mu i • e i := fun i => hmu i
  replace hnu : ∀ i, B (e i) = nu i • e i := fun i => hnu i
  have hmu01 (i) : mu i = 0 ∨ mu i = 1 := by
    apply IsIdempotentElem.iff_eq_zero_or_one.mp
    apply smul_left_injective ℂ (e.orthonormal.ne_zero i)
    have h := congrArg (fun T : E →L[ℂ] E => T (e i)) hA.isIdempotentElem.eq
    change A (A (e i)) = A (e i) at h
    rwa [hmu, map_smul, hmu, smul_smul] at h
  have hnu01 (i) : nu i = 0 ∨ nu i = 1 := by
    apply IsIdempotentElem.iff_eq_zero_or_one.mp
    apply smul_left_injective ℂ (e.orthonormal.ne_zero i)
    have h := congrArg (fun T : E →L[ℂ] E => T (e i)) hB.isIdempotentElem.eq
    change B (B (e i)) = B (e i) at h
    rwa [hnu, map_smul, hnu, smul_smul] at h
  have hnoboth (i) : ¬ (mu i = 1 ∧ nu i = 1) := by
    rintro ⟨hm, hn⟩
    have h := congrArg (fun T : E →L[ℂ] E => T (e i)) hAB
    change A (B (e i)) = 0 at h
    rw [hnu, hn, one_smul, hmu, hm, one_smul] at h
    exact e.orthonormal.ne_zero i h
  let alpha (i) := if mu i = 0 then a else b
  let beta (i) := if nu i = 0 then a else b
  refine ⟨e, alpha, beta, ?_, ?_, ?_⟩
  · intro i
    rcases hmu01 i with hm | hm <;> rcases hnu01 i with hn | hn
    · exact Or.inl ⟨by simp [alpha, hm], by simp [beta, hn]⟩
    · exact Or.inr (Or.inr ⟨by simp [alpha, hm], by simp [beta, hn]⟩)
    · exact Or.inr (Or.inl ⟨by simp [alpha, hm], by simp [beta, hn]⟩)
    · exact (hnoboth i ⟨hm, hn⟩).elim
  · intro i
    change (V : E →L[ℂ] E) (e i) = _
    rw [hV]
    rcases hmu01 i with hm | hm
    · simp [alpha, hm, hmu]
    · simp [alpha, hm, hmu, sub_smul]
  · intro i
    change (W : E →L[ℂ] E) (e i) = _
    rw [hW]
    rcases hnu01 i with hn | hn
    · simp [beta, hn, hnu]
    · simp [beta, hn, hnu, sub_smul]

theorem norm_one_sub_exp_eq_phaseChord (t : ℝ) (ht : t ∈ Icc 0 Real.pi) :
    ‖1 - Complex.exp ((t : ℂ) * Complex.I)‖ = phaseChord t := by
  rw [norm_sub_rev, mul_comm (t : ℂ) Complex.I,
    Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs]
  exact abs_of_nonneg (mul_nonneg (by norm_num)
    (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [ht.1])
      (by linarith [ht.2, Real.pi_pos])))

theorem norm_one_sub_exp_neg_eq_phaseChord (t : ℝ) (ht : t ∈ Icc 0 Real.pi) :
    ‖1 - Complex.exp (((-t : ℝ) : ℂ) * Complex.I)‖ = phaseChord t := by
  have hc : 1 - Complex.exp (((-t : ℝ) : ℂ) * Complex.I) =
      star (1 - Complex.exp ((t : ℂ) * Complex.I)) := by
    rw [star_sub, star_one]
    congr 1
    change Complex.exp (((-t : ℝ) : ℂ) * Complex.I) =
      (starRingEnd ℂ) (Complex.exp ((t : ℂ) * Complex.I))
    rw [← Complex.exp_conj]
    congr 1
    simp
  rw [hc, norm_star]
  exact norm_one_sub_exp_eq_phaseChord t ht

private theorem scalar_cost_of_phase_pair
    (p a b alpha beta : ℝ) (hp1 : 1 < p) (hp2 : p < 2)
    (ha : a ∈ Ioo 0 (criticalAngle p)) (hb : b ∈ Ioo (criticalAngle p) Real.pi)
    (hbalance : phaseAmplitude p a = phaseAmplitude p b)
    (hpair : (alpha = a ∧ beta = a) ∨
      (alpha = b ∧ beta = a) ∨ (alpha = a ∧ beta = b)) :
    (alpha + beta) / 2 ∈ Ioo 0 (Real.pi / 2) ∧
      ‖1 - Complex.exp ((alpha : ℂ) * Complex.I)‖ ^ p +
        ‖1 - Complex.exp (((-beta : ℝ) : ℂ) * Complex.I)‖ ^ p =
          phaseMinimum p ((alpha + beta) / 2) := by
  have hc := criticalAngle_mem p hp1 hp2
  have haπ : a ∈ Icc 0 Real.pi := ⟨ha.1.le, by linarith [ha.2, hc.2, Real.pi_pos]⟩
  have hbπ : b ∈ Icc 0 Real.pi := ⟨by linarith [hb.1, hc.1], hb.2.le⟩
  have hcanon : phaseMinimum p a = 2 * phaseChord a ^ p :=
    phaseMinimum_eq_canonical_of_subcritical p a hp1 hp2 ha.1 (ha.2.trans hc.2)
      ((critical_inequality_iff p a hp1 hp2 haπ).2 ha.2.le)
  have hbalanced := balanced_roots_phase_minimum p a b hp1 hp2 ha hb hbalance
  rcases hpair with hpair | hpair | hpair
  · rw [hpair.1, hpair.2, show (a + a) / 2 = a by ring]
    exact ⟨⟨ha.1, ha.2.trans hc.2⟩, by
      rw [norm_one_sub_exp_eq_phaseChord a haπ, norm_one_sub_exp_neg_eq_phaseChord a haπ,
        hcanon, two_mul]⟩
  · rw [hpair.1, hpair.2, add_comm b a]
    exact ⟨⟨by linarith [ha.1, hb.1, hc.1], hbalanced.2.1⟩, by
      rw [norm_one_sub_exp_eq_phaseChord b hbπ, norm_one_sub_exp_neg_eq_phaseChord a haπ,
        hbalanced.2.2, add_comm]⟩
  · rw [hpair.1, hpair.2]
    exact ⟨⟨by linarith [ha.1, hb.1, hc.1], hbalanced.2.1⟩, by
      rw [norm_one_sub_exp_eq_phaseChord a haπ, norm_one_sub_exp_neg_eq_phaseChord b hbπ,
        hbalanced.2.2]⟩

private theorem norm_opposite_phase_sum (alpha beta : ℝ)
    (hmean : (alpha + beta) / 2 ∈ Icc 0 (Real.pi / 2)) :
    ‖Complex.exp ((alpha : ℂ) * Complex.I) +
      Complex.exp (((-beta : ℝ) : ℂ) * Complex.I)‖ =
        2 * Real.cos ((alpha + beta) / 2) := by
  let delta := (alpha - beta) / 2
  let z := Complex.exp (((-delta : ℝ) : ℂ) * Complex.I)
  have hz : ‖z‖ = 1 := Complex.norm_exp_ofReal_mul_I (-delta)
  have hphase (t : ℝ) : z * Complex.exp ((t : ℂ) * Complex.I) =
      Complex.exp (((t - delta : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    dsimp only [z, delta]
    ring
  have hrot : z * (Complex.exp ((alpha : ℂ) * Complex.I) +
      Complex.exp (((-beta : ℝ) : ℂ) * Complex.I)) =
        (2 * Real.cos ((alpha + beta) / 2) : ℝ) := by
    rw [mul_add, hphase, hphase,
      show alpha - delta = (alpha + beta) / 2 by dsimp [delta]; ring,
      show -beta - delta = -((alpha + beta) / 2) by dsimp [delta]; ring]
    rw [Complex.ofReal_neg, ← Complex.two_cos, ← Complex.ofReal_cos]
    push_cast
    rfl
  have hcos := Real.cos_nonneg_of_mem_Icc
    (show (alpha + beta) / 2 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) from
      ⟨by linarith [hmean.1, Real.pi_pos], hmean.2⟩)
  calc
    _ = ‖z * (Complex.exp ((alpha : ℂ) * Complex.I) +
        Complex.exp (((-beta : ℝ) : ℂ) * Complex.I))‖ := by rw [norm_mul, hz, one_mul]
    _ = _ := by rw [hrot, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
private theorem reflection_paired_phase_angle
    (K : Submodule ℂ E) [K.HasOrthogonalProjection]
    (U : E →L[ℂ] E) (v : E) (alpha beta : ℝ)
    (hv : ‖v‖ = 1) (horth : inner ℂ v (K.reflection v) = 0)
    (hUv : U v = Complex.exp ((alpha : ℂ) * Complex.I) • v)
    (hUJv : U (K.reflection v) =
      Complex.exp (((-beta : ℝ) : ℂ) * Complex.I) • K.reflection v)
    (hmean : (alpha + beta) / 2 ∈ Icc 0 (Real.pi / 2)) :
    ∃ x ∈ K, ‖x‖ = 1 ∧
      ‖inner ℂ x (U x)‖ = Real.cos ((alpha + beta) / 2) ∧
      x ∈ Submodule.span ℂ ({v, K.reflection v} : Set E) := by
  let r := (Real.sqrt 2)⁻¹
  let x := (r : ℂ) • (v + K.reflection v)
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hr : 0 < r := inv_pos.mpr hsqrt
  have hsqrt2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hJv : ‖K.reflection v‖ = 1 := (K.reflection.norm_map v).trans hv
  have hsum : ‖v + K.reflection v‖ = Real.sqrt 2 := by
    apply (sq_eq_sq₀ (norm_nonneg _) hsqrt.le).mp
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
    rw [hv, hJv] at h
    nlinarith
  have hvv : inner ℂ v v = 1 := by rw [inner_self_eq_norm_sq_to_K, hv]; norm_num
  have hJJ : inner ℂ (K.reflection v) (K.reflection v) = 1 := by
    rw [K.reflection.inner_map_map]
    exact hvv
  have hJorth : inner ℂ (K.reflection v) v = 0 := inner_eq_zero_symm.mpr horth
  have hinner : inner ℂ (v + K.reflection v) (U (v + K.reflection v)) =
      Complex.exp ((alpha : ℂ) * Complex.I) +
        Complex.exp (((-beta : ℝ) : ℂ) * Complex.I) := by
    rw [map_add, hUv, hUJv]
    simp only [inner_add_left, inner_add_right, inner_smul_right, hvv, hJJ,
      horth, hJorth, mul_one, add_zero, zero_add]
  refine ⟨x, ?_, ?_, ?_, ?_⟩
  · apply (K.reflection_eq_self_iff x).mp
    change K.reflection ((r : ℂ) • (v + K.reflection v)) = _
    rw [map_smul, map_add, K.reflection_reflection, add_comm]
  · change ‖(r : ℂ) • (v + K.reflection v)‖ = 1
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, hsum]
    exact inv_mul_cancel₀ hsqrt.ne'
  · change ‖inner ℂ ((r : ℂ) • (v + K.reflection v))
      (U ((r : ℂ) • (v + K.reflection v)))‖ = _
    rw [map_smul, inner_smul_left, inner_smul_right, hinner, norm_mul, norm_mul,
      Complex.conj_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      norm_opposite_phase_sum alpha beta hmean]
    dsimp only [r]
    field_simp
    rw [hsqrt2]
  · apply Submodule.smul_mem
    exact Submodule.add_mem _ (Submodule.subset_span (by simp))
      (Submodule.subset_span (by simp))

set_option maxHeartbeats 600000 in
/-- Each actual positive submaximal gradient level of a local transport
minimum admits a common eigenbasis of the two reflection-paired restrictions.
Every resulting pair attains the exact scalar cost at its mean angle, and
their sum is the literal Schatten displacement power of the paired block. -/
theorem gradient_block_scalar_minima_of_isLocalMinOn_transports
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K : Submodule ℂ E) [K.HasOrthogonalProjection]
    (Q : E →L[ℂ] E) (U : unitary (E →L[ℂ] E))
    (htrans : (U : E →L[ℂ] E) * K.starProjection * star (U : E →L[ℂ] E) = Q)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = Q}
      (U : E →L[ℂ] E))
    (g : ℝ) (hg0 : 0 < g)
    (hgm : g < p.toReal * phaseAmplitude p.toReal (criticalAngle p.toReal)) :
    let L := Module.End.eigenspace
      (schattenUnitaryGradient p.toReal (U : E →L[ℂ] E)).toLinearMap (g : ℂ)
    ∃ (V W : L ≃ₗᵢ[ℂ] L)
      (e : OrthonormalBasis (Fin (Module.finrank ℂ L)) ℂ L)
      (alpha beta : Fin (Module.finrank ℂ L) → ℝ),
      (∀ x : L, (V x : E) = (U : E →L[ℂ] E) x) ∧
      (∀ x : L, K.reflection (W x) = (U : E →L[ℂ] E) (K.reflection x)) ∧
      (∀ i, V (e i) = Complex.exp ((alpha i : ℂ) * Complex.I) • e i) ∧
      (∀ i, W (e i) = Complex.exp (((-beta i : ℝ) : ℂ) * Complex.I) • e i) ∧
      (∀ i, (alpha i + beta i) / 2 ∈ Ioo 0 (Real.pi / 2)) ∧
      (∀ i, ‖1 - Complex.exp ((alpha i : ℂ) * Complex.I)‖ ^ p.toReal +
        ‖1 - Complex.exp (((-beta i : ℝ) : ℂ) * Complex.I)‖ ^ p.toReal =
          phaseMinimum p.toReal ((alpha i + beta i) / 2)) ∧
      (∀ i, ∃ x ∈ K, ‖x‖ = 1 ∧
        ‖inner ℂ x ((U : E →L[ℂ] E) x)‖ = Real.cos ((alpha i + beta i) / 2) ∧
        x ∈ Submodule.span ℂ ({(e i : E), K.reflection (e i)} : Set E)) ∧
      UnitarilyInvariantSeminorm.schatten ℂ L L p (LinearMap.id - V.toLinearMap) ^ p.toReal +
        UnitarilyInvariantSeminorm.schatten ℂ L L p (LinearMap.id - W.toLinearMap) ^ p.toReal =
        ∑ i, phaseMinimum p.toReal ((alpha i + beta i) / 2) := by
  let L := Module.End.eigenspace
    (schattenUnitaryGradient p.toReal (U : E →L[ℂ] E)).toLinearMap (g : ℂ)
  obtain ⟨a, ha, b, hb, hbalance, V, W, A, B, hA, hB, hAB,
    hVact, hWact, hV, hW⟩ :=
    gradient_block_no_overlap_of_isLocalMinOn_transports p hp hp1 hp2 K Q U htrans hmin
      g hg0 hgm
  obtain ⟨e, alpha, beta, hpair, hVe, hWe⟩ :=
    orthogonal_two_phase_basis a b V W A B hA hB hAB hV hW
  have hscalar (i) := scalar_cost_of_phase_pair p.toReal a b (alpha i) (beta i)
    hp1 hp2 ha hb hbalance (hpair i)
  refine ⟨V, W, e, alpha, beta, hVact, hWact, hVe, hWe,
    fun i => (hscalar i).1, fun i => (hscalar i).2, ?_, ?_⟩
  · intro i
    obtain ⟨j, hj⟩ := gradient_eigenspace_pairing_of_isLocalMinOn_transports
      p hp hp1 K Q U htrans hmin (g : ℂ)
    have hne : (g : ℂ) ≠ -(g : ℂ) := by
      intro h
      have h' := congrArg Complex.re h
      simp only [Complex.ofReal_re, Complex.neg_re] at h'
      linarith
    have horth : inner ℂ (e i : E) (K.reflection (e i)) = 0 := by
      have h := (isSelfAdjoint_schattenUnitaryGradient p.toReal
        (U : E →L[ℂ] E)).isSymmetric.orthogonalFamily_eigenspaces hne (e i) (j (e i))
      change inner ℂ (e i : E) (j (e i) : E) = 0 at h
      rwa [hj] at h
    have hu : (U : E →L[ℂ] E) (e i : E) =
        Complex.exp ((alpha i : ℂ) * Complex.I) • (e i : E) :=
      (hVact (e i)).symm.trans (congrArg (fun x : L => (x : E)) (hVe i))
    have hw : (U : E →L[ℂ] E) (K.reflection (e i)) =
        Complex.exp (((-beta i : ℝ) : ℂ) * Complex.I) • K.reflection (e i) := by
      rw [← hWact, hWe]
      exact K.reflection.map_smul _ _
    exact reflection_paired_phase_angle K (U : E →L[ℂ] E) (e i) (alpha i) (beta i)
      (e.norm_eq_one i) horth hu hw ⟨(hscalar i).1.1.le, (hscalar i).1.2.le⟩
  ·
    have hVdisp (i : Fin (Module.finrank ℂ L)) :
      ((LinearMap.id : L →ₗ[ℂ] L) - V.toLinearMap) (e i) =
        (1 - Complex.exp ((alpha i : ℂ) * Complex.I)) • e i := by
      change e i - V (e i) = _
      rw [hVe, sub_smul, one_smul]
    have hWdisp (i : Fin (Module.finrank ℂ L)) :
      ((LinearMap.id : L →ₗ[ℂ] L) - W.toLinearMap) (e i) =
        (1 - Complex.exp (((-beta i : ℝ) : ℂ) * Complex.I)) • e i := by
      change e i - W (e i) = _
      rw [hWe, sub_smul, one_smul]
    rw [schatten_rpow_eq_sum_norm_eigenvalues e _ _ hVdisp p hp,
      schatten_rpow_eq_sum_norm_eigenvalues e _ _ hWdisp p hp, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => (hscalar i).2)

private def constantPhaseIsometry (t : ℝ) : E ≃ₗᵢ[ℂ] E :=
  (show E →ₗᵢ[ℂ] E from
    { toLinearMap := Complex.exp ((t : ℂ) * Complex.I) • LinearMap.id
      norm_map' := by
        intro x
        change ‖Complex.exp ((t : ℂ) * Complex.I) • x‖ = ‖x‖
        rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul] }).toLinearIsometryEquiv rfl

private theorem signed_critical_gradient_apply
    (p s : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (hs : s = 1 ∨ s = -1)
    (U : unitary (E →L[ℂ] E)) (x : E)
    (hx : schattenUnitaryGradient p (U : E →L[ℂ] E) x =
      ((s * (p * phaseAmplitude p (criticalAngle p)) : ℝ) : ℂ) • x) :
    (U : E →L[ℂ] E) x = Complex.exp (((s * criticalAngle p : ℝ) : ℂ) * Complex.I) • x := by
  let D := Module.End.eigenspace (schattenUnitaryGradient p (U : E →L[ℂ] E)).toLinearMap
    ((s * (p * phaseAmplitude p (criticalAngle p)) : ℝ) : ℂ)
  let x' : D := ⟨x, Module.End.mem_eigenspace_iff.mpr hx⟩
  obtain ⟨V, hVact, hV⟩ := signed_critical_gradient_eigenspace_representation p s hp1 hp2 hs U
  calc
    _ = (V x' : E) := (hVact x').symm
    _ = _ := congrArg (fun T : D →L[ℂ] D => (T x' : E)) hV

set_option maxHeartbeats 600000 in
/-- At the maximal gradient level, the paired restrictions are opposite
critical scalar phases. Their full Schatten cost is the critical scalar
minimum times the multiplicity, so the coalescing-root case has no cost gap. -/
theorem critical_gradient_block_scalar_minimum_of_isLocalMinOn_transports
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K : Submodule ℂ E) [K.HasOrthogonalProjection]
    (Q : E →L[ℂ] E) (U : unitary (E →L[ℂ] E))
    (htrans : (U : E →L[ℂ] E) * K.starProjection * star (U : E →L[ℂ] E) = Q)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = Q}
      (U : E →L[ℂ] E)) :
    let g := p.toReal * phaseAmplitude p.toReal (criticalAngle p.toReal)
    let L := Module.End.eigenspace
      (schattenUnitaryGradient p.toReal (U : E →L[ℂ] E)).toLinearMap (g : ℂ)
    ∃ V W : L ≃ₗᵢ[ℂ] L,
      (∀ x : L, (V x : E) = (U : E →L[ℂ] E) x) ∧
      (∀ x : L, K.reflection (W x) = (U : E →L[ℂ] E) (K.reflection x)) ∧
      (V : L →L[ℂ] L) = Complex.exp ((criticalAngle p.toReal : ℂ) * Complex.I) • 1 ∧
      (W : L →L[ℂ] L) =
        Complex.exp (((-criticalAngle p.toReal : ℝ) : ℂ) * Complex.I) • 1 ∧
      UnitarilyInvariantSeminorm.schatten ℂ L L p (LinearMap.id - V.toLinearMap) ^ p.toReal +
        UnitarilyInvariantSeminorm.schatten ℂ L L p (LinearMap.id - W.toLinearMap) ^ p.toReal =
          Module.finrank ℂ L * phaseMinimum p.toReal (criticalAngle p.toReal) := by
  let g := p.toReal * phaseAmplitude p.toReal (criticalAngle p.toReal)
  let G := schattenUnitaryGradient p.toReal (U : E →L[ℂ] E)
  let L := Module.End.eigenspace G.toLinearMap (g : ℂ)
  obtain ⟨j, hj⟩ := gradient_eigenspace_pairing_of_isLocalMinOn_transports
    p hp hp1 K Q U htrans hmin (g : ℂ)
  let V : L ≃ₗᵢ[ℂ] L := constantPhaseIsometry (criticalAngle p.toReal)
  let W : L ≃ₗᵢ[ℂ] L := constantPhaseIsometry (-criticalAngle p.toReal)
  have hV : (V : L →L[ℂ] L) =
      Complex.exp ((criticalAngle p.toReal : ℂ) * Complex.I) • 1 := by
    ext x
    rfl
  have hW : (W : L →L[ℂ] L) =
      Complex.exp (((-criticalAngle p.toReal : ℝ) : ℂ) * Complex.I) • 1 := by
    ext x
    rfl
  have hVact (x : L) : (V x : E) = (U : E →L[ℂ] E) x := by
    have hx : G x = (g : ℂ) • (x : E) := Module.End.mem_eigenspace_iff.mp x.property
    have h := signed_critical_gradient_apply p.toReal 1 hp1 hp2 (Or.inl rfl) U x
      (by simpa only [one_mul] using hx)
    change Complex.exp ((criticalAngle p.toReal : ℂ) * Complex.I) • (x : E) = _
    simpa only [one_mul] using h.symm
  have hWact (x : L) : K.reflection (W x) = (U : E →L[ℂ] E) (K.reflection x) := by
    have hx : G (K.reflection x) = -(g : ℂ) • K.reflection x := by
      rw [← hj x]
      exact Module.End.mem_eigenspace_iff.mp (j x).property
    have h := signed_critical_gradient_apply p.toReal (-1) hp1 hp2 (Or.inr rfl) U
      (K.reflection x) (by simpa only [neg_one_mul, Complex.ofReal_neg] using hx)
    change K.reflection (Complex.exp (((-criticalAngle p.toReal : ℝ) : ℂ) * Complex.I) •
      (x : E)) = _
    rw [map_smul]
    simpa only [neg_one_mul] using h.symm
  refine ⟨V, W, hVact, hWact, hV, hW, ?_⟩
  let e := stdOrthonormalBasis ℂ L
  have hVe (i : Fin (Module.finrank ℂ L)) : V (e i) =
      Complex.exp ((criticalAngle p.toReal : ℂ) * Complex.I) • e i := by
    change (V : L →L[ℂ] L) (e i) = _
    rw [hV]
    rfl
  have hWe (i : Fin (Module.finrank ℂ L)) : W (e i) =
      Complex.exp (((-criticalAngle p.toReal : ℝ) : ℂ) * Complex.I) • e i := by
    change (W : L →L[ℂ] L) (e i) = _
    rw [hW]
    rfl
  have hVdisp (i : Fin (Module.finrank ℂ L)) :
      ((LinearMap.id : L →ₗ[ℂ] L) - V.toLinearMap) (e i) =
        (1 - Complex.exp ((criticalAngle p.toReal : ℂ) * Complex.I)) • e i := by
    change e i - V (e i) = _
    rw [hVe, sub_smul, one_smul]
  have hWdisp (i : Fin (Module.finrank ℂ L)) :
      ((LinearMap.id : L →ₗ[ℂ] L) - W.toLinearMap) (e i) =
        (1 - Complex.exp (((-criticalAngle p.toReal : ℝ) : ℂ) * Complex.I)) • e i := by
    change e i - W (e i) = _
    rw [hWe, sub_smul, one_smul]
  have hc := criticalAngle_mem p.toReal hp1 hp2
  have hcπ : criticalAngle p.toReal ∈ Icc 0 Real.pi :=
    ⟨hc.1.le, by linarith [hc.2, Real.pi_pos]⟩
  have hcanon := phaseMinimum_eq_canonical_of_subcritical p.toReal (criticalAngle p.toReal)
    hp1 hp2 hc.1 hc.2 ((critical_inequality_iff p.toReal _ hp1 hp2 hcπ).2 le_rfl)
  rw [schatten_rpow_eq_sum_norm_eigenvalues e _ _ hVdisp p hp,
    schatten_rpow_eq_sum_norm_eigenvalues e _ _ hWdisp p hp, hcanon]
  simp only [norm_one_sub_exp_eq_phaseChord _ hcπ, norm_one_sub_exp_neg_eq_phaseChord _ hcπ,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

set_option maxHeartbeats 600000 in
/-- Every positive spectral level of an actual local transport minimum has
a complete phase eigenbasis paired by source reflection. This uniform form
includes the critical level and exposes ambient eigenvector equations for
assembling different levels into one orthogonal decomposition. -/
theorem gradient_eigenspace_phase_basis_of_isLocalMinOn_transports
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K : Submodule ℂ E) [K.HasOrthogonalProjection]
    (Q : E →L[ℂ] E) (U : unitary (E →L[ℂ] E))
    (htrans : (U : E →L[ℂ] E) * K.starProjection * star (U : E →L[ℂ] E) = Q)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = Q}
      (U : E →L[ℂ] E))
    (g : ℝ) (hg0 : 0 < g)
    (hg : (g : ℂ) ∈ spectrum ℂ (schattenUnitaryGradient p.toReal (U : E →L[ℂ] E))) :
    let L := Module.End.eigenspace
      (schattenUnitaryGradient p.toReal (U : E →L[ℂ] E)).toLinearMap (g : ℂ)
    ∃ (e : OrthonormalBasis (Fin (Module.finrank ℂ L)) ℂ L)
      (alpha beta : Fin (Module.finrank ℂ L) → ℝ),
      (∀ i, (U : E →L[ℂ] E) (e i : E) =
        Complex.exp ((alpha i : ℂ) * Complex.I) • (e i : E)) ∧
      (∀ i, (U : E →L[ℂ] E) (K.reflection (e i)) =
        Complex.exp (((-beta i : ℝ) : ℂ) * Complex.I) • K.reflection (e i)) ∧
      (∀ i, (alpha i + beta i) / 2 ∈ Ioo 0 (Real.pi / 2)) ∧
      (∀ i, ‖1 - Complex.exp ((alpha i : ℂ) * Complex.I)‖ ^ p.toReal +
        ‖1 - Complex.exp (((-beta i : ℝ) : ℂ) * Complex.I)‖ ^ p.toReal =
          phaseMinimum p.toReal ((alpha i + beta i) / 2)) := by
  let L := Module.End.eigenspace
    (schattenUnitaryGradient p.toReal (U : E →L[ℂ] E)).toLinearMap (g : ℂ)
  have hgm := positive_gradient_spectrum_le_max p.toReal g hp1 hp2 hg0 U hg
  rcases lt_or_eq_of_le hgm with hgm | hgm
  · obtain ⟨V, W, e, alpha, beta, hVact, hWact, hVe, hWe, hmean, hcost, _, _⟩ :=
      gradient_block_scalar_minima_of_isLocalMinOn_transports p hp hp1 hp2 K Q U htrans hmin
        g hg0 hgm
    refine ⟨e, alpha, beta, ?_, ?_, hmean, hcost⟩
    · intro i
      exact (hVact (e i)).symm.trans (congrArg (fun x : L => (x : E)) (hVe i))
    · intro i
      rw [← hWact, hWe]
      exact K.reflection.map_smul _ _
  · subst g
    obtain ⟨V, W, hVact, hWact, hV, hW, _⟩ :=
      critical_gradient_block_scalar_minimum_of_isLocalMinOn_transports
        p hp hp1 hp2 K Q U htrans hmin
    let e := stdOrthonormalBasis ℂ L
    let c := criticalAngle p.toReal
    have hc : c ∈ Ioo 0 (Real.pi / 2) := criticalAngle_mem p.toReal hp1 hp2
    have hcπ : c ∈ Icc 0 Real.pi := ⟨hc.1.le, by linarith [hc.2, Real.pi_pos]⟩
    have hcanon : phaseMinimum p.toReal c = 2 * phaseChord c ^ p.toReal :=
      phaseMinimum_eq_canonical_of_subcritical p.toReal c hp1 hp2 hc.1 hc.2
        ((critical_inequality_iff p.toReal c hp1 hp2 hcπ).2 le_rfl)
    refine ⟨e, fun _ => c, fun _ => c, ?_, ?_, ?_, ?_⟩
    · intro i
      have h := congrArg (fun T : L →L[ℂ] L => (T (e i) : E)) hV
      exact (hVact (e i)).symm.trans h
    · intro i
      have h := congrArg (fun T : L →L[ℂ] L => (T (e i) : E)) hW
      calc
        _ = K.reflection (W (e i)) := (hWact (e i)).symm
        _ = K.reflection (Complex.exp (((-c : ℝ) : ℂ) * Complex.I) • (e i : E)) :=
          congrArg K.reflection h
        _ = _ := K.reflection.map_smul _ _
    · intro i
      convert hc using 1; ring
    · intro i
      change ‖1 - Complex.exp ((c : ℂ) * Complex.I)‖ ^ p.toReal +
        ‖1 - Complex.exp (((-c : ℝ) : ℂ) * Complex.I)‖ ^ p.toReal =
          phaseMinimum p.toReal ((c + c) / 2)
      rw [show (c + c) / 2 = c by ring,
        norm_one_sub_exp_eq_phaseChord c hcπ, norm_one_sub_exp_neg_eq_phaseChord c hcπ,
        hcanon, two_mul]

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

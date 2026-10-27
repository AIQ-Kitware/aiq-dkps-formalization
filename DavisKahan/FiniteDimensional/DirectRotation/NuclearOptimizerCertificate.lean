/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedOptimizerCertificate
public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedSubspaceOptimization
public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedPrincipalAngles
public import DavisKahan.FiniteDimensional.DirectRotation.SchattenNuclearEndpoint
public import DavisKahan.Geometry.Polar.PairedPhase

/-!
# A nuclear equality certificate including every ambient competitor

At the nuclear endpoint the paired dual phases are i and -i on every
positive angle, and identity on fixed directions. Their exact trace
support has a nonnegative fixed-direction defect. Equality with the
sine minimum is therefore equivalent to fixation of those directions
and positivity of the dual displacement. The competitor may mix all
principal planes and need only contract the paired basis vectors.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open SmoothedPhaseTransition
open scoped InnerProductSpace

private theorem nuclear_cos_lt_one (theta : ℝ) (hθ : theta ∈ Set.Ioc 0 (Real.pi / 2)) :
    Real.cos theta < 1 := by
  simpa only [Real.cos_zero] using
    Real.cos_lt_cos_of_nonneg_of_le_pi_div_two (x := 0) le_rfl hθ.2 hθ.1

private theorem nuclear_dualReal_eq_zero (theta : ℝ)
    (hθ : theta ∈ Set.Ioc 0 (Real.pi / 2)) : dualReal 1 1 theta = 0 := by
  simp only [dualReal, one_mul, ite_eq_right (not_le.mpr (nuclear_cos_lt_one theta hθ))]

private theorem nuclear_dualPhase_eq_I (theta : ℝ)
    (hθ : theta ∈ Set.Ioc 0 (Real.pi / 2)) : dualPhase 1 1 theta = Complex.I := by
  simp [dualPhase, dualReal, dualImag, not_le.mpr (nuclear_cos_lt_one theta hθ)]

variable {E ι κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [Fintype ι] [Fintype κ]

omit [Fintype ι] [Fintype κ] in
/-- Every positive-angle nuclear dual phase has unit norm; zero angles
are represented among the fixed directions rather than divided by zero. -/
theorem norm_pairedDualPhase_nuclear_complex (theta : ι → ℝ)
    (hθ : ∀ i, theta i ∈ Set.Ioc 0 (Real.pi / 2)) (j : (Fin 2 × ι) ⊕ κ) :
    ‖pairedDualPhase 1 1 theta j‖ = 1 := by
  rcases j with ⟨r, i⟩ | j
  · simp only [pairedDualPhase, Sum.elim_inl, nuclear_dualPhase_eq_I _ (hθ i)]
    split_ifs <;> simp
  · simp [pairedDualPhase]

/-- **Exact nonsmooth nuclear equality certificate.** All contractions
satisfying the paired-diagonal constraint are covered, including arbitrary
mixing and right angles. Equality with the sine value is equivalent to
fixed common directions and a positive dual displacement. -/
theorem nuclear_eq_sine_sum_iff_certificate_complex
    (theta : ι → ℝ) (hθ : ∀ i, theta i ∈ Set.Ioc 0 (Real.pi / 2))
    (e : OrthonormalBasis ((Fin 2 × ι) ⊕ κ) ℂ E) (A Z : E →ₗ[ℂ] E)
    (hA0 : ∀ i, A (e (.inl (0, i))) =
      ((Real.cos (theta i) : ℂ) + Real.sin (theta i) * Complex.I) • e (.inl (0, i)))
    (hA1 : ∀ i, A (e (.inl (1, i))) =
      ((Real.cos (theta i) : ℂ) - Real.sin (theta i) * Complex.I) • e (.inl (1, i)))
    (hAf : ∀ j, A (e (.inr j)) = e (.inr j))
    (hZ : ∀ j, ‖Z (e j)‖ ≤ 1)
    (hdiag : ∀ i, (⟪e (.inl (0, i)), Z (e (.inl (0, i)))⟫_ℂ).im =
      (⟪e (.inl (1, i)), Z (e (.inl (1, i)))⟫_ℂ).im)
    (V : E ≃ₗᵢ[ℂ] E) (hV : ∀ j, V (e j) = pairedDualPhase 1 1 theta j • e j) :
    UnitarilyInvariantSeminorm.nuclear ℂ E E (A - Z) = (∑ i, 2 * Real.sin (theta i)) ↔
      (∀ j, Z (e (.inr j)) = e (.inr j)) ∧
        (V.symm.toLinearMap ∘ₗ (A - Z)).IsPositive := by
  have hid := weightedNuclear_support_eq_re_trace_complex 1 1 1 theta e A Z
    (by simpa only [Complex.ofReal_one, one_mul] using hA0) (by simpa only [Complex.ofReal_one, one_mul] using hA1)
    (by simpa only [Complex.ofReal_one, one_smul] using hAf) hdiag V hV
  have hsupport (i) : weightedSupportValue 1 1 1 (theta i) = 2 * Real.sin (theta i) := by
    simp [weightedSupportValue, dualReal, dualImag,
      not_le.mpr (nuclear_cos_lt_one _ (hθ i))]
  simp only [hsupport, sub_self, mul_zero, add_zero, one_mul, Complex.ofReal_one, one_smul] at hid
  have hnon := weightedDiagonalDefect_nonneg 1 1 theta e Z hZ
  have hbound := re_trace_isometry_comp_le_nuclear V.symm (A - Z)
  have heq := re_trace_isometry_comp_eq_nuclear_iff_isPositive V.symm (A - Z)
  change (LinearMap.trace ℂ E (V.symm.toLinearMap ∘ₗ (A - Z))).re ≤
    UnitarilyInvariantSeminorm.nuclear ℂ E E (A - Z) at hbound
  change (LinearMap.trace ℂ E (V.symm.toLinearMap ∘ₗ (A - Z))).re =
    UnitarilyInvariantSeminorm.nuclear ℂ E E (A - Z) ↔ _ at heq
  have hfixed : weightedDiagonalDefect 1 1 theta e Z = 0 ↔
      ∀ j, Z (e (.inr j)) = e (.inr j) := by
    rw [weightedDiagonalDefect_eq_zero_iff_fixed_complex 1 1 theta e Z hZ]
    simp only [nuclear_dualReal_eq_zero _ (hθ _), lt_self_iff_false, false_implies,
      implies_true, true_and]
  constructor
  · intro hatt
    have hzero : weightedDiagonalDefect 1 1 theta e Z = 0 := by linarith
    refine ⟨hfixed.mp hzero, heq.mp ?_⟩
    rw [← hid, hzero, add_zero, hatt]
  · rintro ⟨hfix, hpos⟩
    have hzero := hfixed.mpr hfix
    have htrace := heq.mpr hpos
    rw [← hid, hzero, add_zero] at htrace
    exact htrace.symm


section Subspace

variable [CompleteSpace E]

/-- **One exact certificate for every nuclear optimizer of a pair.**
The paired basis and unitary dual are constructed from the given
subspaces and work simultaneously for every ambient transporter.
Global minimality is equivalent to fixing the common directions and
positivity of the literal dual displacement. Zero, repeated and right
angles are included; no invariant-block hypothesis is imposed on T. -/
theorem exists_paired_nuclear_optimizer_certificate_complex
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L) :
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
        nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
          unitary (E →L[ℂ] E))
    ∃ n m : ℕ, ∃ (e : OrthonormalBasis ((Fin 2 × Fin n) ⊕ Fin m) ℂ E)
      (theta : Fin n → ℝ) (V : E ≃ₗᵢ[ℂ] E),
      (∀ i, theta i ∈ Set.Ioc 0 (Real.pi / 2)) ∧
      (∀ i, R (e (.inl (0, i))) =
        Complex.exp ((theta i : ℂ) * Complex.I) • e (.inl (0, i))) ∧
      (∀ i, R (e (.inl (1, i))) =
        Complex.exp ((-theta i : ℝ) * Complex.I) • e (.inl (1, i))) ∧
      (∀ j, R (e (.inr j)) = e (.inr j)) ∧
      (∀ i, K.reflection (e (.inl (0, i))) = e (.inl (1, i))) ∧
      (∀ j, V (e j) = pairedDualPhase 1 1 theta j • e j) ∧
      ∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
        ((∀ W : E ≃ₗᵢ[ℂ] E, K.map W.toLinearMap = L →
          UnitarilyInvariantSeminorm.nuclear ℂ E E (LinearMap.id - T.toLinearMap) ≤
            UnitarilyInvariantSeminorm.nuclear ℂ E E (LinearMap.id - W.toLinearMap)) ↔
          (∀ j, T (e (.inr j)) = e (.inr j)) ∧
            (V.symm.toLinearMap ∘ₗ
              (R.toLinearMap - (R.trans T.symm).toLinearMap)).IsPositive) := by
  classical
  let D := finiteCrossedDefectEquiv K L hKL
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L D, nonacuteDirectRotation_mem_unitary K L D⟩ : unitary (E →L[ℂ] E))
  obtain ⟨n, m, e, theta, hθ, hC0, hC1, hCf, hR0, hR1, hRf, hJ0⟩ :=
    exists_subspace_paired_rotation_basis K L hKL
  obtain ⟨V, hV⟩ := e.exists_linearIsometryEquiv_apply_eq_smul
    (pairedDualPhase 1 1 theta) (norm_pairedDualPhase_nuclear_complex theta hθ)
  have hA0 (i) : R.toLinearMap (e (.inl (0, i))) =
      ((Real.cos (theta i) : ℂ) + Real.sin (theta i) * Complex.I) • e (.inl (0, i)) := by
    change R (e (.inl (0, i))) = _
    rw [show R (e (.inl (0, i))) = _ from hR0 i, Complex.exp_ofReal_mul_I]
  have hA1 (i) : R.toLinearMap (e (.inl (1, i))) =
      ((Real.cos (theta i) : ℂ) - Real.sin (theta i) * Complex.I) • e (.inl (1, i)) := by
    change R (e (.inl (1, i))) = _
    rw [show R (e (.inl (1, i))) = _ from hR1 i, Complex.exp_ofReal_mul_I,
      Real.cos_neg, Real.sin_neg]
    congr 1
    push_cast
    ring
  have hsum := sum_principalAngles_eq_paired_sum K L e theta hθ hC0 hC1 hCf hJ0
    (fun t => 2 * Real.sin t) (by simp)
  obtain ⟨W, hWmap, hWcost, hWmin⟩ :=
    exists_unitary_minimizing_nuclear_transport_principalAngles_complex K L hKL
  simp only [UnitarilyInvariantSeminorm.schatten_one] at hWcost hWmin
  rw [hsum] at hWcost
  simp_rw [hsum] at hWmin
  refine ⟨n, m, e, theta, V, hθ, hR0, hR1, hRf, hJ0, hV, ?_⟩
  intro T hT
  let Z := R.trans T.symm
  have hRref (x : E) : R (K.reflection x) = L.reflection (R x) :=
    nonacuteDirectRotation_reflection_intertwines K L D x
  have hTref := (K.map_eq_iff_intertwines_reflection L T).mp hT
  have hcomm (x : E) : Z (K.reflection x) = K.reflection (Z x) := by
    apply T.injective
    change T (T.symm (R (K.reflection x))) = T (K.reflection (T.symm (R x)))
    rw [T.apply_symm_apply, hTref, T.apply_symm_apply, hRref]
  have hdiag (i) : (⟪e (.inl (0, i)), Z (e (.inl (0, i)))⟫_ℂ).im =
      (⟪e (.inl (1, i)), Z (e (.inl (1, i)))⟫_ℂ).im := by
    have h := inner_diagonal_eq_of_commute K.reflection Z.toLinearMap hcomm (e (.inl (0, i)))
    rw [hJ0] at h
    exact (congrArg Complex.im h).symm
  have hZ (j) : ‖Z.toLinearMap (e j)‖ ≤ 1 := by
    change ‖Z (e j)‖ ≤ 1
    rw [Z.norm_map, e.norm_eq_one]
  have hfactor : R.toLinearMap - Z.toLinearMap =
      (T.toLinearMap - LinearMap.id) ∘ₗ Z.toLinearMap := by
    ext x
    simp [Z]
  have hN : UnitarilyInvariantSeminorm.nuclear ℂ E E (R.toLinearMap - Z.toLinearMap) =
      UnitarilyInvariantSeminorm.nuclear ℂ E E (LinearMap.id - T.toLinearMap) := by
    rw [hfactor]
    calc
      _ = UnitarilyInvariantSeminorm.nuclear ℂ E E (T.toLinearMap - LinearMap.id) :=
        (UnitarilyInvariantSeminorm.nuclear ℂ E E).map_comp_linearIsometryEquiv Z _
      _ = _ := by rw [← neg_sub LinearMap.id T.toLinearMap, map_neg_eq_map]
  have hcert := nuclear_eq_sine_sum_iff_certificate_complex theta hθ e
    R.toLinearMap Z.toLinearMap hA0 hA1 hRf hZ hdiag V hV
  rw [hN] at hcert
  have hminiff : (∀ S : E ≃ₗᵢ[ℂ] E, K.map S.toLinearMap = L →
      UnitarilyInvariantSeminorm.nuclear ℂ E E (LinearMap.id - T.toLinearMap) ≤
        UnitarilyInvariantSeminorm.nuclear ℂ E E (LinearMap.id - S.toLinearMap)) ↔
      UnitarilyInvariantSeminorm.nuclear ℂ E E (LinearMap.id - T.toLinearMap) =
        ∑ i, 2 * Real.sin (theta i) := by
    constructor
    · intro hmin
      exact le_antisymm ((hmin W hWmap).trans_eq hWcost) (hWmin T hT)
    · intro hcost S hS
      rw [hcost]
      exact hWmin S hS
  have hfix (j) : Z.toLinearMap (e (.inr j)) = e (.inr j) ↔
      T (e (.inr j)) = e (.inr j) := by
    change T.symm (R (e (.inr j))) = e (.inr j) ↔ _
    rw [show R (e (.inr j)) = _ from hRf j]
    constructor
    · intro h
      have h' := congrArg T h
      rw [T.apply_symm_apply] at h'
      exact h'.symm
    · intro h
      apply T.injective
      rw [T.apply_symm_apply, h]
  rw [hminiff]
  simpa only [hfix] using hcert


/-- Every finite-dimensional global complex nuclear optimizer fixes
all vectors on which the source and target projections agree. The
competitor is unrestricted, and no differentiability or invariant-block
hypothesis is used. -/
theorem nuclear_minimizer_apply_eq_self_of_projections_eq_complex
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L)
    (T : E ≃ₗᵢ[ℂ] E) (hT : K.map T.toLinearMap = L)
    (hmin : ∀ W : E ≃ₗᵢ[ℂ] E, K.map W.toLinearMap = L →
      UnitarilyInvariantSeminorm.nuclear ℂ E E (LinearMap.id - T.toLinearMap) ≤
        UnitarilyInvariantSeminorm.nuclear ℂ E E (LinearMap.id - W.toLinearMap))
    (x : E) (hx : K.starProjection x = L.starProjection x) : T x = x := by
  classical
  let D := finiteCrossedDefectEquiv K L hKL
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L D, nonacuteDirectRotation_mem_unitary K L D⟩ : unitary (E →L[ℂ] E))
  obtain ⟨n, m, e, theta, V, hθ, hR0, hR1, _, _, _, hcert⟩ :=
    exists_paired_nuclear_optimizer_certificate_complex K L hKL
  have hfixed := ((hcert T hT).mp hmin).1
  have hRx : R x = x := nonacuteDirectRotation_apply_eq_self_of_projections_eq K L D x hx
  have hinner (r : Fin 2) (i : Fin n) : ⟪e (.inl (r, i)), x⟫_ℂ = 0 := by
    let mu := if r = 0 then Complex.exp ((theta i : ℂ) * Complex.I)
      else Complex.exp (((-theta i : ℝ) : ℂ) * Complex.I)
    have hRe : R (e (.inl (r, i))) = mu • e (.inl (r, i)) := by
      by_cases hr : r = 0
      · subst r
        exact hR0 i
      · have hr1 : r = 1 := by omega
        subst r
        exact hR1 i
    have hnorm : ‖mu‖ = 1 := by
      dsimp only [mu]
      split_ifs <;> exact Complex.norm_exp_ofReal_mul_I _
    have hne : mu ≠ 1 := by
      intro h
      have hre : mu.re = 1 := by rw [h]; rfl
      have hcos : mu.re = Real.cos (theta i) := by
        have hreal (t : ℝ) : (Complex.exp ((t : ℂ) * Complex.I)).re = Real.cos t :=
          Complex.exp_ofReal_mul_I_re t
        dsimp only [mu]
        split_ifs
        · exact hreal _
        · exact (hreal (-theta i)).trans (Real.cos_neg _)
      rw [hcos] at hre
      exact (nuclear_cos_lt_one _ (hθ i)).ne hre
    exact unitary_eigenvectors_inner_eq_zero_of_ne
      (⟨nonacuteDirectRotation K L D, nonacuteDirectRotation_mem_unitary K L D⟩ : unitary (E →L[ℂ] E))
      mu 1 hnorm hne _ x hRe (by rw [one_smul]; exact hRx)
  calc
    T x = T (∑ j, ⟪e j, x⟫_ℂ • e j) := congrArg T (e.sum_repr' x).symm
    _ = ∑ j, ⟪e j, x⟫_ℂ • T (e j) := by rw [map_sum]; simp only [map_smul]
    _ = ∑ j, ⟪e j, x⟫_ℂ • e j := by
      apply Finset.sum_congr rfl
      intro j _
      rcases j with ⟨r, i⟩ | j
      · rw [hinner, zero_smul, zero_smul]
      · rw [hfixed]
    _ = x := e.sum_repr' x

end Subspace

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

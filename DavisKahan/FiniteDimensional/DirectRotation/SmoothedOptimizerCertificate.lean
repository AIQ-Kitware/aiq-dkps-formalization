/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedCommutantOptimization

/-!
# Necessary and sufficient equality conditions for smoothed transport

The weighted nuclear certificate characterizes every attaining contraction:
its diagonal defect vanishes, and its displacement is positive after the
dual unitary change of coordinates. In particular every attaining contraction
fixes all strict subcritical directions and all fixed ambient directions.
No block invariance of the competitor is assumed.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

open scoped InnerProductSpace

variable {E ι κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [Fintype ι] [Fintype κ]

/-- Every contraction attaining the weighted nuclear lower bound is
characterized by a zero diagonal defect and a positive dual displacement.
The criterion also applies at the transition and at right angles. -/
theorem weightedNuclear_eq_minimum_iff_certificate
    (a b : ℝ) (hb : 0 < b) (hab : b < a) (theta : ι → ℝ)
    (e : OrthonormalBasis ((Fin 2 × ι) ⊕ κ) ℂ E) (A Z : E →ₗ[ℂ] E)
    (hA0 : ∀ i, A (e (.inl (0, i))) =
      (((a * Real.cos (theta i) : ℝ) : ℂ) + (a * Real.sin (theta i)) * Complex.I) •
        e (.inl (0, i)))
    (hA1 : ∀ i, A (e (.inl (1, i))) =
      (((a * Real.cos (theta i) : ℝ) : ℂ) - (a * Real.sin (theta i)) * Complex.I) •
        e (.inl (1, i)))
    (hAf : ∀ j, A (e (.inr j)) = (a : ℂ) • e (.inr j))
    (hZ : ∀ j, ‖Z (e j)‖ ≤ 1)
    (hdiag : ∀ i, (⟪e (.inl (0, i)), Z (e (.inl (0, i)))⟫_ℂ).im =
      (⟪e (.inl (1, i)), Z (e (.inl (1, i)))⟫_ℂ).im)
    (V : E ≃ₗᵢ[ℂ] E) (hV : ∀ j, V (e j) = pairedDualPhase a b theta j • e j) :
    UnitarilyInvariantSeminorm.nuclear ℂ E E (A - (b : ℂ) • Z) =
        (∑ i, weightedPhaseMinimum a b (theta i)) + Fintype.card κ * (a - b) ↔
      weightedDiagonalDefect a b theta e Z = 0 ∧
        (V.symm.toLinearMap ∘ₗ (A - (b : ℂ) • Z)).IsPositive := by
  have hid := weightedNuclear_support_eq_re_trace a b b theta e A Z hA0 hA1 hAf hdiag V hV
  simp only [weightedSupportValue_self a b _ hb.le hab] at hid
  have hnon := weightedDiagonalDefect_nonneg a b theta e Z hZ
  have hbound := weightedNuclear_lowerBound_with_diagonal_defect
    a b hb.le hab theta e A Z hA0 hA1 hAf hdiag
  have heq := re_trace_isometry_comp_eq_nuclear_iff_isPositive V.symm (A - (b : ℂ) • Z)
  change (LinearMap.trace ℂ E (V.symm.toLinearMap ∘ₗ (A - (b : ℂ) • Z))).re =
    UnitarilyInvariantSeminorm.nuclear ℂ E E (A - (b : ℂ) • Z) ↔ _ at heq
  constructor
  · intro hatt
    have hzero : weightedDiagonalDefect a b theta e Z = 0 := by nlinarith
    refine ⟨hzero, heq.mp ?_⟩
    rw [← hid, hzero, mul_zero, add_zero, hatt]
  · rintro ⟨hzero, hpos⟩
    have htrace := heq.mpr hpos
    rw [← hid, hzero, mul_zero, add_zero] at htrace
    exact htrace.symm

omit [FiniteDimensional ℂ E] in
/-- Vanishing diagonal defect is exactly pointwise fixation of all
positive-weight directions and all fixed directions. Even the competitor
need only contract the basis vectors. -/
theorem weightedDiagonalDefect_eq_zero_iff_fixed
    (a b : ℝ) (theta : ι → ℝ)
    (e : OrthonormalBasis ((Fin 2 × ι) ⊕ κ) ℂ E) (Z : E →ₗ[ℂ] E)
    (hZ : ∀ j, ‖Z (e j)‖ ≤ 1) :
    weightedDiagonalDefect a b theta e Z = 0 ↔
      (∀ i, 0 < dualReal a b (theta i) → ∀ r : Fin 2,
        Z (e (.inl (r, i))) = e (.inl (r, i))) ∧
      ∀ j, Z (e (.inr j)) = e (.inr j) := by
  classical
  let d (j : (Fin 2 × ι) ⊕ κ) := 1 - (⟪e j, Z (e j)⟫_ℂ).re
  have hd (j) : 0 ≤ d j := by
    apply sub_nonneg.mpr
    calc
      _ ≤ ‖⟪e j, Z (e j)⟫_ℂ‖ := Complex.re_le_norm _
      _ ≤ ‖e j‖ * ‖Z (e j)‖ := norm_inner_le_norm _ _
      _ ≤ 1 := by rw [e.norm_eq_one, one_mul]; exact hZ j
  have hfix (j) (hj : d j = 0) : Z (e j) = e j := by
    apply eq_of_norm_le_re_inner_eq_norm_sq (𝕜 := ℂ)
    · simpa only [e.norm_eq_one] using hZ j
    · rw [inner_re_symm, e.norm_eq_one]
      change (⟪e j, Z (e j)⟫_ℂ).re = (1 : ℝ) ^ 2
      dsimp only [d] at hj
      linarith
  have hdef : weightedDiagonalDefect a b theta e Z =
      (∑ i, dualReal a b (theta i) * (d (.inl (0, i)) + d (.inl (1, i)))) +
        ∑ j, d (.inr j) := by
    unfold weightedDiagonalDefect
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [d]
    ring
  have hpair (i) : 0 ≤ dualReal a b (theta i) *
      (d (.inl (0, i)) + d (.inl (1, i))) :=
    mul_nonneg (dualReal_nonneg _ _ _) (add_nonneg (hd _) (hd _))
  constructor
  · intro hzero
    have hs := hzero
    rw [hdef] at hs
    have hp : (∑ i, dualReal a b (theta i) *
        (d (.inl (0, i)) + d (.inl (1, i)))) = 0 :=
      (add_eq_zero_iff_of_nonneg (Finset.sum_nonneg (fun i _ => hpair i))
        (Finset.sum_nonneg (fun j _ => hd (.inr j)))).mp hs |>.1
    have hf : (∑ j, d (.inr j)) = 0 := by linarith
    refine ⟨?_, ?_⟩
    · intro i hi r
      have hi0 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hpair j)).mp hp i
        (Finset.mem_univ i)
      have hsum := (mul_eq_zero.mp hi0).resolve_left hi.ne'
      have hz := (add_eq_zero_iff_of_nonneg (hd _) (hd _)).mp hsum
      fin_cases r
      · exact hfix _ hz.1
      · exact hfix _ hz.2
    · intro j
      exact hfix _ ((Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hd (.inr k))).mp hf j
        (Finset.mem_univ j))
  · rintro ⟨hp, hf⟩
    rw [hdef]
    have hpair0 (i) : dualReal a b (theta i) *
        (d (.inl (0, i)) + d (.inl (1, i))) = 0 := by
      by_cases hi : 0 < dualReal a b (theta i)
      · simp only [d, hp i hi, e.inner_eq_one, Complex.one_re, sub_self, add_zero, mul_zero]
      · rw [le_antisymm (le_of_not_gt hi) (dualReal_nonneg _ _ _), zero_mul]
    have hfixed0 (j) : d (.inr j) = 0 := by
      simp only [d, hf, e.inner_eq_one, Complex.one_re, sub_self]
    simp only [hpair0, hfixed0, Finset.sum_const_zero, add_zero]

omit [FiniteDimensional ℂ E] in
private theorem eq_self_of_quarter_turn_certificate
    (b s t : ℝ) (hb : 0 < b) (ht : t ≠ 0)
    (A Z : E →ₗ[ℂ] E) (V : E ≃ₗᵢ[ℂ] E) (x : E)
    (hx : ‖x‖ = 1) (hZ : ‖Z x‖ ≤ 1)
    (hA : A x = ((b : ℂ) + (s : ℂ) * Complex.I) • x)
    (hV : V x = ((t : ℂ) * Complex.I) • x)
    (hpos : (V.symm.toLinearMap ∘ₗ (A - (b : ℂ) • Z)).IsPositive) : Z x = x := by
  have hinner := V.inner_map_map x (V.symm ((A - (b : ℂ) • Z) x))
  rw [V.apply_symm_apply, hV] at hinner
  have him := hpos.isSymmetric.im_inner_self_apply x
  change (⟪x, V.symm ((A - (b : ℂ) • Z) x)⟫_ℂ).im = 0 at him
  rw [← hinner, inner_smul_left, LinearMap.sub_apply, LinearMap.smul_apply,
    hA, inner_sub_right, inner_smul_right, inner_smul_right,
    inner_self_eq_norm_sq_to_K, hx] at him
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.mul_im,
    Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, Complex.neg_re, Complex.neg_im, mul_zero, zero_mul,
    add_zero, zero_add, sub_zero, mul_one] at him
  norm_num at him
  have hre : (⟪x, Z x⟫_ℂ).re = 1 := by
    have heq := him.resolve_left ht
    nlinarith
  apply eq_of_norm_le_re_inner_eq_norm_sq (𝕜 := ℂ)
  · simpa only [hx] using hZ
  · rw [inner_re_symm, hx]
    change (⟪x, Z x⟫_ℂ).re = (1 : ℝ) ^ 2
    simpa only [one_pow] using hre

omit [FiniteDimensional ℂ E] in
/-- The positive-displacement equality condition fixes critical directions
as well, even when other angles are supercritical and the competitor mixes
them. Diagonal defect alone would not detect these zero-weight directions. -/
theorem apply_eq_self_of_critical_certificate_complex
    (a b : ℝ) (hb : 0 < b) (hab : b < a) (theta : ι → ℝ)
    (hθ : ∀ i, theta i ∈ Set.Ioc 0 (Real.pi / 2))
    (e : OrthonormalBasis ((Fin 2 × ι) ⊕ κ) ℂ E) (A Z : E →ₗ[ℂ] E)
    (hA0 : ∀ i, A (e (.inl (0, i))) =
      (((a * Real.cos (theta i) : ℝ) : ℂ) + (a * Real.sin (theta i)) * Complex.I) •
        e (.inl (0, i)))
    (hA1 : ∀ i, A (e (.inl (1, i))) =
      (((a * Real.cos (theta i) : ℝ) : ℂ) - (a * Real.sin (theta i)) * Complex.I) •
        e (.inl (1, i)))
    (hZ : ∀ j, ‖Z (e j)‖ ≤ 1)
    (V : E ≃ₗᵢ[ℂ] E) (hV : ∀ j, V (e j) = pairedDualPhase a b theta j • e j)
    (hpos : (V.symm.toLinearMap ∘ₗ (A - (b : ℂ) • Z)).IsPositive)
    (i : ι) (hcritical : b = a * Real.cos (theta i)) (r : Fin 2) :
    Z (e (.inl (r, i))) = e (.inl (r, i)) := by
  have hphase := dualPhase_eq_I_of_supercritical a b (theta i) hb.le hab (hθ i) hcritical.ge
  fin_cases r
  · change Z (e (.inl (0, i))) = e (.inl (0, i))
    apply eq_self_of_quarter_turn_certificate b (a * Real.sin (theta i)) 1 hb one_ne_zero
      A Z V _ (e.norm_eq_one _) (hZ _) _ _ hpos
    · rw [hA0, ← hcritical, Complex.ofReal_mul]
    · simpa [pairedDualPhase, hphase] using hV (.inl (0, i))
  · change Z (e (.inl (1, i))) = e (.inl (1, i))
    apply eq_self_of_quarter_turn_certificate b (-(a * Real.sin (theta i))) (-1) hb
      (by norm_num) A Z V _ (e.norm_eq_one _) (hZ _) _ _ hpos
    · rw [hA1, ← hcritical, Complex.ofReal_neg, Complex.ofReal_mul, neg_mul]
      rfl
    · simpa [pairedDualPhase, hphase] using hV (.inl (1, i))

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

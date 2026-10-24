/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedPhaseMinimum
public import ForTauCeti.Analysis.InnerProductSpace.NuclearTrace

/-!
# An explicit nuclear trace certificate for smoothed transport

In an eigenbasis of a principal-plane rotation, the dual certificate is
diagonal with conjugate unit entries. Its trace pairing bounds all
competitors whose paired diagonal entries have equal imaginary parts.
Commutation with the source reflection implies that condition, even when
the competitor mixes different principal planes.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

open scoped ComplexConjugate InnerProductSpace

/-- The nonnegative real coordinate of the planar nuclear dual unitary. -/
def dualReal (a b theta : ℝ) : ℝ :=
  if b ≤ a * Real.cos theta then
    (a * Real.cos theta - b) /
      Real.sqrt ((a * Real.cos theta - b) ^ 2 + (a * Real.sin theta) ^ 2)
  else 0

/-- The imaginary coordinate of the planar nuclear dual unitary. -/
def dualImag (a b theta : ℝ) : ℝ :=
  if b ≤ a * Real.cos theta then
    (a * Real.sin theta) /
      Real.sqrt ((a * Real.cos theta - b) ^ 2 + (a * Real.sin theta) ^ 2)
  else 1

private theorem dual_denominator_pos (a b theta : ℝ) (hb : 0 ≤ b) (hab : b < a) :
    0 < Real.sqrt ((a * Real.cos theta - b) ^ 2 + (a * Real.sin theta) ^ 2) := by
  apply Real.sqrt_pos.mpr
  have hc : a * Real.cos theta ≤ a := mul_le_of_le_one_right (by linarith) (Real.cos_le_one _)
  have htrig := congrArg (fun t : ℝ => a ^ 2 * t) (Real.sin_sq_add_cos_sq theta)
  nlinarith [sq_pos_of_pos (sub_pos.mpr hab), mul_nonneg hb (sub_nonneg.mpr hc)]

theorem dualReal_nonneg (a b theta : ℝ) : 0 ≤ dualReal a b theta := by
  unfold dualReal
  split_ifs with hc
  · exact div_nonneg (sub_nonneg.mpr hc) (Real.sqrt_nonneg _)
  · exact le_rfl

/-- The two real dual coordinates form a unit vector. -/
theorem dualReal_sq_add_dualImag_sq (a b theta : ℝ) (hb : 0 ≤ b) (hab : b < a) :
    dualReal a b theta ^ 2 + dualImag a b theta ^ 2 = 1 := by
  have hd := dual_denominator_pos a b theta hb hab
  have hsq := Real.sq_sqrt (show
      0 ≤ (a * Real.cos theta - b) ^ 2 + (a * Real.sin theta) ^ 2 by positivity)
  unfold dualReal dualImag
  split_ifs
  · rw [div_pow, div_pow, ← add_div]
    exact (div_eq_one_iff_eq (pow_ne_zero _ hd.ne')).mpr hsq.symm
  · norm_num

/-- The real dual weight is bounded by one. -/
theorem dualReal_le_one (a b theta : ℝ) (hb : 0 ≤ b) (hab : b < a) :
    dualReal a b theta ≤ 1 := by
  have hs := dualReal_sq_add_dualImag_sq a b theta hb hab
  nlinarith [dualReal_nonneg a b theta, sq_nonneg (dualImag a b theta)]

/-- The dual weight is strictly positive below the angle transition. -/
theorem dualReal_pos_of_lt (a b theta : ℝ) (hb : 0 ≤ b) (hab : b < a)
    (hθ : b < a * Real.cos theta) : 0 < dualReal a b theta := by
  rw [dualReal, ite_eq_left hθ.le]
  exact div_pos (sub_pos.mpr hθ) (dual_denominator_pos a b theta hb hab)

/-- The real dual weight increases with the principal cosine throughout
the canonical regime. -/
theorem dualReal_mono_of_cos_le (a b theta phi : ℝ) (hb : 0 ≤ b) (hab : b < a)
    (hφ : b ≤ a * Real.cos phi) (hcos : Real.cos phi ≤ Real.cos theta) :
    dualReal a b phi ≤ dualReal a b theta := by
  have ha : 0 ≤ a := hb.trans hab.le
  have hnum : a * Real.cos phi - b ≤ a * Real.cos theta - b := by
    exact sub_le_sub_right (mul_le_mul_of_nonneg_left hcos ha) b
  have hθ : b ≤ a * Real.cos theta := by linarith
  have hdθ := dual_denominator_pos a b theta hb hab
  have hdφ := dual_denominator_pos a b phi hb hab
  have hden :
      Real.sqrt ((a * Real.cos theta - b) ^ 2 + (a * Real.sin theta) ^ 2) ≤
        Real.sqrt ((a * Real.cos phi - b) ^ 2 + (a * Real.sin phi) ^ 2) := by
    apply Real.sqrt_le_sqrt
    have ht := congrArg (fun t : ℝ => a ^ 2 * t) (Real.sin_sq_add_cos_sq theta)
    have hp := congrArg (fun t : ℝ => a ^ 2 * t) (Real.sin_sq_add_cos_sq phi)
    nlinarith [mul_nonneg (mul_nonneg ha hb) (sub_nonneg.mpr hcos)]
  rw [dualReal, dualReal, ite_eq_left hφ, ite_eq_left hθ]
  calc
    _ ≤ (a * Real.cos theta - b) /
        Real.sqrt ((a * Real.cos phi - b) ^ 2 + (a * Real.sin phi) ^ 2) :=
      div_le_div_of_nonneg_right hnum hdφ.le
    _ ≤ _ := div_le_div_of_nonneg_left (sub_nonneg.mpr hθ) hdθ hden

/-- The dual trace value is exactly the explicit scalar minimum. -/
theorem weightedPhaseMinimum_eq_dual (a b theta : ℝ) (hb : 0 ≤ b) (hab : b < a) :
    weightedPhaseMinimum a b theta =
      2 * (dualReal a b theta * (a * Real.cos theta - b) +
        dualImag a b theta * (a * Real.sin theta)) := by
  have hd := dual_denominator_pos a b theta hb hab
  have hsq := Real.sq_sqrt (show
      0 ≤ (a * Real.cos theta - b) ^ 2 + (a * Real.sin theta) ^ 2 by positivity)
  have hrad : a ^ 2 + b ^ 2 - 2 * a * b * Real.cos theta =
      (a * Real.cos theta - b) ^ 2 + (a * Real.sin theta) ^ 2 := by
    have htrig := congrArg (fun t : ℝ => a ^ 2 * t) (Real.sin_sq_add_cos_sq theta)
    nlinarith
  unfold weightedPhaseMinimum dualReal dualImag
  split_ifs
  · rw [hrad]
    have hv :
        (a * Real.cos theta - b) /
            Real.sqrt ((a * Real.cos theta - b) ^ 2 + (a * Real.sin theta) ^ 2) *
              (a * Real.cos theta - b) +
          (a * Real.sin theta) /
            Real.sqrt ((a * Real.cos theta - b) ^ 2 + (a * Real.sin theta) ^ 2) *
              (a * Real.sin theta) =
          Real.sqrt ((a * Real.cos theta - b) ^ 2 + (a * Real.sin theta) ^ 2) := by
      calc
        _ = ((a * Real.cos theta - b) ^ 2 + (a * Real.sin theta) ^ 2) /
            Real.sqrt ((a * Real.cos theta - b) ^ 2 + (a * Real.sin theta) ^ 2) := by ring
        _ = _ := (div_eq_iff hd.ne').mpr (by simpa only [pow_two] using hsq.symm)
    rw [hv]
  · ring

private theorem paired_scalar_support_eq (h k u v b : ℝ)
    (z w : ℂ) (hzw : z.im = w.im) :
    2 * (h * (u - b) + k * v) + b * h * (2 - z.re - w.re) =
      (conj ((h : ℂ) + k * Complex.I) * ((u : ℂ) + v * Complex.I - b * z)).re +
      (conj ((h : ℂ) - k * Complex.I) * ((u : ℂ) - v * Complex.I - b * w)).re := by
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, mul_one, zero_add, add_zero, sub_zero, zero_sub]
  rw [hzw]
  ring

/-- The positive-eigenphase entry of the diagonal nuclear dual unitary. -/
@[expose]
def dualPhase (a b theta : ℝ) : ℂ :=
  (dualReal a b theta : ℂ) + dualImag a b theta * Complex.I

theorem norm_dualPhase (a b theta : ℝ) (hb : 0 ≤ b) (hab : b < a) :
    ‖dualPhase a b theta‖ = 1 := by
  have hsq := dualReal_sq_add_dualImag_sq a b theta hb hab
  rw [← sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1), Complex.sq_norm]
  simpa [dualPhase, Complex.normSq_apply, pow_two] using hsq

private theorem conj_dualPhase (a b theta : ℝ) :
    conj (dualPhase a b theta) =
      (dualReal a b theta : ℂ) - dualImag a b theta * Complex.I := by
  apply Complex.ext <;> simp [dualPhase]

variable {E ι κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [Fintype ι] [Fintype κ]

/-- The weighted diagonal departure from the identity seen by the nuclear
dual certificate. It is nonnegative for contractions, and controls squared
distance on the unitary group. -/
@[expose]
def weightedDiagonalDefect (a b : ℝ) (theta : ι → ℝ)
    (e : OrthonormalBasis ((Fin 2 × ι) ⊕ κ) ℂ E) (Z : E →ₗ[ℂ] E) : ℝ :=
  (∑ i, dualReal a b (theta i) *
    (2 - (⟪e (.inl (0, i)), Z (e (.inl (0, i)))⟫_ℂ).re -
      (⟪e (.inl (1, i)), Z (e (.inl (1, i)))⟫_ℂ).re)) +
    ∑ j, (1 - (⟪e (.inr j), Z (e (.inr j))⟫_ℂ).re)

/-- The nuclear certificate retains an exact diagonal defect term, even
without a contraction assumption on the competitor. Arbitrary mixing of
principal planes is permitted. -/
theorem weightedNuclear_lowerBound_with_diagonal_defect
    (a b : ℝ) (hb : 0 ≤ b) (hab : b < a) (theta : ι → ℝ)
    (e : OrthonormalBasis ((Fin 2 × ι) ⊕ κ) ℂ E) (A Z : E →ₗ[ℂ] E)
    (hA0 : ∀ i, A (e (.inl (0, i))) =
      (((a * Real.cos (theta i) : ℝ) : ℂ) + (a * Real.sin (theta i)) * Complex.I) •
        e (.inl (0, i)))
    (hA1 : ∀ i, A (e (.inl (1, i))) =
      (((a * Real.cos (theta i) : ℝ) : ℂ) - (a * Real.sin (theta i)) * Complex.I) •
        e (.inl (1, i)))
    (hAf : ∀ j, A (e (.inr j)) = (a : ℂ) • e (.inr j))
    (hdiag : ∀ i, (⟪e (.inl (0, i)), Z (e (.inl (0, i)))⟫_ℂ).im =
      (⟪e (.inl (1, i)), Z (e (.inl (1, i)))⟫_ℂ).im) :
    (∑ i, weightedPhaseMinimum a b (theta i)) + Fintype.card κ * (a - b) +
      b * weightedDiagonalDefect a b theta e Z ≤
      UnitarilyInvariantSeminorm.nuclear ℂ E E (A - (b : ℂ) • Z) := by
  classical
  let t : ((Fin 2 × ι) ⊕ κ) → ℂ := Sum.elim
    (fun j => if j.1 = 0 then dualPhase a b (theta j.2) else conj (dualPhase a b (theta j.2)))
    (fun _ => 1)
  have ht (j) : ‖t j‖ = 1 := by
    rcases j with ⟨r, i⟩ | j
    · dsimp only [t, Sum.elim_inl]
      split_ifs <;> simpa only [Complex.norm_conj] using norm_dualPhase a b (theta i) hb hab
    · simp [t]
  let u (j) := t j • e j
  have hu : Orthonormal ℂ u := by
    rw [orthonormal_iff_ite]
    intro j k
    dsimp only [u]
    rw [inner_smul_left, inner_smul_right, (orthonormal_iff_ite.mp e.orthonormal) j k]
    by_cases hjk : j = k
    · subst k
      rw [ite_eq_left rfl, mul_one, RCLike.conj_mul, ht j]
      norm_num
    · rw [ite_eq_right hjk, mul_zero, mul_zero]
  let D := A - (b : ℂ) • Z
  let z (j) : ℂ := ⟪e j, Z (e j)⟫_ℂ
  have hentry (j) (lam : ℂ) (hAj : A (e j) = lam • e j) :
      ⟪u j, D (e j)⟫_ℂ = conj (t j) * (lam - b * z j) := by
    dsimp only [u, D, z]
    rw [LinearMap.sub_apply, LinearMap.smul_apply, hAj, inner_smul_left,
      inner_sub_right, inner_smul_right, inner_smul_right, e.inner_eq_one, mul_one]
  have hpair (i : ι) : weightedPhaseMinimum a b (theta i) +
      b * dualReal a b (theta i) * (2 - (z (.inl (0, i))).re - (z (.inl (1, i))).re) =
      (⟪u (.inl (0, i)), D (e (.inl (0, i)))⟫_ℂ).re +
      (⟪u (.inl (1, i)), D (e (.inl (1, i)))⟫_ℂ).re := by
    rw [weightedPhaseMinimum_eq_dual a b (theta i) hb hab]
    have h := paired_scalar_support_eq (dualReal a b (theta i)) (dualImag a b (theta i))
      (a * Real.cos (theta i)) (a * Real.sin (theta i)) b
      (z (.inl (0, i))) (z (.inl (1, i))) (hdiag i)
    rw [hentry _ _ (hA0 i), hentry _ _ (hA1 i)]
    have ht0 : t (.inl (0, i)) = dualPhase a b (theta i) := by simp [t]
    have ht1 : t (.inl (1, i)) = conj (dualPhase a b (theta i)) := by simp [t]
    rw [ht0, ht1, conj_dualPhase]
    have hconj := conj_dualPhase a b (theta i)
    change conj ((dualReal a b (theta i) : ℂ) + dualImag a b (theta i) * Complex.I) = _ at hconj
    rw [hconj] at h
    simpa only [dualPhase, Complex.ofReal_mul] using h
  have hfixed (j : κ) : a - b + b * (1 - (z (.inr j)).re) =
      (⟪u (.inr j), D (e (.inr j))⟫_ℂ).re := by
    simp only [u, t, Sum.elim_inr, one_smul, D, LinearMap.sub_apply,
      LinearMap.smul_apply, hAf, inner_sub_right, inner_smul_right,
      e.inner_eq_one, mul_one, Complex.sub_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero]
    change a - b + b * (1 - (z (.inr j)).re) = a - b * (z (.inr j)).re
    ring
  calc
    _ = (∑ i, (weightedPhaseMinimum a b (theta i) +
        b * dualReal a b (theta i) *
          (2 - (z (.inl (0, i))).re - (z (.inl (1, i))).re))) +
        ∑ j : κ, (a - b + b * (1 - (z (.inr j)).re)) := by
      simp only [weightedDiagonalDefect, z, Finset.sum_add_distrib, mul_add, Finset.mul_sum,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc]
      ring
    _ = (∑ i, ((⟪u (.inl (0, i)), D (e (.inl (0, i)))⟫_ℂ).re +
        (⟪u (.inl (1, i)), D (e (.inl (1, i)))⟫_ℂ).re)) +
        ∑ j : κ, (⟪u (.inr j), D (e (.inr j))⟫_ℂ).re := by
      simp only [hpair, hfixed]
    _ = ∑ j, (⟪u j, D (e j)⟫_ℂ).re := by
      rw [Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_two, ← Finset.sum_add_distrib]
    _ ≤ _ := re_sum_inner_le_nuclear e D u hu

omit [FiniteDimensional ℂ E] in
/-- The diagonal defect is nonnegative for every competitor that contracts
the given basis vectors. -/
theorem weightedDiagonalDefect_nonneg
    (a b : ℝ) (theta : ι → ℝ)
    (e : OrthonormalBasis ((Fin 2 × ι) ⊕ κ) ℂ E) (Z : E →ₗ[ℂ] E)
    (hZ : ∀ j, ‖Z (e j)‖ ≤ 1) : 0 ≤ weightedDiagonalDefect a b theta e Z := by
  have hz (j) : (⟪e j, Z (e j)⟫_ℂ).re ≤ 1 := by
    calc
      _ ≤ ‖⟪e j, Z (e j)⟫_ℂ‖ := Complex.re_le_norm _
      _ ≤ ‖e j‖ * ‖Z (e j)‖ := norm_inner_le_norm _ _
      _ = ‖Z (e j)‖ := by rw [e.norm_eq_one, one_mul]
      _ ≤ 1 := hZ j
  unfold weightedDiagonalDefect
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (dualReal_nonneg _ _ _)
      (by linarith [hz (.inl (0, i)), hz (.inl (1, i))])
  · exact Finset.sum_nonneg (fun j _ => sub_nonneg.mpr (hz (.inr j)))

/-- A global weighted nuclear lower bound allowing arbitrary mixing between
principal planes and fixed directions. Only the imaginary parts of paired
diagonal entries must agree; an operator-norm contraction commuting with
the swapping source reflection satisfies these hypotheses. -/
theorem weightedNuclear_lowerBound_of_paired_diagonals
    (a b : ℝ) (hb : 0 ≤ b) (hab : b < a) (theta : ι → ℝ)
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
      (⟪e (.inl (1, i)), Z (e (.inl (1, i)))⟫_ℂ).im) :
    (∑ i, weightedPhaseMinimum a b (theta i)) + Fintype.card κ * (a - b) ≤
      UnitarilyInvariantSeminorm.nuclear ℂ E E (A - (b : ℂ) • Z) := by
  have h := weightedNuclear_lowerBound_with_diagonal_defect
    a b hb hab theta e A Z hA0 hA1 hAf hdiag
  exact (le_add_of_nonneg_right
    (mul_nonneg hb (weightedDiagonalDefect_nonneg a b theta e Z hZ))).trans h

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

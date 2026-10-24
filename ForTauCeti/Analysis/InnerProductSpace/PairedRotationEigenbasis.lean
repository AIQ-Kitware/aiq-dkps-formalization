/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.PairedSpectralDecomposition
public import TauCeti.Analysis.InnerProductSpace.Positive.SquareRoot
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Paired eigenphases of a positive-real-part rotation

A rotation `R = C + i B`, with `C` positive, `B` symmetric and
`C² + B² = I`, has eigenphases in the closed right semicircle. If a
reflection reverses `B`, its nonzero phases have an orthonormal paired
basis and the reflection is diagonal on the fixed space.
-/

public section

noncomputable section

namespace TauCeti

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

private theorem positive_apply_of_square_apply
    (C : Module.End ℂ E) (hC : C.IsPositive) (x : E) (r : ℝ)
    (hx : C (C x) = (r : ℂ) • x) : C x = (Real.sqrt r : ℂ) • x := by
  have hC2 : (C ∘ₗ C).IsPositive := by
    simpa only [hC.adjoint_eq] using LinearMap.isPositive_adjoint_comp_self C
  have hroot : C = hC2.sqrt := hC2.sqrt_unique hC rfl
  rw [hroot]
  exact hC2.sqrt_apply_of_apply_eq_smul hx

/-- The supplied positive real part and reversing reflection determine an
actual orthonormal basis of paired rotation eigenphases and fixed vectors.
No principal-coordinate hypothesis is supplied. -/
theorem exists_paired_rotation_eigenbasis
    (R J : E ≃ₗᵢ[ℂ] E) (C B : Module.End ℂ E)
    (hC : C.IsPositive) (hB : B.IsSymmetric)
    (hR : ∀ x, R x = C x + Complex.I • B x)
    (hpy : C * C + B * B = 1) (hJ : Function.Involutive J)
    (hanti : ∀ x, B (J x) = -J (B x)) :
    ∃ n m : ℕ, ∃ (e : OrthonormalBasis ((Fin 2 × Fin n) ⊕ Fin m) ℂ E)
      (theta : Fin n → ℝ) (eps : Fin m → ℝ),
      (∀ i, theta i ∈ Set.Ioc 0 (Real.pi / 2)) ∧
      (∀ i, C (e (.inl (0, i))) = (Real.cos (theta i) : ℂ) • e (.inl (0, i))) ∧
      (∀ i, C (e (.inl (1, i))) = (Real.cos (theta i) : ℂ) • e (.inl (1, i))) ∧
      (∀ j, C (e (.inr j)) = e (.inr j)) ∧
      (∀ i, R (e (.inl (0, i))) =
        Complex.exp ((theta i : ℂ) * Complex.I) • e (.inl (0, i))) ∧
      (∀ i, R (e (.inl (1, i))) =
        Complex.exp ((-theta i : ℝ) * Complex.I) • e (.inl (1, i))) ∧
      (∀ j, R (e (.inr j)) = e (.inr j)) ∧
      (∀ i, J (e (.inl (0, i))) = e (.inl (1, i))) ∧
      (∀ j, J (e (.inr j)) = (eps j : ℂ) • e (.inr j)) := by
  obtain ⟨n, m, e, mu, eps, hmu, hB0, hB1, hBf, hJ0, hJf⟩ :=
    exists_paired_spectral_eigenbasis B hB J hJ hanti
  have hC_eigen (x : E) (r : ℝ) (hBx : B x = (r : ℂ) • x) :
      C x = (Real.sqrt (1 - r ^ 2) : ℂ) • x := by
    have hsq : C (C x) = ((1 - r ^ 2 : ℝ) : ℂ) • x := by
      have h := DFunLike.congr_fun hpy x
      change C (C x) + B (B x) = x at h
      rw [hBx, map_smul, hBx, smul_smul] at h
      rw [Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_one, sub_smul, one_smul]
      exact eq_sub_iff_add_eq.mpr (by simpa only [pow_two] using h)
    exact positive_apply_of_square_apply C hC x _ hsq
  have hR_eigen (x : E) (r : ℝ) (hBx : B x = (r : ℂ) • x) :
      R x = ((Real.sqrt (1 - r ^ 2) : ℂ) + (r : ℂ) * Complex.I) • x := by
    rw [hR, hC_eigen x r hBx, hBx, smul_smul, ← add_smul]
    congr 1
    ring
  have hmu1 (i) : mu i ≤ 1 := by
    have hr := hR_eigen (e (.inl (0, i))) (mu i) (hB0 i)
    have hn := R.norm_map (e (.inl (0, i)))
    rw [hr, norm_smul, e.norm_eq_one, mul_one] at hn
    have hs := congrArg (fun t : ℝ => t ^ 2) hn
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero,
      zero_add, add_zero, one_pow] at hs
    nlinarith [sq_nonneg (Real.sqrt (1 - mu i ^ 2)), hmu i]
  let theta (i : Fin n) := Real.arcsin (mu i)
  refine ⟨n, m, e, theta, eps, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hJ0, hJf⟩
  · intro i
    exact ⟨Real.arcsin_pos.mpr (hmu i), Real.arcsin_le_pi_div_two _⟩
  · intro i
    rw [hC_eigen _ _ (hB0 i)]
    simp [theta, Real.cos_arcsin]
  · intro i
    have hBi : B (e (.inl (1, i))) = ((-mu i : ℝ) : ℂ) • e (.inl (1, i)) := by
      calc
        _ = -(mu i : ℂ) • e (.inl (1, i)) := hB1 i
        _ = _ := congrArg (fun z : ℂ => z • e (.inl (1, i))) (Complex.ofReal_neg _).symm
    rw [hC_eigen _ _ hBi]
    simp [theta, Real.cos_arcsin]
  · intro j
    have hBzero : B (e (.inr j)) = ((0 : ℝ) : ℂ) • e (.inr j) := by
      simpa using hBf j
    rw [hC_eigen _ _ hBzero]
    simp
  · intro i
    rw [hR_eigen _ _ (hB0 i), Complex.exp_ofReal_mul_I]
    simp only [theta, Real.cos_arcsin, Real.sin_arcsin (by linarith [hmu i]) (hmu1 i)]
    simp
  · intro i
    have hBi : B (e (.inl (1, i))) = ((-mu i : ℝ) : ℂ) • e (.inl (1, i)) := by
      calc
        _ = -(mu i : ℂ) • e (.inl (1, i)) := hB1 i
        _ = _ := congrArg (fun z : ℂ => z • e (.inl (1, i))) (Complex.ofReal_neg _).symm
    rw [hR_eigen _ _ hBi, Complex.exp_ofReal_mul_I]
    simp only [theta, Real.cos_neg, Real.sin_neg, Real.cos_arcsin,
      Real.sin_arcsin (by linarith [hmu i]) (hmu1 i), neg_sq, Complex.ofReal_neg]
  · intro j
    have hBzero : B (e (.inr j)) = ((0 : ℝ) : ℂ) • e (.inr j) := by
      simpa using hBf j
    rw [hR_eigen _ _ hBzero]
    simp

end TauCeti

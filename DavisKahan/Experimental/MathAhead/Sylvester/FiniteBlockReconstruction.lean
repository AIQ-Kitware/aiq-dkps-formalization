/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.MathAhead.Sylvester.OrthogonalIdempotentExp
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Finite spectral-block Sylvester reconstruction

This is the purely algebraic and scalar-Fourier core of the separated
Sylvester theorem.  It is parameterized by a scalar kernel and its reciprocal
identity, so it is independent of the particular Haagerup--Zsido construction.
-/

namespace ForMathlib
namespace DavisKahanExt

open MeasureTheory Set
open scoped InnerProductSpace BigOperators

noncomputable section

universe u v

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

/-- Finite diagonal operator with respect to a projection family. -/
noncomputable def finiteDiagonalOperator {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {n : ℕ} (P : Fin n → H →L[ℂ] H) (a : Fin n → ℝ) : H →L[ℂ] H :=
  ∑ i, (a i : ℂ) • P i

/-- The unitary exponential of a finite real diagonal operator acts
coefficientwise. -/
theorem unitaryGroup_finiteDiagonal
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {n : ℕ} (P : Fin n → H →L[ℂ] H) (a : Fin n → ℝ)
    (hidem : ∀ i, P i * P i = P i)
    (horth : ∀ i j, i ≠ j → P i * P j = 0)
    (hsum : ∑ i, P i = (1 : H →L[ℂ] H)) (t : ℝ) :
    NormedSpace.exp (((t : ℂ) * Complex.I) • finiteDiagonalOperator P a) =
      ∑ i, Complex.exp (((t * a i : ℝ) : ℂ) * Complex.I) • P i := by
  unfold finiteDiagonalOperator
  have hscale : (((t : ℂ) * Complex.I) • ∑ i, (a i : ℂ) • P i) =
      ((t : ℂ) • ∑ i, ((a i : ℂ) * Complex.I) • P i) := by
    rw [Finset.smul_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp [smul_smul]
    ring
  rw [hscale]
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    exp_finset_orthogonal_idempotents P
      (fun i => (a i : ℂ) * Complex.I) hidem horth hsum t

/-- A diagonal block selects the corresponding coefficient on the left. -/
theorem finiteDiagonal_select_left
    {m : ℕ} (P : Fin m → F →L[ℂ] F) (a : Fin m → ℝ)
    (hidem : ∀ i, P i * P i = P i)
    (horth : ∀ i j, i ≠ j → P i * P j = 0)
    (i : Fin m) :
    P i ∘L finiteDiagonalOperator P a = (a i : ℂ) • P i := by
  unfold finiteDiagonalOperator
  rw [ContinuousLinearMap.comp_finset_sum]
  apply Finset.sum_eq_single i
  · intro j hj hji
    rw [ContinuousLinearMap.comp_smul]
    change (a j : ℂ) • (P i * P j) = 0
    rw [horth i j hji, smul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi
  · rw [ContinuousLinearMap.comp_smul]
    change (a i : ℂ) • (P i * P i) = _
    rw [hidem i]

/-- A diagonal block selects the corresponding coefficient on the right. -/
theorem finiteDiagonal_select_right
    {m : ℕ} (P : Fin m → E →L[ℂ] E) (a : Fin m → ℝ)
    (hidem : ∀ i, P i * P i = P i)
    (horth : ∀ i j, i ≠ j → P i * P j = 0)
    (i : Fin m) :
    finiteDiagonalOperator P a ∘L P i = (a i : ℂ) • P i := by
  unfold finiteDiagonalOperator
  rw [ContinuousLinearMap.finset_sum_comp]
  apply Finset.sum_eq_single i
  · intro j hj hji
    rw [ContinuousLinearMap.smul_comp]
    change (a j : ℂ) • (P j * P i) = 0
    rw [horth j i hji, smul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi
  · rw [ContinuousLinearMap.smul_comp]
    change (a i : ℂ) • (P i * P i) = _
    rw [hidem i]

/-- The Sylvester defect restricted to one spectral rectangle is scalar. -/
theorem finiteDiagonal_sylvester_block
    {m n : ℕ}
    (P : Fin m → F →L[ℂ] F) (Q : Fin n → E →L[ℂ] E)
    (a : Fin m → ℝ) (b : Fin n → ℝ)
    (hPid : ∀ i, P i * P i = P i)
    (hPorth : ∀ i j, i ≠ j → P i * P j = 0)
    (hQid : ∀ i, Q i * Q i = Q i)
    (hQorth : ∀ i j, i ≠ j → Q i * Q j = 0)
    (X : E →L[ℂ] F) (i : Fin m) (j : Fin n) :
    P i ∘L (finiteDiagonalOperator P a ∘L X -
      X ∘L finiteDiagonalOperator Q b) ∘L Q j =
      (((a i - b j : ℝ) : ℂ)) • (P i ∘L X ∘L Q j) := by
  rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]
  rw [← ContinuousLinearMap.comp_assoc,
    finiteDiagonal_select_left P a hPid hPorth i,
    ContinuousLinearMap.smul_comp]
  rw [ContinuousLinearMap.comp_assoc X,
    finiteDiagonal_select_right Q b hQid hQorth j,
    ContinuousLinearMap.comp_smul]
  ext x
  simp [sub_smul, ContinuousLinearMap.comp_apply]
  module

/-- The full operator is the sum of all rectangular blocks. -/
theorem eq_sum_rectangular_blocks
    {m n : ℕ}
    (P : Fin m → F →L[ℂ] F) (Q : Fin n → E →L[ℂ] E)
    (hPsum : ∑ i, P i = (1 : F →L[ℂ] F))
    (hQsum : ∑ j, Q j = (1 : E →L[ℂ] E))
    (X : E →L[ℂ] F) :
    X = ∑ i, ∑ j, P i ∘L X ∘L Q j := by
  calc
    X = (∑ i, P i) ∘L X ∘L (∑ j, Q j) := by
      rw [hPsum, hQsum]
      simp
    _ = ∑ i, ∑ j, P i ∘L X ∘L Q j := by
      simp [ContinuousLinearMap.finset_sum_comp,
        ContinuousLinearMap.comp_finset_sum]

/-- Expansion of the conjugated Sylvester defect into scalar spectral blocks. -/
theorem finiteDiagonal_orbit_expansion
    {m n : ℕ}
    (P : Fin m → F →L[ℂ] F) (Q : Fin n → E →L[ℂ] E)
    (a : Fin m → ℝ) (b : Fin n → ℝ)
    (hPid : ∀ i, P i * P i = P i)
    (hPorth : ∀ i j, i ≠ j → P i * P j = 0)
    (hPsum : ∑ i, P i = (1 : F →L[ℂ] F))
    (hQid : ∀ i, Q i * Q i = Q i)
    (hQorth : ∀ i j, i ≠ j → Q i * Q j = 0)
    (hQsum : ∑ i, Q i = (1 : E →L[ℂ] E))
    (X : E →L[ℂ] F) (t : ℝ) :
    NormedSpace.exp ((((t : ℂ) * Complex.I) • finiteDiagonalOperator P a)) ∘L
        (finiteDiagonalOperator P a ∘L X - X ∘L finiteDiagonalOperator Q b) ∘L
        NormedSpace.exp ((((-t : ℝ) : ℂ) * Complex.I) • finiteDiagonalOperator Q b) =
      ∑ i, ∑ j,
        Complex.exp ((((t * (a i - b j) : ℝ) : ℂ) * Complex.I)) •
          ((((a i - b j : ℝ) : ℂ)) • (P i ∘L X ∘L Q j)) := by
  rw [unitaryGroup_finiteDiagonal P a hPid hPorth hPsum t,
    unitaryGroup_finiteDiagonal Q b hQid hQorth hQsum (-t)]
  simp only [ContinuousLinearMap.finset_sum_comp,
    ContinuousLinearMap.comp_finset_sum, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_smul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [finiteDiagonal_sylvester_block P Q a b hPid hPorth hQid hQorth X i j]
  rw [smul_smul, smul_smul]
  congr 1
  rw [Complex.exp_mul, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Integrability of one scalar oscillatory block against an `L1` kernel. -/
theorem integrable_scalar_oscillatory_block
    (μ : ℝ → ℂ) (hμ : Integrable μ)
    (r : ℝ) (T : E →L[ℂ] F) :
    Integrable fun t : ℝ =>
      (μ t * Complex.exp ((((t * r : ℝ) : ℂ) * Complex.I))) • T := by
  have hnorm : ∀ t : ℝ,
      ‖(μ t * Complex.exp ((((t * r : ℝ) : ℂ) * Complex.I))) • T‖ =
        ‖μ t‖ * ‖T‖ := by
    intro t
    rw [norm_smul, norm_mul, Complex.norm_exp]
    have hre : ((((t * r : ℝ) : ℂ) * Complex.I)).re = 0 := by simp
    rw [hre, Real.exp_zero, one_mul]
  apply Integrable.mono' (hμ.norm.const_mul ‖T‖)
  · exact (hμ.aestronglyMeasurable.mul
      (Complex.continuous_exp.comp
        (Complex.continuous_ofReal.comp
          (continuous_const.mul continuous_id) |>.mul continuous_const)).aestronglyMeasurable).smul
      stronglyMeasurable_const
  · filter_upwards [] with t
    rw [hnorm]

/-- Finite blockwise reconstruction from the scalar reciprocal identity. -/
theorem finiteDiagonal_sylvester_reconstruction
    {m n : ℕ}
    (P : Fin m → F →L[ℂ] F) (Q : Fin n → E →L[ℂ] E)
    (a : Fin m → ℝ) (b : Fin n → ℝ)
    (hPid : ∀ i, P i * P i = P i)
    (hPorth : ∀ i j, i ≠ j → P i * P j = 0)
    (hPsum : ∑ i, P i = (1 : F →L[ℂ] F))
    (hQid : ∀ i, Q i * Q i = Q i)
    (hQorth : ∀ i j, i ≠ j → Q i * Q j = 0)
    (hQsum : ∑ i, Q i = (1 : E →L[ℂ] E))
    (μ : ℝ → ℂ) (hμ : Integrable μ)
    (hscalar : ∀ i j,
      ∫ t : ℝ, μ t *
        Complex.exp ((((t * (a i - b j) : ℝ) : ℂ) * Complex.I)) =
          (((a i - b j)⁻¹ : ℝ) : ℂ))
    (hne : ∀ i j, a i - b j ≠ 0)
    (X : E →L[ℂ] F) :
    X = ∫ t : ℝ, μ t •
      (NormedSpace.exp ((((t : ℂ) * Complex.I) • finiteDiagonalOperator P a)) ∘L
        (finiteDiagonalOperator P a ∘L X - X ∘L finiteDiagonalOperator Q b) ∘L
        NormedSpace.exp ((((-t : ℝ) : ℂ) * Complex.I) • finiteDiagonalOperator Q b)) := by
  have horbit := finiteDiagonal_orbit_expansion P Q a b
    hPid hPorth hPsum hQid hQorth hQsum X
  have hintegrable : ∀ i j, Integrable fun t : ℝ =>
      μ t •
        (Complex.exp ((((t * (a i - b j) : ℝ) : ℂ) * Complex.I)) •
          ((((a i - b j : ℝ) : ℂ)) • (P i ∘L X ∘L Q j))) := by
    intro i j
    simpa [smul_smul, mul_assoc] using
      integrable_scalar_oscillatory_block μ hμ (a i - b j)
        ((((a i - b j : ℝ) : ℂ)) • (P i ∘L X ∘L Q j))
  calc
    X = ∑ i, ∑ j, P i ∘L X ∘L Q j :=
      eq_sum_rectangular_blocks P Q hPsum hQsum X
    _ = ∑ i, ∑ j,
        ∫ t : ℝ, μ t •
          (Complex.exp ((((t * (a i - b j) : ℝ) : ℂ) * Complex.I)) •
            ((((a i - b j : ℝ) : ℂ)) • (P i ∘L X ∘L Q j))) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [← integral_smul_const]
      rw [smul_smul]
      rw [hscalar i j]
      have hc : (((a i - b j)⁻¹ : ℝ) : ℂ) *
          (((a i - b j : ℝ) : ℂ)) = 1 := by
        norm_cast
        exact inv_mul_cancel₀ (hne i j)
      rw [hc, one_smul]
    _ = ∫ t : ℝ, ∑ i, ∑ j,
        μ t •
          (Complex.exp ((((t * (a i - b j) : ℝ) : ℂ) * Complex.I)) •
            ((((a i - b j : ℝ) : ℂ)) • (P i ∘L X ∘L Q j))) := by
      rw [integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [integral_finset_sum]
        exact fun j hj => hintegrable i j
      · intro i hi
        exact (Finset.integrable_finset_sum _ fun j hj => hintegrable i j)
    _ = ∫ t : ℝ, μ t •
      (NormedSpace.exp ((((t : ℂ) * Complex.I) • finiteDiagonalOperator P a)) ∘L
        (finiteDiagonalOperator P a ∘L X - X ∘L finiteDiagonalOperator Q b) ∘L
        NormedSpace.exp ((((-t : ℝ) : ℂ) * Complex.I) • finiteDiagonalOperator Q b)) := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [horbit t, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.smul_sum]

end
end DavisKahanExt
end ForMathlib

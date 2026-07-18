/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import Mathlib.Analysis.InnerProductSpace.SingularValues
import ForMathlib.Analysis.Normed.Operator.ApproximationNumber
import ForMathlib.Analysis.InnerProductSpace.CourantFischer

/-!
# Approximation numbers on finite-dimensional Hilbert spaces

This module begins the bridge between the finite-dimensional singular-value
library and approximation numbers defined by finite-rank operator-norm
approximation.

The main result is the lower half of Eckart--Young: the `n`th singular value of
a finite-dimensional Hilbert-space map is no larger than its `n`th
approximation number. The proof uses the Courant--Fischer `(n+1)`-dimensional
right singular subspace and dimension counting against the kernel of an
arbitrary rank-at-most-`n` approximant.
-/

namespace ContinuousLinearMap

open Module (finrank)
open scoped InnerProductSpace

noncomputable section

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- Lower Eckart--Young inequality in operator-norm form: an operator of rank
at most `n` cannot approximate `T` more closely than the `n`th singular value
of `T`. -/
theorem singularValues_le_norm_sub_of_rank_le
    (T R : E →L[𝕜] F) (n : ℕ)
    (hR : R.rank ≤ (n : Cardinal)) :
    T.toLinearMap.singularValues n ≤ ‖T - R‖ := by
  by_cases hn : finrank 𝕜 E ≤ n
  · rw [T.toLinearMap.singularValues_of_finrank_le hn]
    exact norm_nonneg _
  · have hnlt : n < finrank 𝕜 E := Nat.lt_of_not_ge hn
    let k : Fin (finrank 𝕜 E) := ⟨n, hnlt⟩
    obtain ⟨V, hVdim, hVlow⟩ :=
      ForMathlib.forall_unit_vector_eigenvalue_le_re_inner
        T.toLinearMap.isSymmetric_adjoint_comp_self rfl k
    have hVdim' : finrank 𝕜 V = n + 1 := by
      simpa [k] using hVdim
    have hRcard : (finrank 𝕜 R.range : Cardinal) ≤ (n : Cardinal) := by
      calc
        (finrank 𝕜 R.range : Cardinal) = R.rank :=
          Module.finrank_eq_rank' 𝕜 R.range
        _ ≤ (n : Cardinal) := hR
    have hRfin : finrank 𝕜 R.range ≤ n := by
      exact_mod_cast hRcard
    have hRker : finrank 𝕜 R.ker = finrank 𝕜 E - finrank 𝕜 R.range := by
      have hnull := R.toLinearMap.finrank_range_add_finrank_ker
      omega
    have hinf : V ⊓ R.ker ≠ ⊥ := by
      intro hbot
      have hdim := Submodule.finrank_sup_add_finrank_inf_eq V R.ker
      rw [hbot, finrank_bot, add_zero, hVdim', hRker] at hdim
      have hsup : finrank 𝕜 (V ⊔ R.ker : Submodule 𝕜 E) ≤ finrank 𝕜 E :=
        Submodule.finrank_le _
      omega
    obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hinf
    obtain ⟨hzV, hzker⟩ := Submodule.mem_inf.mp hz
    have hzNorm : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
    let x : E := ((‖z‖⁻¹ : ℝ) : 𝕜) • z
    have hxV : x ∈ V := V.smul_mem _ hzV
    have hxNorm : ‖x‖ = 1 := by
      simp only [x, norm_smul, RCLike.norm_ofReal, abs_inv, abs_norm]
      exact inv_mul_cancel₀ hzNorm
    have hRx : R x = 0 := by
      have hRz : R z = 0 := LinearMap.mem_ker.mp hzker
      simp [x, hRz]
    have hsq : T.toLinearMap.singularValues n ^ 2 ≤ ‖T - R‖ ^ 2 := by
      calc
        T.toLinearMap.singularValues n ^ 2
            = T.toLinearMap.isSymmetric_adjoint_comp_self.eigenvalues rfl k :=
          T.toLinearMap.sq_singularValues_fin rfl k
        _ ≤ RCLike.re
              ⟪(T.toLinearMap.adjoint ∘ₗ T.toLinearMap) x, x⟫_𝕜 :=
          hVlow x hxV hxNorm
        _ = ‖T x‖ ^ 2 := by
          rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left,
            inner_self_eq_norm_sq]
          rfl
        _ = ‖(T - R) x‖ ^ 2 := by
          rw [sub_apply, hRx, sub_zero]
        _ ≤ ‖T - R‖ ^ 2 := by
          have hxop := (T - R).le_opNorm x
          rw [hxNorm, mul_one] at hxop
          nlinarith [norm_nonneg ((T - R) x), norm_nonneg (T - R)]
    exact le_of_sq_le_sq hsq (norm_nonneg _)

/-- The `n`th finite-dimensional singular value is bounded by the `n`th
approximation number. This is the lower half of the finite-dimensional
Eckart--Young identification. -/
theorem singularValues_le_approximationNumber
    (T : E →L[𝕜] F) (n : ℕ) :
    (⟨T.toLinearMap.singularValues n,
      T.toLinearMap.singularValues_nonneg n⟩ : NNReal) ≤
      T.approximationNumber n := by
  apply T.le_approximationNumber
  intro R hR
  exact_mod_cast singularValues_le_norm_sub_of_rank_le T R n hR

end

end ContinuousLinearMap

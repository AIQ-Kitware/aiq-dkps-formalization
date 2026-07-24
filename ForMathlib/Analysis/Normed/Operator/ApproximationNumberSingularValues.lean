/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import ForMathlib.Analysis.Normed.Operator.ApproximationNumber
import ForMathlib.Analysis.InnerProductSpace.CourantFischer

/-!
# Approximation numbers on finite-dimensional Hilbert spaces

This module begins the bridge between the finite-dimensional singular-value
library and approximation numbers defined by finite-rank operator-norm
approximation.

The main result is the finite-dimensional Eckart--Young identification: the
`n`th approximation number equals the `n`th singular value. The lower bound
uses the Courant--Fischer `(n+1)`-dimensional right singular subspace and
dimension counting against the kernel of an arbitrary rank-at-most-`n`
approximant. The upper bound projects onto the first `n` right singular
directions and controls the complementary spectral tail.
-/

namespace ContinuousLinearMap

open Module (finrank)
open scoped InnerProductSpace

noncomputable section

universe u v w

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} {F : Type w}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The first `k` indices of `Fin n` have cardinality `k`. -/
private theorem card_filter_lt {n k : ℕ} (hk : k ≤ n) :
    (Finset.univ.filter (fun j : Fin n => (j : ℕ) < k)).card = k := by
  rcases lt_or_eq_of_le hk with hlt | rfl
  · have h : (Finset.univ.filter (fun j : Fin n => (j : ℕ) < k)) =
        Finset.Iio (⟨k, hlt⟩ : Fin n) := by
      ext j
      simp [Fin.lt_def]
    rw [h, Fin.card_Iio]
  · have h : (Finset.univ.filter (fun j : Fin k => (j : ℕ) < k)) = Finset.univ := by
      ext j
      simp
    rw [h, Finset.card_univ, Fintype.card_fin]

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

/-- Upper Eckart--Young inequality: projection onto the first `n` right
singular directions gives a rank-at-most-`n` approximant whose error is bounded
by the `n`th singular value. -/
theorem approximationNumber_le_singularValues
    (T : E →L[𝕜] F) (n : ℕ) :
    T.approximationNumber n ≤
      (⟨T.toLinearMap.singularValues n,
        T.toLinearMap.singularValues_nonneg n⟩ : NNReal) := by
  classical
  by_cases hn : finrank 𝕜 E ≤ n
  · -- The rank of `T` lives in the codomain universe and `Module.rank 𝕜 E` in
    -- the domain universe, so compare them through `Cardinal.lift`.
    have hTrank : T.rank ≤ (n : Cardinal) := by
      refine Cardinal.le_natCast_of_lift_le
        ((lift_rank_range_le T.toLinearMap).trans ?_)
      calc
        Cardinal.lift.{w} (Module.rank 𝕜 E)
            = Cardinal.lift.{w} ((finrank 𝕜 E : Cardinal)) := by
          rw [← Module.finrank_eq_rank' 𝕜 E]
        _ = ((finrank 𝕜 E : ℕ) : Cardinal) := Cardinal.lift_natCast _
        _ ≤ (n : Cardinal) := by exact_mod_cast hn
    have hle : T.approximationNumber n ≤ (0 : NNReal) := by
      have h := T.approximationNumber_le (R := T) hTrank
      have hdist : ‖T - T‖₊ = (0 : NNReal) := by simp
      rw [hdist] at h
      exact h
    exact hle.trans (bot_le : (0 : NNReal) ≤
      (⟨T.toLinearMap.singularValues n,
        T.toLinearMap.singularValues_nonneg n⟩ : NNReal))
  · have hnlt : n < finrank 𝕜 E := Nat.lt_of_not_ge hn
    let A : E →ₗ[𝕜] F := T.toLinearMap
    let hGram : (A.adjoint ∘ₗ A).IsSymmetric := A.isSymmetric_adjoint_comp_self
    let b : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E := hGram.eigenvectorBasis rfl
    let W : Submodule 𝕜 E :=
      ForMathlib.specSubspace b (fun i : Fin (finrank 𝕜 E) => (i : ℕ) < n)
    let k : Fin (finrank 𝕜 E) := ⟨n, hnlt⟩
    have hWdim : finrank 𝕜 W = n := by
      dsimp only [W]
      rw [ForMathlib.finrank_specSubspace, card_filter_lt hnlt.le]
    have hPrank : W.starProjection.rank = (n : Cardinal) := by
      change Module.rank 𝕜 W.starProjection.range = (n : Cardinal)
      rw [Submodule.range_starProjection, ← Module.finrank_eq_rank' 𝕜 W, hWdim]
    let R : E →L[𝕜] F := T ∘L W.starProjection
    -- Cross-universe once the codomain is independent, so route the bound
    -- through the natural-number rank estimate.
    have hRrank : R.rank ≤ (n : Cardinal) :=
      ContinuousLinearMap.rank_comp_left_le_of_rank_le T W.starProjection
        hPrank.le
    have htail : Wᗮ = ForMathlib.specSubspace b
        (fun i : Fin (finrank 𝕜 E) => ¬ (i : ℕ) < n) := by
      exact ForMathlib.orthogonal_specSubspace b
        (fun i : Fin (finrank 𝕜 E) => (i : ℕ) < n)
    have htailQuad {y : E} (hy : y ∈ Wᗮ) :
        RCLike.re ⟪(A.adjoint ∘ₗ A) y, y⟫_𝕜 ≤
          A.singularValues n ^ 2 * ‖y‖ ^ 2 := by
      have hy' : y ∈ ForMathlib.specSubspace b
          (fun i : Fin (finrank 𝕜 E) => ¬ (i : ℕ) < n) := by
        rw [← htail]
        exact hy
      have hbound := ForMathlib.re_inner_map_self_le_of_mem_specSubspace
        hGram rfl
        (p := fun i : Fin (finrank 𝕜 E) => ¬ (i : ℕ) < n)
        (c := hGram.eigenvalues rfl k)
        (fun i hi => hGram.eigenvalues_antitone rfl (by
          change n ≤ (i : ℕ)
          exact Nat.le_of_not_gt hi))
        hy'
      calc
        RCLike.re ⟪(A.adjoint ∘ₗ A) y, y⟫_𝕜 ≤
            hGram.eigenvalues rfl k * ‖y‖ ^ 2 := hbound
        _ = A.singularValues n ^ 2 * ‖y‖ ^ 2 := by
          rw [← A.sq_singularValues_fin rfl k]
    have htailNorm {y : E} (hy : y ∈ Wᗮ) :
        ‖T y‖ ≤ A.singularValues n * ‖y‖ := by
      have hsq : ‖T y‖ ^ 2 ≤ A.singularValues n ^ 2 * ‖y‖ ^ 2 := by
        calc
          ‖T y‖ ^ 2 = RCLike.re ⟪(A.adjoint ∘ₗ A) y, y⟫_𝕜 := by
            rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left,
              inner_self_eq_norm_sq]
            rfl
          _ ≤ A.singularValues n ^ 2 * ‖y‖ ^ 2 := htailQuad hy
      have hsq' : ‖T y‖ ^ 2 ≤ (A.singularValues n * ‖y‖) ^ 2 := by
        calc
          ‖T y‖ ^ 2 ≤ A.singularValues n ^ 2 * ‖y‖ ^ 2 := hsq
          _ = (A.singularValues n * ‖y‖) ^ 2 := by ring
      exact le_of_sq_le_sq hsq'
        (mul_nonneg (A.singularValues_nonneg n) (norm_nonneg y))
    have htailOpNorm : ‖T ∘L Wᗮ.starProjection‖ ≤ A.singularValues n := by
      refine (T ∘L Wᗮ.starProjection).opNorm_le_bound
        (A.singularValues_nonneg n) ?_
      intro x
      have hy : Wᗮ.starProjection x ∈ Wᗮ := Wᗮ.starProjection_apply_mem x
      calc
        ‖(T ∘L Wᗮ.starProjection) x‖ = ‖T (Wᗮ.starProjection x)‖ := rfl
        _ ≤ A.singularValues n * ‖Wᗮ.starProjection x‖ := htailNorm hy
        _ ≤ A.singularValues n * ‖x‖ :=
          mul_le_mul_of_nonneg_left (Wᗮ.norm_starProjection_apply_le x)
            (A.singularValues_nonneg n)
    have herr : T - R = T ∘L Wᗮ.starProjection := by
      ext x
      change T x - T (W.starProjection x) = T (Wᗮ.starProjection x)
      rw [Submodule.starProjection_orthogonal_val, map_sub]
    have htailOpNorm' :
        ‖T ∘L Wᗮ.starProjection‖ ≤ T.toLinearMap.singularValues n := by
      simpa [A] using htailOpNorm
    have htailNN :
        ‖T ∘L Wᗮ.starProjection‖₊ ≤
          (⟨T.toLinearMap.singularValues n,
            T.toLinearMap.singularValues_nonneg n⟩ : NNReal) := by
      apply NNReal.coe_le_coe.mp
      change ‖T ∘L Wᗮ.starProjection‖ ≤ T.toLinearMap.singularValues n
      exact htailOpNorm'
    have happrox :
        T.approximationNumber n ≤ ‖T ∘L Wᗮ.starProjection‖₊ := by
      simpa only [herr] using T.approximationNumber_le hRrank
    exact happrox.trans htailNN

/-- Finite-dimensional Eckart--Young identification for the zero-based
approximation-number convention used in this project. -/
theorem approximationNumber_eq_singularValues
    (T : E →L[𝕜] F) (n : ℕ) :
    T.approximationNumber n =
      (⟨T.toLinearMap.singularValues n,
        T.toLinearMap.singularValues_nonneg n⟩ : NNReal) := by
  apply le_antisymm
  · exact approximationNumber_le_singularValues T n
  · exact singularValues_le_approximationNumber T n

end

end ContinuousLinearMap

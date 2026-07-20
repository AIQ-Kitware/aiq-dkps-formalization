/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Thinking
-/

import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Finite-dimensional self-adjoint functional calculus

For a symmetric endomorphism on a finite-dimensional real or complex inner-product
space, apply a real scalar function to the ordered eigenvalues and reconstruct the
operator in the associated orthonormal eigenbasis.

The construction is intended as a small `RCLike` counterpart of the continuous
functional calculus.  It is sufficient for functions such as `arcsin` and the
totalized tangent functions used by finite-dimensional operator-angle theory.
-/

namespace FiniteDimensional

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- Apply a real function to the spectrum of a finite-dimensional symmetric
endomorphism. -/
noncomputable def selfAdjointFunctionalCalculus
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (f : ℝ → ℝ) : E →ₗ[𝕜] E :=
  ∑ i : Fin (finrank 𝕜 E),
    ((f (hT.eigenvalues rfl i) : ℝ) : 𝕜) •
      (InnerProductSpace.rankOne 𝕜
        (hT.eigenvectorBasis rfl i)
        (hT.eigenvectorBasis rfl i)).toLinearMap

/-- The functional calculus acts diagonally in the chosen eigenbasis. -/
theorem selfAdjointFunctionalCalculus_apply_eigenvectorBasis
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (f : ℝ → ℝ)
    (k : Fin (finrank 𝕜 E)) :
    selfAdjointFunctionalCalculus hT f (hT.eigenvectorBasis rfl k) =
      ((f (hT.eigenvalues rfl k) : ℝ) : 𝕜) •
        hT.eigenvectorBasis rfl k := by
  classical
  unfold selfAdjointFunctionalCalculus
  rw [LinearMap.sum_apply]
  refine (Finset.sum_eq_single k ?_ ?_).trans ?_
  · intro i _ hik
    simp [InnerProductSpace.rankOne_apply,
      orthonormal_iff_ite.mp (hT.eigenvectorBasis rfl).orthonormal i k,
      if_neg hik]
  · intro hk
    exact absurd (Finset.mem_univ k) hk
  · simp [InnerProductSpace.rankOne_apply]

/-- Applying a real function to a symmetric operator remains symmetric. -/
theorem selfAdjointFunctionalCalculus_isSymmetric
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (f : ℝ → ℝ) :
    (selfAdjointFunctionalCalculus hT f).IsSymmetric := by
  classical
  unfold selfAdjointFunctionalCalculus
  induction (Finset.univ : Finset (Fin (finrank 𝕜 E))) using Finset.induction_on with
  | empty => simp
  | @insert i s hi hs =>
      rw [Finset.sum_insert hi]
      exact
        ((InnerProductSpace.isSymmetric_rankOne_self
          (hT.eigenvectorBasis rfl i)).smul
            (RCLike.conj_ofReal (f (hT.eigenvalues rfl i)))).add hs

/-- The identity function recovers the original symmetric operator. -/
theorem selfAdjointFunctionalCalculus_id
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) :
    selfAdjointFunctionalCalculus hT id = T := by
  apply (hT.eigenvectorBasis rfl).toBasis.ext
  intro i
  rw [OrthonormalBasis.coe_toBasis,
    selfAdjointFunctionalCalculus_apply_eigenvectorBasis,
    hT.apply_eigenvectorBasis]
  rfl

/-- Functions agreeing on every eigenvalue produce the same operator. -/
theorem selfAdjointFunctionalCalculus_congr
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) {f g : ℝ → ℝ}
    (hfg : ∀ i : Fin (finrank 𝕜 E),
      f (hT.eigenvalues rfl i) = g (hT.eigenvalues rfl i)) :
    selfAdjointFunctionalCalculus hT f =
      selfAdjointFunctionalCalculus hT g := by
  apply (hT.eigenvectorBasis rfl).toBasis.ext
  intro i
  simp only [OrthonormalBasis.coe_toBasis,
    selfAdjointFunctionalCalculus_apply_eigenvectorBasis]
  rw [hfg i]

/-- Composition corresponds to pointwise multiplication of scalar functions. -/
theorem selfAdjointFunctionalCalculus_comp
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (f g : ℝ → ℝ) :
    selfAdjointFunctionalCalculus hT f ∘ₗ
        selfAdjointFunctionalCalculus hT g =
      selfAdjointFunctionalCalculus hT (fun x => f x * g x) := by
  apply (hT.eigenvectorBasis rfl).toBasis.ext
  intro i
  simp only [OrthonormalBasis.coe_toBasis, LinearMap.comp_apply,
    selfAdjointFunctionalCalculus_apply_eigenvectorBasis, map_smul, smul_smul,
    RCLike.ofReal_mul, mul_comm]

/-- Constant zero gives the zero operator. -/
@[simp] theorem selfAdjointFunctionalCalculus_zero
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) :
    selfAdjointFunctionalCalculus hT (fun _ => 0) = 0 := by
  apply (hT.eigenvectorBasis rfl).toBasis.ext
  intro i
  simp [selfAdjointFunctionalCalculus_apply_eigenvectorBasis]

end FiniteDimensional

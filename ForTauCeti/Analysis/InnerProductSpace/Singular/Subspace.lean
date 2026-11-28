/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 4.8
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.Polar.Decomposition

/-!
# Gram conjugation at the selected polar unitary

On a finite-dimensional inner product space, the kernel-completed polar
unitary conjugates the source Gram operator to the target Gram operator.
-/

public section

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- The Gram operators `A A⋆` and `A⋆A` are unitarily conjugate:
`A A⋆ = U (A⋆A) U⁻¹` with `U = choosePolarUnitary A`.  From `A = U |A|`,
`A⋆ = |A| U⁻¹`, so `A A⋆ = U |A|² U⁻¹ = U (A⋆A) U⁻¹`. -/
theorem comp_adjoint_eq_conj_adjoint_comp (A : E →ₗ[𝕜] E) :
    A ∘ₗ A.adjoint = (choosePolarUnitary A).toLinearMap ∘ₗ (A.adjoint ∘ₗ A)
      ∘ₗ (choosePolarUnitary A).symm.toLinearMap := by
  set U := choosePolarUnitary A with hU
  have hpolar : A = U.toLinearMap ∘ₗ A.operatorAbs := polar_decomposition_choosePolarUnitary A
  have hadj : A.adjoint = A.operatorAbs ∘ₗ U.symm.toLinearMap := by
    conv_lhs => rw [hpolar]
    rw [LinearMap.adjoint_comp, (A.isPositive_operatorAbs).adjoint_eq,
      U.adjoint_toLinearMap_eq_symm]
  calc A ∘ₗ A.adjoint
      = (U.toLinearMap ∘ₗ A.operatorAbs) ∘ₗ (A.operatorAbs ∘ₗ U.symm.toLinearMap) := by
        rw [← hpolar, ← hadj]
    _ = U.toLinearMap ∘ₗ (A.operatorAbs ∘ₗ A.operatorAbs) ∘ₗ U.symm.toLinearMap := by
        ext v; simp only [LinearMap.comp_apply]
    _ = U.toLinearMap ∘ₗ (A.adjoint ∘ₗ A) ∘ₗ U.symm.toLinearMap := by
      rw [LinearMap.operatorAbs_sq A]

end TauCeti

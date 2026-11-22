/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI gpt-6.1-sol
-/
module

public import TauCeti.Analysis.Fredholm.Prod

/-! # Fredholm index of a conjugated product

This donor packages the finite/free kernel and cokernel instances supplied by Fredholm
hypotheses for the accepted product-index and coordinate-invariance laws.
-/

public section

namespace ContinuousLinearMap

variable {K E₁ E₂ : Type*} [NontriviallyNormedField K]
variable [AddCommGroup E₁] [TopologicalSpace E₁] [Module K E₁] [IsTopologicalAddGroup E₁]
variable [AddCommGroup E₂] [TopologicalSpace E₂] [Module K E₂] [IsTopologicalAddGroup E₂]

/-- Conjugating a product of Fredholm operators preserves the sum of their indices. -/
lemma IsFredholm.index_conj_prodMap
    [ContinuousConstSMul K E₁] [ContinuousConstSMul K E₂]
    {G : Type*} [AddCommGroup G] [TopologicalSpace G] [Module K G]
    [IsTopologicalAddGroup G] [ContinuousConstSMul K G]
    {T : E₁ →L[K] E₁} {S : E₂ →L[K] E₂}
    (hT : IsFredholm T) (hS : IsFredholm S) (e : (E₁ × E₂) ≃L[K] G) :
    (e.conjContinuousAlgEquiv (T.prodMap S)).index = T.index + S.index := by
  let := hT.finite_ker
  let := hS.finite_ker
  let := hT.finite_coker
  let := hS.finite_coker
  let := Module.Free.of_divisionRing K T.ker
  let := Module.Free.of_divisionRing K S.ker
  let := Module.Free.of_divisionRing K (E₁ ⧸ T.range)
  let := Module.Free.of_divisionRing K (E₂ ⧸ S.range)
  rw [ContinuousLinearEquiv.conjContinuousAlgEquiv_apply, index_equiv_comp,
    index_comp_equiv, index_prodMap]

end ContinuousLinearMap

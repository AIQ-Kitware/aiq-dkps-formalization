/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI gpt-6.1-sol
-/
module

public import TauCeti.Analysis.Fredholm.Prod

/-! # Fredholm product indices

This donor packages the finite/free kernel and cokernel instances supplied by Fredholm
hypotheses for the accepted product-index formula.
-/

public section

namespace ContinuousLinearMap

variable {K E₁ E₂ F₁ F₂ : Type*} [NontriviallyNormedField K]
variable [AddCommGroup E₁] [TopologicalSpace E₁] [Module K E₁]
variable [AddCommGroup E₂] [TopologicalSpace E₂] [Module K E₂]

variable [AddCommGroup F₁] [TopologicalSpace F₁] [Module K F₁]
variable [AddCommGroup F₂] [TopologicalSpace F₂] [Module K F₂]
variable {T : E₁ →L[K] F₁} {S : E₂ →L[K] F₂}

/-- The indices of Fredholm maps add under Cartesian products. -/
lemma IsFredholm.index_prodMap (hT : IsFredholm T) (hS : IsFredholm S) :
    (T.prodMap S).index = T.index + S.index := by
  let := hT.finite_ker
  let := hS.finite_ker
  let := hT.finite_coker
  let := hS.finite_coker
  let := Module.Free.of_divisionRing K T.ker
  let := Module.Free.of_divisionRing K S.ker
  let := Module.Free.of_divisionRing K (F₁ ⧸ T.range)
  let := Module.Free.of_divisionRing K (F₂ ⧸ S.range)
  exact ContinuousLinearMap.index_prodMap T S

end ContinuousLinearMap

/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import TauCeti.Analysis.Normed.Lp.ProdLp
public import Mathlib.Analysis.Normed.Operator.Prod
public import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Continuity of orthogonal block curves

Operator-norm continuous families remain continuous under the accepted
`ContinuousLinearMap.withLpProdMap` construction.
-/

public section

open scoped ENNReal

variable {𝕜 X E₁ E₂ F₁ F₂ : Type*} [NontriviallyNormedField 𝕜]
  [TopologicalSpace X]
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]

/-- Operator-norm continuity of the `Lᵖ` block sum of two continuous families. -/
theorem Continuous.withLpProdMap {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {f : X → E₁ →L[𝕜] F₁} {g : X → E₂ →L[𝕜] F₂}
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => (f x).withLpProdMap p (g x)) := by
  let e := WithLp.prodContinuousLinearEquiv p 𝕜 E₁ E₂
  let e' := WithLp.prodContinuousLinearEquiv p 𝕜 F₁ F₂
  have hblock (x : X) : (f x).withLpProdMap p (g x) =
      e'.symm.toContinuousLinearMap ∘L (f x).prodMap (g x) ∘L e.toContinuousLinearMap := by
    ext v
    simp [ContinuousLinearMap.withLpProdMap_apply, e, e']
    rfl
  simp_rw [hblock]
  exact ((hf.prod_mapL 𝕜 hg).clm_comp_const e.toContinuousLinearMap).const_clm_comp
    e'.symm.toContinuousLinearMap

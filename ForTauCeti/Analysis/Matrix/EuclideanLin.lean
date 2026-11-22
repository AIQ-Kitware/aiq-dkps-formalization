/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI gpt-6.1-sol
-/
module

public import TauCeti.Analysis.Matrix.EuclideanLin

/-! # Coordinate entries of the inverse matrix/operator correspondence -/

public noncomputable section

namespace Matrix

variable {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]

/-- The matrix of a continuous linear map has entries given by its action on coordinate units. -/
theorem toEuclideanCLM_symm_apply_single
    (T : EuclideanSpace 𝕜 ι →L[𝕜] EuclideanSpace 𝕜 ι) (i j : ι) :
    (toEuclideanCLM (𝕜 := 𝕜)).symm T i j = T (EuclideanSpace.single j 1) i := by
  have h := congrArg (fun S : EuclideanSpace 𝕜 ι →L[𝕜] EuclideanSpace 𝕜 ι =>
    S (EuclideanSpace.single j 1) i) ((toEuclideanCLM (𝕜 := 𝕜)).apply_symm_apply T)
  have hm := (Matrix.toEuclideanCLM_apply_apply
    ((toEuclideanCLM (𝕜 := 𝕜)).symm T) (EuclideanSpace.single j 1) i)
  simp only [PiLp.single_apply, EuclideanSpace.single, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hm
  exact hm.symm.trans h

end Matrix

/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI gpt-6.1-sol
-/
module

public import TauCeti.Analysis.Matrix.EuclideanLin

/-! # Coordinate units for the matrix/operator correspondence -/

public noncomputable section

namespace Matrix

variable {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]

/-- A matrix operator sends a coordinate unit vector to the corresponding column. -/
theorem toEuclideanCLM_apply_single (A : Matrix ι ι 𝕜) (j : ι) :
    toEuclideanCLM (𝕜 := 𝕜) A (EuclideanSpace.single j 1) =
      WithLp.toLp 2 (fun i => A i j) := by
  rw [toEuclideanCLM_apply, toLpLin_apply, PiLp.ofLp_single,
    Matrix.mulVec_single_one]
  rfl

/-- The matrix of a continuous linear map has entries given by its action on coordinate units. -/
@[simp] theorem toEuclideanCLM_symm_apply_single
    (T : EuclideanSpace 𝕜 ι →L[𝕜] EuclideanSpace 𝕜 ι) (i j : ι) :
    (toEuclideanCLM (𝕜 := 𝕜)).symm T i j = T (EuclideanSpace.single j 1) i := by
  rw [ContinuousLinearMap.toEuclideanCLM_symm_eq_toMatrix, LinearMap.toMatrix_apply]
  simp

end Matrix

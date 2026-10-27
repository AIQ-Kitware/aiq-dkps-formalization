/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import TauCeti.Analysis.InnerProductSpace.Projection.Block
public import Mathlib.Analysis.Normed.Operator.NormedSpace

/-! # Contractivity of the canonical diagonal-block projection -/

public section

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Orthogonal pinching is contractive in operator norm, including
infinite-dimensional and zero-dimensional spaces. -/
theorem norm_diagBlock_le (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]
    (A : E →L[𝕜] E) : ‖K.diagBlock A‖ ≤ ‖A‖ := by
  have h := K.two_smul_diagBlock A
  rw [← ofNat_smul_eq_nsmul 𝕜] at h
  have hn := norm_add_le A ((K.reflection : E →L[𝕜] E) ∘L A ∘L (K.reflection : E →L[𝕜] E))
  rw [← h, norm_smul, RCLike.norm_two,
    ContinuousLinearMap.opNorm_linearIsometryEquiv_comp,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv] at hn
  linarith

/-- The diagonal part cannot amplify errors in the input operator. -/
theorem norm_diagBlock_sub_le (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]
    (A B : E →L[𝕜] E) : ‖K.diagBlock A - K.diagBlock B‖ ≤ ‖A - B‖ := by
  rw [← K.diagBlock_sub]
  exact K.norm_diagBlock_le _

end Submodule

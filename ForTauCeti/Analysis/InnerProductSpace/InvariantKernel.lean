/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import Mathlib.Analysis.InnerProductSpace.Symmetric

/-!
# Kernel invariance from commutation with a symmetric square

The kernel of a symmetric operator equals the kernel of its square.
Consequently any linear map commuting with that square preserves the kernel.
No completeness or dimension assumption is required.
-/

public section

namespace LinearMap.IsSymmetric

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Commutation with the square of a symmetric operator preserves its
kernel, even if the two operators themselves do not commute. -/
theorem mapsTo_ker_of_commute_square {G P : Module.End 𝕜 E} (hG : G.IsSymmetric)
    (hP : Commute P (G * G)) : Set.MapsTo P G.ker G.ker := by
  intro x hx
  change G x = 0 at hx
  change G (P x) = 0
  have h := congrArg (fun T : Module.End 𝕜 E => T x) hP.eq
  change P (G (G x)) = G (G (P x)) at h
  rw [hx, map_zero, map_zero] at h
  have hi := hG (P x) (G (P x))
  rw [← h, inner_zero_right] at hi
  exact inner_self_eq_zero.mp hi

end LinearMap.IsSymmetric

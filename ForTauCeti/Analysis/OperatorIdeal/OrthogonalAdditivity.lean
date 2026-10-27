/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.OperatorIdeal.ReducingTrace

/-!
# Exact Schatten additivity on orthogonal self-adjoint supports

Self-adjoint operators with zero product occupy complementary reducing
sectors. Their native Schatten powers add exactly, including infinite
values, without compactness or a finite-dimensional ambient hypothesis.
-/

public section

noncomputable section

namespace ContinuousLinearMap

open scoped ENNReal InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- Exact additivity of native Schatten powers on orthogonal
self-adjoint supports. Neither compactness nor ideal membership is needed. -/
theorem gauge_schatten_rpow_add_of_selfAdjoint_mul_eq_zero
    (p : ℝ) (hp : 1 ≤ p) (A B : E →L[𝕜] E)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (hAB : A * B = 0) :
    (TauCeti.OperatorIdealFamily.schatten 𝕜 p hp).gauge (A + B) ^ p =
      (TauCeti.OperatorIdealFamily.schatten 𝕜 p hp).gauge A ^ p +
        (TauCeti.OperatorIdealFamily.schatten 𝕜 p hp).gauge B ^ p := by
  let M := A.ker
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hAred : M.IsReducing A.toLinearMap := by
    apply (hA.isSymmetric.isReducing_iff_mem_invtSubmodule M).mpr
    intro x hx
    change A (A x) = 0
    rw [show A x = 0 from hx, map_zero]
  have hBker (x : E) : B x ∈ M := by
    change A (B x) = 0
    exact congrArg (fun T : E →L[𝕜] E => T x) hAB
  have hBred : M.IsReducing B.toLinearMap :=
    (hB.isSymmetric.isReducing_iff_mem_invtSubmodule M).mpr (fun x _ => hBker x)
  have hBzero (x : E) (hx : x ∈ Mᗮ) : B x = 0 := by
    exact inner_self_eq_zero.mp ((Submodule.mem_orthogonal M (B x)).mp
      (hBred.orthogonal_mem_invtSubmodule hx) (B x) (hBker x))
  have hsum : M.IsReducing (A + B).toLinearMap := by
    apply (M.isReducing_iff _).mpr
    exact ⟨fun x hx => M.add_mem (hAred.mem_invtSubmodule hx) (hBred.mem_invtSubmodule hx),
      fun x hx => Mᗮ.add_mem (hAred.orthogonal_mem_invtSubmodule hx)
        (hBred.orthogonal_mem_invtSubmodule hx)⟩
  have hA0 : M.orthogonalProjectionOnto ∘L A ∘L M.subtypeL = 0 := by
    apply ContinuousLinearMap.ext
    intro x
    change M.orthogonalProjectionOnto (A (x : E)) = 0
    rw [show A (x : E) = 0 from x.property, map_zero]
  have hB0 : Mᗮ.orthogonalProjectionOnto ∘L B ∘L Mᗮ.subtypeL = 0 := by
    apply ContinuousLinearMap.ext
    intro x
    change Mᗮ.orthogonalProjectionOnto (B (x : E)) = 0
    rw [hBzero x x.property, map_zero]
  have hhead : M.orthogonalProjectionOnto ∘L (A + B) ∘L M.subtypeL =
      M.orthogonalProjectionOnto ∘L B ∘L M.subtypeL := by
    apply ContinuousLinearMap.ext
    intro x
    change M.orthogonalProjectionOnto (A (x : E) + B x) = M.orthogonalProjectionOnto (B x)
    rw [show A (x : E) = 0 from x.property, zero_add]
  have htail : Mᗮ.orthogonalProjectionOnto ∘L (A + B) ∘L Mᗮ.subtypeL =
      Mᗮ.orthogonalProjectionOnto ∘L A ∘L Mᗮ.subtypeL := by
    apply ContinuousLinearMap.ext
    intro x
    change Mᗮ.orthogonalProjectionOnto (A (x : E) + B x) = Mᗮ.orthogonalProjectionOnto (A x)
    rw [hBzero x x.property, add_zero]
  have hAsplit := gauge_schatten_rpow_eq_add_of_isReducing p hp A M hAred
  have hBsplit := gauge_schatten_rpow_eq_add_of_isReducing p hp B M hBred
  have hSsplit := gauge_schatten_rpow_eq_add_of_isReducing p hp (A + B) M hsum
  rw [hA0, TauCeti.OperatorIdealFamily.gauge_zero, ENNReal.zero_rpow_of_pos hp0,
    zero_add] at hAsplit
  rw [hB0, TauCeti.OperatorIdealFamily.gauge_zero, ENNReal.zero_rpow_of_pos hp0,
    add_zero] at hBsplit
  rw [hhead, htail, ← hAsplit, ← hBsplit] at hSsplit
  exact hSsplit.trans (add_comm _ _)

end ContinuousLinearMap

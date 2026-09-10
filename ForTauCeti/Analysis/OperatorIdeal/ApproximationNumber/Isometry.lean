/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall
-/
module

public import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.Basic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-! # Approximation numbers under isometric changes of coordinates -/

public section

namespace ContinuousLinearMap

variable {𝕜 E F E' F' : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F']

/-- Isometric changes of domain and codomain preserve every approximation number,
including when the spaces live in different universes. -/
theorem approximationNumber_comp_linearIsometryEquiv
    (e : E' ≃ₗᵢ[𝕜] E) (f : F ≃ₗᵢ[𝕜] F') (T : E →L[𝕜] F) (n : ℕ) :
    (f.toContinuousLinearMap ∘L T ∘L e.toContinuousLinearMap).approximationNumber n =
      T.approximationNumber n := by
  have hnorm {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
      [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] (g : X ≃ₗᵢ[𝕜] Y) :
      ‖g.toContinuousLinearMap‖ ≤ 1 := by
    refine opNorm_le_bound _ zero_le_one fun x => ?_
    simpa only [one_mul] using (g.norm_map x).le
  have bound {X Y X' Y' : Type*}
      [NormedAddCommGroup X] [NormedSpace 𝕜 X]
      [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
      [NormedAddCommGroup X'] [NormedSpace 𝕜 X']
      [NormedAddCommGroup Y'] [NormedSpace 𝕜 Y']
      (a : X' ≃ₗᵢ[𝕜] X) (b : Y ≃ₗᵢ[𝕜] Y') (S : X →L[𝕜] Y) :
      (b.toContinuousLinearMap ∘L S ∘L a.toContinuousLinearMap).approximationNumber n
        ≤ S.approximationNumber n := by
    calc
      _ ≤ ‖b.toContinuousLinearMap‖ * S.approximationNumber n *
          ‖a.toContinuousLinearMap‖ :=
        approximationNumber_comp_comp_le _ _ _ n
      _ ≤ 1 * S.approximationNumber n * 1 := by
        gcongr
        · exact hnorm b
        · exact hnorm a
      _ = _ := by simp
  refine le_antisymm (bound e f T) ?_
  have h := bound e.symm f.symm
    (f.toContinuousLinearMap ∘L T ∘L e.toContinuousLinearMap)
  have heq : f.symm.toContinuousLinearMap ∘L
      (f.toContinuousLinearMap ∘L T ∘L e.toContinuousLinearMap) ∘L
        e.symm.toContinuousLinearMap = T := by
    ext x
    simp
  rwa [heq] at h

end ContinuousLinearMap

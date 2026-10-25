/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.CStarAlgebra.Unitary.Maps
public import Mathlib.Topology.Order.LocalExtr

/-!
# Transfer of local-to-global optimality to unitary corrections

Right multiplication by the input unitary identifies a transport fiber
with its source-preserving correction fiber. A real cost that respects
this identification inherits local-to-global optimality. This is a
topological group argument and uses no dimension or penalty assumption.
-/

public section

noncomputable section

namespace TauCeti

open scoped Topology

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- A source-preserving correction cost inherits local-to-global
optimality from the corresponding transport cost. The supplied cost
identity is required on all operators. Source and target need not be
projections, and the ambient Hilbert space need not be finite-dimensional. -/
theorem isMinOn_unitary_correction_of_transport_local_global
    (P Q : E →L[𝕜] E) (A V : unitary (E →L[𝕜] E))
    (hA : (A : E →L[𝕜] E) * P * star (A : E →L[𝕜] E) = Q)
    (hV : (V : E →L[𝕜] E) * P * star (V : E →L[𝕜] E) = P)
    (cost correctionCost : (E →L[𝕜] E) → ℝ)
    (hcost : ∀ W, correctionCost (W * (A : E →L[𝕜] E)) = cost W)
    (hlocalglobal : ∀ T : unitary (E →L[𝕜] E),
      (T : E →L[𝕜] E) * Q * star (T : E →L[𝕜] E) = P →
      IsLocalMinOn cost {W | W ∈ unitary (E →L[𝕜] E) ∧ W * Q * star W = P}
        (T : E →L[𝕜] E) →
      IsMinOn cost {W | W ∈ unitary (E →L[𝕜] E) ∧ W * Q * star W = P}
        (T : E →L[𝕜] E))
    (hmin : IsLocalMinOn correctionCost
      {W | W ∈ unitary (E →L[𝕜] E) ∧ W * P * star W = P} (V : E →L[𝕜] E)) :
    IsMinOn correctionCost {W | W ∈ unitary (E →L[𝕜] E) ∧ W * P * star W = P}
      (V : E →L[𝕜] E) := by
  let T := V * star A
  let f := fun W : E →L[𝕜] E => W * (A : E →L[𝕜] E)
  have hfT : f (T : E →L[𝕜] E) = (V : E →L[𝕜] E) := by
    change ((V : E →L[𝕜] E) * star (A : E →L[𝕜] E)) * (A : E →L[𝕜] E) = _
    rw [mul_assoc, Unitary.coe_star_mul_self, mul_one]
  have hconj (W : E →L[𝕜] E) :
      f W * P * star (f W) = W * Q * star W := by
    dsimp only [f]
    rw [star_mul, ← hA]
    simp only [mul_assoc]
  have hTtrans : (T : E →L[𝕜] E) * Q * star (T : E →L[𝕜] E) = P := by
    rw [← hconj, hfT]
    exact hV
  have hfeasible (W : E →L[𝕜] E)
      (hW : W ∈ unitary (E →L[𝕜] E) ∧ W * Q * star W = P) :
      f W ∈ unitary (E →L[𝕜] E) ∧ f W * P * star (f W) = P :=
    ⟨mul_mem hW.1 A.property, (hconj W).trans hW.2⟩
  have hmin' : IsLocalMinOn correctionCost
      {W | W ∈ unitary (E →L[𝕜] E) ∧ W * P * star W = P}
      (f (T : E →L[𝕜] E)) := by rw [hfT]; exact hmin
  have hlocal := hmin'.comp_continuousOn (g := f)
    (s := {W | W ∈ unitary (E →L[𝕜] E) ∧ W * Q * star W = P})
    (fun W hW => hfeasible W hW) (continuous_id.mul_const (A : E →L[𝕜] E)).continuousOn
    ⟨T.property, hTtrans⟩
  have hlocalT : IsLocalMinOn cost
      {W | W ∈ unitary (E →L[𝕜] E) ∧ W * Q * star W = P} (T : E →L[𝕜] E) := by
    change ∀ᶠ W in 𝓝[{W | W ∈ unitary (E →L[𝕜] E) ∧ W * Q * star W = P}]
      (T : E →L[𝕜] E), _ ≤ _ at hlocal ⊢
    filter_upwards [hlocal] with W hW
    simpa only [Function.comp_apply, f, hcost] using hW
  have hglobal := hlocalglobal T hTtrans hlocalT
  intro S hS
  let B := S * star (A : E →L[𝕜] E)
  have hBunit : B ∈ unitary (E →L[𝕜] E) := mul_mem hS.1 (Unitary.star_mem A.property)
  have hfB : f B = S := by
    change (S * star (A : E →L[𝕜] E)) * (A : E →L[𝕜] E) = S
    rw [mul_assoc, Unitary.coe_star_mul_self, mul_one]
  have hBtrans : B * Q * star B = P := by
    rw [← hconj, hfB]
    exact hS.2
  have hg := hglobal ⟨hBunit, hBtrans⟩
  change cost (T : E →L[𝕜] E) ≤ cost B at hg
  rw [← hcost (T : E →L[𝕜] E), ← hcost B] at hg
  change correctionCost (f (T : E →L[𝕜] E)) ≤ correctionCost (f B) at hg
  rw [hfT, hfB] at hg
  exact hg

end TauCeti

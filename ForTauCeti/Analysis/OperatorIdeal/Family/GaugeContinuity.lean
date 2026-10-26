/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import TauCeti.Analysis.OperatorIdeal.Family
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Continuity of extended ideal costs under ideal convergence

An operator-ideal gauge converges whenever the gauge of the difference
tends to zero. This follows from the two triangle inequalities and
extended subtraction; infinite limit costs are included.
-/

public section

namespace TauCeti.OperatorIdealFamily

open Filter
open scoped ENNReal Topology

universe u v w

variable {𝕜 : Type u} [RCLike 𝕜] {E : Type v} {F : Type w}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Convergence in an ideal gauge implies convergence of that gauge's
extended values, without a finite-cost assumption on the limit. -/
theorem tendsto_gauge_of_tendsto_gauge_sub_zero
    (Φ : OperatorIdealFamily.{u, v, w} 𝕜)
    {α : Type*} {l : Filter α} (A : E →L[𝕜] F) (T : α → E →L[𝕜] F)
    (h : Tendsto (fun n => Φ.gauge (T n - A)) l (𝓝 0)) :
    Tendsto (fun n => Φ.gauge (T n)) l (𝓝 (Φ.gauge A)) := by
  have hupper (n : α) : Φ.gauge (T n) ≤ Φ.gauge A + Φ.gauge (T n - A) := by
    have hle := Φ.gauge_add_le A (T n - A)
    rwa [show A + (T n - A) = T n by abel] at hle
  have hlower (n : α) : Φ.gauge A - Φ.gauge (T n - A) ≤ Φ.gauge (T n) := by
    apply tsub_le_iff_right.mpr
    have hle := Φ.gauge_add_le (T n) (A - T n)
    rw [show T n + (A - T n) = A by abel, ← neg_sub (T n) A, Φ.gauge_neg] at hle
    exact hle
  have hc : Tendsto (fun _ : α => Φ.gauge A) l (𝓝 (Φ.gauge A)) := tendsto_const_nhds
  have hlo := ENNReal.Tendsto.sub hc h (Or.inr ENNReal.zero_ne_top)
  have hhi := hc.add h
  simp only [tsub_zero] at hlo
  simp only [add_zero] at hhi
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi hlower hupper

end TauCeti.OperatorIdealFamily

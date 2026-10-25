/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6, GPT-6.1 Sol
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.SchattenContinuity
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Topology.Algebra.Star.Unitary
public import Mathlib.Topology.Order.Compact

/-!
# Attainment of finite Schatten transport minima

A nonempty unitary transport fiber is compact in finite dimension. The actual
Schatten displacement power therefore attains its minimum. This classical
existence statement supplies a minimizer to the subsequent spectral reduction;
it does not identify the minimum value.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open scoped ENNReal

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [CompleteSpace E]

/-- A finite-dimensional unitary transport fiber is compact, also when
empty. The transported operators need not be projections. -/
theorem isCompact_unitary_transport_fiber (P Q : E →L[𝕜] E) :
    IsCompact {W : E →L[𝕜] E | W ∈ unitary (E →L[𝕜] E) ∧ W * P * star W = Q} := by
  have hnorm (W : E →L[𝕜] E) (hW : W ∈ unitary (E →L[𝕜] E)) : ‖W‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simpa only [one_mul] using
      (_root_.ContinuousLinearMap.norm_map_of_mem_unitary hW x).le
  let : ProperSpace (E →L[𝕜] E) := FiniteDimensional.proper_rclike 𝕜 _
  have hcompact : IsCompact (unitary (E →L[𝕜] E) : Set (E →L[𝕜] E)) := by
    apply (isCompact_closedBall (0 : E →L[𝕜] E) 1).of_isClosed_subset isClosed_unitary
    intro W hW
    simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm W hW
  have hclosed : IsClosed {W : E →L[𝕜] E | W * P * star W = Q} :=
    isClosed_eq ((continuous_id.mul continuous_const).mul continuous_star) continuous_const
  exact hcompact.inter_right hclosed

/-- Every nonempty finite-dimensional unitary transport fiber has an
attaining minimizer for the actual finite Schatten displacement power.
The two transported operators need not be projections for attainment. -/
theorem exists_schatten_transport_minimizer
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (P Q : E →L[𝕜] E) (U₀ : unitary (E →L[𝕜] E))
    (h₀ : (U₀ : E →L[𝕜] E) * P * star (U₀ : E →L[𝕜] E) = Q) :
    ∃ U : unitary (E →L[𝕜] E),
      (U : E →L[𝕜] E) * P * star (U : E →L[𝕜] E) = Q ∧
      IsMinOn
        (fun W : E →L[𝕜] E => UnitarilyInvariantSeminorm.schatten 𝕜 E E p
          (LinearMap.id - W.toLinearMap) ^ p.toReal)
        {W | W ∈ unitary (E →L[𝕜] E) ∧ W * P * star W = Q}
        (U : E →L[𝕜] E) := by
  have hcompact := isCompact_unitary_transport_fiber P Q
  have hf : Continuous (fun W : E →L[𝕜] E => UnitarilyInvariantSeminorm.schatten 𝕜 E E p
      (LinearMap.id - W.toLinearMap) ^ p.toReal) := by
    have hdisp (W : E →L[𝕜] E) : (1 - W).toLinearMap = LinearMap.id - W.toLinearMap := by
      rfl
    have hf' : Continuous (fun W : E →L[𝕜] E => UnitarilyInvariantSeminorm.schatten 𝕜 E E p
        (1 - W).toLinearMap ^ p.toReal) :=
      (continuous_schatten_rpow_toLinearMap p hp).comp
        ((continuous_const (y := (1 : E →L[𝕜] E))).sub continuous_id)
    simpa only [hdisp] using hf'
  obtain ⟨W, hW, hmin⟩ := hcompact.exists_isMinOn
    ⟨(U₀ : E →L[𝕜] E), U₀.2, h₀⟩ hf.continuousOn
  exact ⟨⟨W, hW.1⟩, hW.2, hmin⟩

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

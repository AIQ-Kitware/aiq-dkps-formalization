/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import TauCeti.Analysis.OperatorIdeal.Family.Schatten
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Exact spectral cost identities from dominated norm approximations

Finite-section cost identities pass to bounded operators when both
extended costs are bounded by their proposed limits. Continuity of each
fixed singular-value penalty and lower semicontinuity of the native
Schatten gauge give the two inequalities. Infinite costs are included;
no summability or compactness is required by this limit step.
-/

public section

namespace TauCeti.OperatorIdealFamily

open Filter
open scoped ENNReal NNReal Topology

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Norm limits preserve an exact Schatten-power / continuous spectral
penalty identity if the approximants' two costs are bounded by the
corresponding limit costs. Divergent extended sums are allowed. -/
theorem gauge_schatten_rpow_eq_tsum_of_dominated_approximation
    (p : ℝ) (hp : 1 ≤ p) (f : ℝ≥0 → ℝ≥0∞) (hf : Continuous f)
    (A B : E →L[𝕜] F) (Aₙ Bₙ : ℕ → E →L[𝕜] F)
    (hA : Tendsto Aₙ atTop (𝓝 A)) (hB : Tendsto Bₙ atTop (𝓝 B))
    (heq : ∀ n, (schatten 𝕜 p hp).gauge (Aₙ n) ^ p =
      ∑' j, f ((Bₙ n).singularValue j))
    (hdomA : ∀ n, (schatten 𝕜 p hp).gauge (Aₙ n) ^ p ≤
      (schatten 𝕜 p hp).gauge A ^ p)
    (hdomB : ∀ n, (∑' j, f ((Bₙ n).singularValue j)) ≤
      ∑' j, f (B.singularValue j)) :
    (schatten 𝕜 p hp).gauge A ^ p = ∑' j, f (B.singularValue j) := by
  apply le_antisymm
  · have hlsc : LowerSemicontinuous (fun T : E →L[𝕜] F =>
        (schatten 𝕜 p hp).gauge T ^ p) :=
      ENNReal.continuous_rpow_const.comp_lowerSemicontinuous
        (lowerSemicontinuous_gauge_schatten p hp)
        (fun _ _ h => ENNReal.rpow_le_rpow h (by linarith))
    exact (hlsc.isClosed_preimage (∑' j, f (B.singularValue j))).mem_of_tendsto hA
      (Eventually.of_forall (fun n => (heq n).trans_le (hdomB n)))
  · rw [ENNReal.tsum_eq_iSup_sum]
    apply iSup_le
    intro s
    have hterm (j : ℕ) :=
      ((hf.comp (ContinuousLinearMap.continuous_singularValue j)).tendsto B).comp hB
    apply le_of_tendsto' (tendsto_finsetSum s (fun j _ => hterm j))
    intro n
    calc
      _ ≤ ∑' j, f ((Bₙ n).singularValue j) := ENNReal.sum_le_tsum s
      _ = (schatten 𝕜 p hp).gauge (Aₙ n) ^ p := (heq n).symm
      _ ≤ _ := hdomA n

end TauCeti.OperatorIdealFamily

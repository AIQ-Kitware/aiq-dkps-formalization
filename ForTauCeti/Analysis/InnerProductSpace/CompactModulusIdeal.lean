/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.CompactModulusFiber
public import ForTauCeti.Analysis.OperatorIdeal.Family.SchattenConvergence
public import TauCeti.Analysis.OperatorIdeal.Family.Carrier

/-!
# Fixed-modulus fibers are compact in Schatten norm

For a positive Schatten operator S, the full self-adjoint modulus fiber
is compact in the native Schatten carrier. Its operator-norm and
Schatten-norm topologies agree. The proof uses interlacing and dominated
convergence and requires neither separability nor finite rank.

## Provenance

New local proof code for the DKPS optimizer classification, using the
accepted Tau Ceti carrier and singular-value APIs. No historical priority
or accepted roadmap ownership is asserted.
-/

public section

noncomputable section

namespace TauCeti

open Filter
open scoped Topology ENNReal

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- On a fixed-modulus fiber, operator convergence upgrades to convergence
in every finite Schatten norm in which the modulus lies. -/
theorem tendsto_schatten_sub_zero_of_modulus_eq
    (p : ℝ) (hp : 1 ≤ p) (S A : E →L[𝕜] E)
    (hS : (OperatorIdealFamily.schatten 𝕜 p hp).gauge S ≠ ∞)
    {α : Type*} {l : Filter α} (T : α → E →L[𝕜] E)
    (hT : Tendsto T l (𝓝 A)) (hmod : ∀ n, (T n).modulus = S) (hA : A.modulus = S) :
    Tendsto (fun n => (OperatorIdealFamily.schatten 𝕜 p hp).gauge (T n - A)) l (𝓝 0) := by
  apply OperatorIdealFamily.tendsto_gauge_schatten_sub_zero_of_singularValue_le
    p hp S A hS T hT
  · intro n k
    exact le_of_eq ((ContinuousLinearMap.singularValue_modulus (T n) k).symm.trans
      (congrArg (fun B : E →L[𝕜] E => B.singularValue k) (hmod n)))
  · intro k
    exact le_of_eq ((ContinuousLinearMap.singularValue_modulus A k).symm.trans
      (congrArg (fun B : E →L[𝕜] E => B.singularValue k) hA))

/-- The fixed-modulus fiber is compact in the accepted Schatten carrier,
with its ideal norm, rather than the inherited operator norm. -/
theorem isCompact_setOf_isSelfAdjoint_modulus_eq_schatten
    (p : ℝ) (hp : 1 ≤ p) (S : E →L[𝕜] E) (hSpos : S.IsPositive)
    (hS : (OperatorIdealFamily.schatten 𝕜 p hp).gauge S ≠ ∞) :
    IsCompact {A : ((OperatorIdealFamily.schatten 𝕜 p hp).operatorGauge E E).Carrier |
      IsSelfAdjoint A.toContinuousLinearMap ∧ A.toContinuousLinearMap.modulus = S} := by
  let Φ := OperatorIdealFamily.schatten 𝕜 p hp
  let X := {A : E →L[𝕜] E // IsSelfAdjoint A ∧ A.modulus = S}
  have hfinite (A : X) : Φ.gauge A.val ≠ ∞ := by
    have heq : Φ.gauge A.val = Φ.gauge S := by
      rw [OperatorIdealFamily.gauge_schatten, OperatorIdealFamily.gauge_schatten]
      congr 1
      apply tsum_congr
      intro k
      rw [← ContinuousLinearMap.singularValue_modulus A.val k, A.property.2]
    rwa [heq]
  let f : X → (Φ.operatorGauge E E).Carrier := fun A =>
    ⟨A.val, by simpa only [OperatorGauge.mem_finiteSubmodule,
      OperatorIdealFamily.operatorGauge_apply] using lt_top_iff_ne_top.mpr (hfinite A)⟩
  have hf : Continuous f := by
    apply continuous_iff_continuousAt.mpr
    intro A
    apply tendsto_iff_enorm_sub_tendsto_zero.mpr
    have ht := tendsto_schatten_sub_zero_of_modulus_eq p hp S A.val hS
      (fun B : X => B.val) continuous_subtype_val.continuousAt
      (fun B => B.property.2) A.property.2
    simpa only [OperatorGauge.Carrier.enorm_eq_gauge,
      OperatorGauge.Carrier.toContinuousLinearMap_sub, OperatorIdealFamily.operatorGauge_apply,
      f, enorm_neg, neg_sub] using ht
  have hc := isCompact_setOf_isSelfAdjoint_modulus_eq S hSpos
    (OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top p hp S hS)
  let : CompactSpace X := isCompact_iff_compactSpace.mp hc
  have hrange : Set.range f = {A : (Φ.operatorGauge E E).Carrier |
      IsSelfAdjoint A.toContinuousLinearMap ∧ A.toContinuousLinearMap.modulus = S} := by
    ext A
    constructor
    · rintro ⟨B, rfl⟩
      exact B.property
    · intro hA
      exact ⟨⟨A.toContinuousLinearMap, hA⟩, OperatorGauge.Carrier.ext rfl⟩
  rw [← hrange]
  exact isCompact_range hf

end TauCeti
